
/*--------------------------------------------------------------------*/
/*--- Nulgrind: The minimal Valgrind tool.               da_main.c ---*/
/*--------------------------------------------------------------------*/

/*
   This file is part of Nulgrind, the minimal Valgrind tool,
   which does no instrumentation or analysis.

   Copyright (C) 2002-2017 Nicholas Nethercote
      njn@valgrind.org

   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation; either version 2 of the
   License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program; if not, see <http://www.gnu.org/licenses/>.

   The GNU General Public License is contained in the file COPYING.
*/

#include "pub_tool_basics.h"
#include "pub_tool_debuginfo.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcfile.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_libcproc.h"
#include "pub_tool_mallocfree.h"
#include "pub_tool_options.h"
#include "pub_tool_oset.h"
#include "pub_tool_tooliface.h"
#include "pub_tool_xarray.h"
#include "pub_tool_clientstate.h"
#include "pub_tool_machine.h"     
#include "pub_tool_mallocfree.h"
#include "pub_tool_hashtable.h"
#include "pub_tool_xarray.h"


#define FILENAME_LEN 100
#define LINENUM_LEN 100

#define CODE_RANGE 0x04000000
#define VAR_RANGE 0xFF000000
// Let's assume 1MB process space

#define MT_MAXLEN 10
#define MT_REC_MAXLEN 202
struct Memtable_entry{
   UInt top;
   Addr keys[MT_MAXLEN];
   HChar values[MT_MAXLEN][MT_REC_MAXLEN];
};
typedef struct Memtable_entry Memtable_entry;

#define MT_PRIME_SIZE 65537
static Memtable_entry table[MT_PRIME_SIZE];
static Bool trace = False;
static Bool tableOverflowed = False;

#define SEEN_PRIME_SIZE 65537
static Addr seen[SEEN_PRIME_SIZE];
static Bool seen_clash = False;

#define LD_CACHE_MAXLEN 1000
static Addr loadCache[LD_CACHE_MAXLEN];
static UInt lcPtr = 0;
static UInt lcRecentRead = -1;
static Bool lcOverflowed = False;

static const HChar* trace_fnname = NULL;
static VgFile* trace_f;
static Bool da_process_cmd_line_option(const HChar* arg)
{
   if VG_STR_CLO(arg, "--trace-file", trace_fnname) {
      if(!trace_fnname) trace_fnname = "./tmp";
      trace_f = VG_(fopen)(trace_fnname, VKI_O_CREAT|VKI_O_WRONLY|VKI_O_TRUNC, VKI_S_IRUSR|VKI_S_IWUSR|VKI_S_IRGRP|VKI_S_IROTH);
   }
   else{
      trace_fnname = "./tmp";
      trace_f = VG_(fopen)(trace_fnname, VKI_O_CREAT|VKI_O_WRONLY|VKI_O_TRUNC, VKI_S_IRUSR|VKI_S_IWUSR|VKI_S_IRGRP|VKI_S_IROTH);
   }
   VG_(umsg)("%s\n", trace_fnname);
   tl_assert(trace_f);
   tl_assert(trace_fnname);
   tl_assert(trace_fnname[0]);
   return True;
}

static void da_print_usage(void)
{  
   VG_(printf)(
"    --trace-file=<full path to file>  output path of tracefile\n"
   );
}

static void da_print_debug_usage(void)
{  
   VG_(printf)(
"    (none)\n"
   );
}

static void insert_loadCache(Addr addr){
   if(lcRecentRead != -1){
      // VG_(umsg)("\tinsert - if...\n");
      lcRecentRead = -1;
      loadCache[0] = addr;
      lcPtr = 1;
   }
   else{
      // VG_(umsg)("\tinsert - else...\n");
      if(lcPtr < LD_CACHE_MAXLEN){
         loadCache[lcPtr++] = addr;
      }
      else{
         lcOverflowed = True;
      }
   }
}

static void test_loadCache(UInt linenum){
   if(lcRecentRead == -1){
      // VG_(umsg)("\ttest - if...\n");
      lcRecentRead = linenum;
   }
   else if(lcRecentRead != linenum){
      // VG_(umsg)("\ttest - else...\n");
      lcPtr = 0;
   }
}

static HChar* get_shadow_mem(Addr addr){
   Int mt_index = addr % MT_PRIME_SIZE;
   Memtable_entry *lookup = &table[mt_index];
   for(Int i = 0; i < lookup->top; i++){
      if(lookup->keys[i] == addr){
         // VG_(umsg)("\tfound...\n");
         return lookup->values[i];
      }
   }
   // VG_(umsg)("\tnot found...\n");
   return NULL;
}

static void set_shadow_mem(Addr addr, HChar* str, UInt size){
   UInt mt_index = addr % MT_PRIME_SIZE;
   Memtable_entry *lookup = &table[mt_index];
   for(UInt i = 0; i < lookup->top; i++){
      if(lookup->keys[i] == addr){
         // VG_(umsg)("\tupdates...\n");
         UInt copy_len = size < MT_REC_MAXLEN - 1 ? size : MT_REC_MAXLEN - 1;
         VG_(memcpy)(lookup->values[i], str, copy_len);
         lookup->values[i][copy_len + 1] = '\0';
         return;
      }
   }
   if(lookup->top < MT_MAXLEN){
      // VG_(umsg)("\tnew insert...\n");
      lookup->keys[lookup->top] = addr;
      UInt copy_len = size < MT_REC_MAXLEN - 1 ? size : MT_REC_MAXLEN - 1;
      VG_(memcpy)(lookup->values[lookup->top], str, copy_len);
      lookup->values[lookup->top][copy_len + 1] = '\0';
      ++lookup->top;
   }
   else{
      tableOverflowed = True;
   }
   return;
}

static HChar* get_varname(Addr addr)
{
   if(addr > VAR_RANGE) 
      return NULL;
   DiEpoch    ep = VG_(current_DiEpoch)();
   // AddrInfo ai;
   // VG_(describe_addr) (ep, addr, &ai);
   // VG_(pp_addrinfo) (addr, &ai);
   // return NULL;
   XArray *x1, *x2;
   x1 = VG_(newXA)( VG_(malloc), "mc.da.descr1", VG_(free), sizeof(HChar) );
   x2 = VG_(newXA)( VG_(malloc), "mc.da.descr2", VG_(free), sizeof(HChar) );
   if(VG_(get_data_description)(x1, x2, ep, addr) == False)
   {
      return NULL;
   }
   if(x1 == NULL)
      return NULL;
   HChar* str = (HChar*)VG_(indexXA)(x1, 0);
   int len = VG_(strlen)(str);
   int start = 0;
   for(int i = 0; i < len; i++)
   {
      if(str[i] == '"')
      {
         start = i;
         break;
      }
   }
   //global array int a[5]
   if(start == 0)
   {
      for(int i = 0; i < len; i++)
      {
         if(str[i] == ',')
         {
            start = i;
            break;
         }
      }
      if(start == len)
         return NULL;
      int end = 0;
      for(int i = start; i >= 0; i--)
      {
         if(str[i] == ' ')
         {
            end = i;
            break;
         }
      }
      HChar* vname = VG_(malloc)("varname", sizeof(HChar) * (start - end));
      VG_(memcpy)(vname, str + end + 1, start - end - 1);
      vname[start - end - 1] = 0;
      return vname;
   }
   //global var, int a
   else
   {
      HChar* vname = VG_(strdup)("varname", str + start + 1);
      for(int i = 0; i < len; i++)
      {
         if(vname[i] == '"')
         {
            vname[i] = 0;
            break;
         }
      }
      return vname;
   }
}

VG_REGPARM(2) static void st_callback(Addr var_addr, Addr inst_addr){
   DiEpoch    ep;
   static Addr addr;
   static Addr pc;
   static const HChar* filename;
   static UInt linenum;
   static HChar record[MT_REC_MAXLEN];
   addr = var_addr;
   pc = inst_addr;
   ep = VG_(current_DiEpoch)();
   HChar* varname = get_varname(addr);
   // if(varname == NULL){
   //    return;
   // } 
   UInt record_size = 0;
   if(VG_(get_filename_linenum)(ep, pc, &filename, NULL, &linenum)){
      record_size = VG_(snprintf)(record, MT_REC_MAXLEN - 1, 
                     "%s 0x%lx %s:%u", varname, addr, filename, linenum);
   }
   else{
      record_size = VG_(snprintf)(record, MT_REC_MAXLEN - 1, 
                     "%s 0x%lx (null)", varname, addr);
   }
   VG_(free)(varname);
   if(record_size >= MT_REC_MAXLEN - 1)
      record_size = MT_REC_MAXLEN - 1;
   set_shadow_mem(addr, record, record_size);

   test_loadCache(linenum);
   UInt offset = record_size;
   UInt leftspace = MT_REC_MAXLEN - 1 - record_size;
   VG_(memset)(seen, 0, sizeof(Addr) * SEEN_PRIME_SIZE);
   for(UInt i = 0; i < lcPtr; i++){
      Addr hit = seen[loadCache[i] % SEEN_PRIME_SIZE];
      if(hit != 0){
         if(hit != loadCache[i])
            seen_clash = True;
         continue;
      }
      hit = seen[loadCache[i] %SEEN_PRIME_SIZE] = loadCache[i];
      HChar* depVarStr = get_shadow_mem(loadCache[i]);
      VG_(memset)(record + offset, 0, leftspace);
      if(!depVarStr){
         varname = get_varname(hit);
         // if(varname == NULL){
         //    continue;
         // }
#ifdef DA_DEBUG
         VG_(snprintf)(record + offset, leftspace, 
               " <--- %s 0x%lx (null)", varname, hit);
#else
         VG_(snprintf)(record + offset, leftspace, 
               " %s 0x%lx (null)", varname, hit);
#endif
         VG_(free)(varname);
      }
      else{
#ifdef DA_DEBUG
         VG_(snprintf)(record + offset, leftspace, 
               " <--- %s", depVarStr);
#else
         VG_(snprintf)(record + offset, leftspace, 
               " %s", depVarStr);
#endif
      }
      VG_(umsg)("%s\n", record);
      VG_(fprintf)(trace_f, "%s\n", record);
   }
   return;
}

VG_REGPARM(2) static void ld_callback(Addr var_addr){
   static Addr addr;
   addr = var_addr;
   insert_loadCache(addr);
   return;
}

static void da_post_clo_init(void)
{
   VG_(umsg)("Initializing...\n");
   for(Int i = 0; i < MT_PRIME_SIZE; i++){
      table[i].top = 0;
   }
   VG_(umsg)("Finish Initialization\n");
}

static
IRSB* da_instrument ( VgCallbackClosure* closure,
                      IRSB* sbIn,
                      const VexGuestLayout* layout, 
                      const VexGuestExtents* vge,
                      const VexArchInfo* archinfo_host,
                      IRType gWordTy, IRType hWordTy )
{
   static IRExpr ** argv;
   static IRDirty* dirty;
   static const HChar* filename;

   DiEpoch  ep = VG_(current_DiEpoch)();
   IRSB* sbOut;
   Int i = 0;
   Addr curaddr = 0;

   if (gWordTy != hWordTy) {
      /* We don't currently support this case. */
      VG_(tool_panic)("host/guest word size mismatch");
   }

   sbOut = deepCopyIRSBExceptStmts(sbIn);

   while (i < sbIn->stmts_used && sbIn->stmts[i]->tag != Ist_IMark) {
      addStmtToIRSB( sbOut, sbIn->stmts[i] );
      i++;
   }
   
   for (; i < sbIn->stmts_used; i++) {
      IRStmt* st = sbIn->stmts[i];
      if (!st || st->tag == Ist_NoOp) continue;
      // VG_(umsg)("%d,%d\n",i, st->tag);
      switch (st->tag) {
         case Ist_Store:
            if(trace){
               // VG_(umsg)("Store!\n");
               if(curaddr < CODE_RANGE){
                  argv = mkIRExprVec_2(st->Ist.Store.addr, mkIRExpr_HWord(curaddr));
                  dirty = unsafeIRDirty_0_N(2, "st_callback", VG_(fnptr_to_fnentry)( &st_callback ), argv);
                  addStmtToIRSB(sbOut, IRStmt_Dirty(dirty));
               }
            }
            addStmtToIRSB(sbOut, st);
            break;
         case Ist_WrTmp:
            if(trace){
               IRExpr* data = st->Ist.WrTmp.data;
               if (data->tag == Iex_Load) {
                  if(curaddr < CODE_RANGE){
                     argv = mkIRExprVec_1(data->Iex.Load.addr);
                     dirty = unsafeIRDirty_0_N(1, "ld_callback", VG_(fnptr_to_fnentry)( &ld_callback ), argv);
                     addStmtToIRSB(sbOut, IRStmt_Dirty(dirty));
                  }
               }

            }
            addStmtToIRSB(sbOut, st);
            break;
         case Ist_IMark:
            curaddr =  st->Ist.IMark.addr;
            if (VG_(get_fnname_if_entry)(ep, curaddr, &filename)) {
               if(VG_(strcmp)(filename, "main") == 0) {
                  trace = True;
               }
               else if(VG_(strcmp)(filename, "exit") == 0) {
                  trace = False;
               }
            }
            addStmtToIRSB(sbOut, st);
            break;
         default:
            addStmtToIRSB(sbOut, st);
            break;
      }
   }
   return sbOut;
}

static void da_fini(Int exitcode)
{
   if(tableOverflowed){
      VG_(umsg)("Memtable pool overflowed!\n");
   }
   if(lcOverflowed){
      VG_(umsg)("Load cache overflowed!\n");
   }
   if(seen_clash){
      VG_(umsg)("Seen hash map clashed!\n");
   }
   VG_(umsg)("Finished\n");
   VG_(fclose)(trace_f);
}

static void da_pre_clo_init(void)
{
   VG_(details_name)            ("depAnalysis");
   VG_(details_version)         (NULL);
   VG_(details_description)     ("CS510 - LAB01 - Junyang Shao");
   VG_(details_copyright_author)(
      "Copyright (C) 2002-2017, and GNU GPL'd, by Nicholas Nethercote.");
   VG_(details_bug_reports_to)  (VG_BUGS_TO);

   VG_(details_avg_translation_sizeB) ( 275 );

   VG_(basic_tool_funcs)        (da_post_clo_init,
                                 da_instrument,
                                 da_fini);
   VG_(needs_var_info)();

   VG_(needs_command_line_options)(da_process_cmd_line_option,
                                 da_print_usage,
                                 da_print_debug_usage);
}

VG_DETERMINE_INTERFACE_VERSION(da_pre_clo_init)

/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/
