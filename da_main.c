
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
#include "pub_tool_tooliface.h"
#include "pub_tool_libcassert.h"
#include "pub_tool_libcprint.h"
#include "pub_tool_debuginfo.h"
#include "pub_tool_libcbase.h"
#include "pub_tool_options.h"
#include "pub_tool_machine.h"     
#include "pub_tool_addrinfo.h"

#define FILENAME_LEN 100
#define LINENUM_LEN 100

#define CODE_RANGE 0xFFFFFFF
// Let's assume 256MB process space

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

#define LD_CACHE_MAXLEN 100
static Addr loadCache[LD_CACHE_MAXLEN];
static UInt lcPtr = 0;
static UInt lcRecentRead = -1;
static Bool lcOverflowed = False;

static Addr firstPC = 0;

static void insert_loadCache(Addr addr, UInt linenum){
   if(linenum != -1){
      linenum = -1;
      loadCache[0] = addr;
      lcPtr = 1;
   }
   else{
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
      lcRecentRead = linenum;
   }
   else if(lcRecentRead != linenum){
      lcPtr = 0;
   }
}

static HChar* get_shadow_mem(Addr addr){
   Int mt_index = addr % MT_PRIME_SIZE;
   Memtable_entry lookup = table[mt_index];
   for(Int i = 0; i < lookup.top; i++){
      if(lookup.keys[i] == addr){
         return lookup.values[i];
      }
   }
   return NULL;
}

static void set_shadow_mem(Addr addr, HChar* str, UInt size){
   UInt mt_index = addr % MT_PRIME_SIZE;
   Memtable_entry lookup = table[mt_index];
   for(UInt i = 0; i < lookup.top; i++){
      if(lookup.keys[i] == addr){
         UInt copy_len = size < MT_REC_MAXLEN - 1 ? size : MT_REC_MAXLEN - 1;
         VG_(memcpy)(lookup.values[i], str, copy_len);
         lookup.values[i][copy_len + 1] = '\0';
         return;
      }
   }
   if(lookup.top < MT_MAXLEN){
      lookup.keys[lookup.top] = addr;
      UInt copy_len = size < MT_REC_MAXLEN - 1 ? size : MT_REC_MAXLEN - 1;
      VG_(memcpy)(lookup.values[lookup.top], str, copy_len);
      lookup.values[lookup.top][copy_len + 1] = '\0';
      ++lookup.top;
   }
   else{
      tableOverflowed = True;
   }
   return;
}

static HChar* get_varname(Addr addr)
{
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
   static HChar filename[FILENAME_LEN];
   static UInt linenum[LINENUM_LEN];
   static HChar record[MT_REC_MAXLEN];
   addr = var_addr;
   pc = inst_addr;
   ep = VG_(current_DiEpoch)();
   if(VG_(get_filename_linenum)(ep, pc, &filename, NULL, &linenum)){
      HChar* varname = get_varname(addr);
      UInt record_size = VG_(snprintf)(record, MT_REC_MAXLEN - 1, 
                     "%s %x %s:%lu", varname, addr, filename, linenum)
      VG_(free)(varname);
      if(record_size >= MT_REC_MAXLEN - 1)
         record_size = MT_REC_MAXLEN - 1;
      set_shadow_mem(addr, record, record_size);

      test_loadCache(linenum);
      UInt offset = record_size;
      UInt leftspace = MT_REC_MAXLEN - 1 - record_size;
      for(UInt i = 0; i < lcPtr; i++){
         HChar* depVarStr = get_shadow_mem(loadCache[i]);
         if(!depVarStr) continue;
         UInt record_size = VG_(snprintf)(record + offset, leftspace, 
               ", %s", depVarStr);
         if(record_size >= leftspace) break;
         offset += record_size;
         leftspace -= record_size;
      }
      VG_(umsg)("%s\n", record);
   }

   return;
}

VG_REGPARM(2) static void ld_callback(Addr var_addr, Addr inst_addr){
   DiEpoch    ep = VG_(current_DiEpoch)();
   static Addr addr;
   static Addr pc;
   static HChar filename[FILENAME_LEN];
   static UInt linenum[LINENUM_LEN];
   addr = var_addr;
   pc = inst_addr;
   if(VG_(get_filename_linenum)(ep, pc, &filename, NULL, &linenum)){
      insert_loadCache(addr, linenum);
   }
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
                      IRSB* bb,
                      const VexGuestLayout* layout, 
                      const VexGuestExtents* vge,
                      const VexArchInfo* archinfo_host,
                      IRType gWordTy, IRType hWordTy )
{
   IRSB*      sbOut;

   static IRExpr ** argv;
   static IRDirty* dirty;
   static Long diff;
   for (Int i; i < sbIn->stmts_used; i++) {
      IRStmt* st = sbIn->stmts[i];
      if (!st || st->tag == Ist_NoOp) continue;
      switch (st->tag) {
         case Ist_Store:
            if(trace){
               diff = st->Ist.IMark.addr - firstPC;
               if(diff < 0) 
                  diff = -diff;
               if(diff < CODE_RANGE){
                  argv = mkIRExprVec_2(st->Ist.Store.addr, mkIRExpr_HWord(st->Ist.IMark.addr));
                  dirty = unsafeIRDirty_0_N(2, "st_callback", VG_(fnptr_to_fnentry)(st_callback), argv);
                  addStmtToIRSB(sbOut, IRStmt_Dirty(dirty));
               }
            }
            addStmtToIRSB(sbOut, st);
            break;
         case Ist_LoadG:
            if(trace){
               diff = st->Ist.IMark.addr - firstPC;
               if(diff < 0) 
                  diff = -diff;
               if(diff < CODE_RANGE){
                  argv = mkIRExprVec_2(st->Ist.LoadG.details->addr, mkIRExpr_HWord(st->Ist.IMark.addr));
                  dirty = unsafeIRDirty_0_N(2, "ld_callback", VG_(fnptr_to_fnentry)(ld_callback), argv);
                  addStmtToIRSB(sbOut, IRStmt_Dirty(dirty));
               }
            }
            addStmtToIRSB(sbOut, st);
            break;
         case Ist_IMark:
            if (VG_(get_fnname_if_entry)(st->Ist.IMark.addr, filename, sizeof(filename))) {
               if(VG_(strcmp)(filename, "main") == 0) {
                  trace = True;
               }
               else if(VG_(strcmp)(filename, "exit") == 0) {
                  trace = False;
               }
            }
            if(firstPC == 0){
               firstPC = st->Ist.IMark.addr;
            }
            addStmtToIRSB(sbOut, st);
            break;
         default:
            addStmtToIRSB(sbOut, st);
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
}

VG_DETERMINE_INTERFACE_VERSION(da_pre_clo_init)

/*--------------------------------------------------------------------*/
/*--- end                                                          ---*/
/*--------------------------------------------------------------------*/
