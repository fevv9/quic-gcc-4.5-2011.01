
/* HEXAGON specific functions
   Copyright (C) 1998, 1999, 2000, 2001, 2002 Free Software Foundation, Inc.

   This file is part of GCC.

   GCC is free software; you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation; either version 2, or (at your option)
   any later version.

   GCC is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with GCC; see the file COPYING.  If not, write to
   the Free Software Foundation, 59 Temple Place - Suite 330,
   Boston, MA 02111-1307, USA.  */

#include "config.h"

#include <string.h>
#include <assert.h>

#include "system.h"
#include "coretypes.h"
#include "tm.h"
#include "rtl.h"
#include "regs.h"
#include "hard-reg-set.h"
#include "basic-block.h"
#include "real.h"
#include "insn-config.h"
#include "conditions.h"
#include "insn-attr.h"
#include "flags.h"
#include "recog.h"
#include "tree.h"
#include "tree-pass.h"
#include "output.h"
#include "expr.h"
#include "obstack.h"
#include "except.h"
#include "function.h"
#include "toplev.h"
#include "options.h"
#include "tm_p.h"
#include "target.h"
#include "target-def.h"
#include "reload.h"
#include "optabs.h"
#include "ggc.h"
#include "c-pragma.h"
#include "integrate.h"
#include "debug.h"
#include "langhooks.h"
#include "df.h"
#include "sched-int.h"
#include "cfgloop.h"





enum hexagon_architecture hexagon_arch = HEXAGON_ARCH_UNSPECIFIED;
enum hexagon_abi hexagon_abi = HEXAGON_ABI_UNSPECIFIED;
int hexagon_features;
enum hexagon_falign hexagon_falign = HEXAGON_FALIGN_UNSPECIFIED;
bool hexagon_dual_memory_accesses = true;

/* Used for qdsp6 compatibility */
int hexagon_qdsp6_compat = 0;

static GTY(()) struct hexagon_packet_info *hexagon_head_packet;
static GTY(()) struct hexagon_packet_info *hexagon_tail_packet;
static struct hexagon_bb_aux_info *hexagon_head_bb_aux;




static bool hexagon_handle_option(size_t code, const char *arg, int value);

static struct machine_function *hexagon_init_machine_status(void);

static int hexagon_array_alignment(tree type, int align);
static bool hexagon_align_anon_bitfield(void);

static bool hexagon_default_short_enums(void);

static enum reg_class hexagon_secondary_reload(
                        bool in_p,
                        rtx x,
                        enum reg_class reload_class,
                        enum machine_mode reload_mode,
                        secondary_reload_info *sri);

static bool hexagon_save_register_p(unsigned int regno);
static void hexagon_make_prologue_epilogue_decisions(
              struct hexagon_frame_info *info);
static struct hexagon_frame_info *hexagon_frame_info(void);

static bool hexagon_must_pass_in_stack(enum machine_mode mode, const_tree type);

static bool hexagon_vector_mode_supported_p(enum machine_mode mode);

static rtx hexagon_function_value(
             const_tree ret_type,
             const_tree fn_decl_or_type,
             bool outgoing);

static bool hexagon_return_in_memory(const_tree type, const_tree fntype);

static void hexagon_asm_function_prologue(FILE *file, HOST_WIDE_INT size);

static bool hexagon_function_ok_for_sibcall(tree decl, tree exp);

#if HEXAGON_DINKUMWARE
static void hexagon_init_libfuncs(void);
#endif /* HEXAGON_DINKUMWARE */

static bool hexagon_legit_addr_const_p(
              HOST_WIDE_INT value,
              enum machine_mode mode,
              int num_bits);
static bool hexagon_reg_ok_for_base_p(rtx x, bool reg_ok_strict_p);
static bool hexagon_reg_ok_for_index_p(rtx x, bool reg_ok_strict_p);
static tree hexagon_vectorize_builtin_mask_for_load(void);

static bool hexagon_free_immediate(rtx x, int outer_code, int value);
static bool hexagon_rtx_costs(
              rtx x,
              int code,
              int outer_code,
              int *total,
              bool speed);
bool hexagon_rtx_costs_debug(
       rtx x,
       int code,
       int outer_code,
       int *total,
       bool speed);
static int hexagon_address_cost(rtx address, bool speed);
int hexagon_address_cost_debug(rtx address, bool speed);

static int hexagon_sched_issue_rate(void);
static void hexagon_sched_dependencies_eval (rtx, rtx);
static int hexagon_sched_first_cycle_multipass_dfa_lookahead(void);

static section *hexagon_asm_select_rtx_section(
                  enum machine_mode mode,
                  rtx x,
                  unsigned HOST_WIDE_INT align);
static section * hexagon_select_section (tree decl, int reloc, unsigned HOST_WIDE_INT align ATTRIBUTE_UNUSED); 
static bool hexagon_in_small_data_p(const_tree exp);
static void qpds6_load_pic_register (void);
static void hexagon_unique_section (tree decl, int reloc); 
static void hexagon_elf_asm_named_section (const char *name, unsigned int flags,tree decl ATTRIBUTE_UNUSED); 

static void hexagon_output_operand(FILE *f, rtx x, int code);

static void hexagon_fixup_cfg(void);
static void hexagon_fixup_doloops(void);
static void hexagon_machine_dependent_reorg(void);
static void hexagon_local_combine_pass(void);

static void hexagon_init_builtins(void);

static tree hexagon_builtin_decl (unsigned code, bool initialize_p ATTRIBUTE_UNUSED);

static rtx expand_one_builtin(
             enum insn_code icode,
             rtx target,
             tree exp,
             int nargs);
static rtx hexagon_expand_builtin(
             tree exp,
             rtx target,
             rtx subtarget,
             enum machine_mode mode,
             int ignore);
static const char *hexagon_invalid_within_doloop(const_rtx insn);
static void hexagon_print_jump(FILE *file, const_rtx x);
static void hexagon_print_transfer(FILE *file, const_rtx x);
static void hexagon_print_condition(FILE *file, const_rtx x, bool non_inverted);
static void hexagon_print_address(FILE *file, const_rtx x);
static void hexagon_print_unary_op(FILE *file, const char *op, const_rtx x);
static void hexagon_print_binary_op(FILE *file, const char *op, const_rtx x);
static void hexagon_print_swapped_binary_op(FILE *file, const char *op, const_rtx x);
static void hexagon_print_binary_op_with_option(FILE *file, const char *op, const char *option, const_rtx x);
static void hexagon_print_trinary_op(FILE *file, const char *op, const_rtx x);
static void hexagon_print_vecexp(FILE *file, const char *open, const char *separator, const char *close, const_rtx x);
static void hexagon_print_rtx(FILE *file, const_rtx x);
static void hexagon_print_rtl_pseudo_asm(FILE *stream, const_rtx x);

static void hexagon_compute_dwarf_frame_information(void);
static void hexagon_allocate_stack(
              unsigned HOST_WIDE_INT size,
              int allocate_stack_insn);
static void hexagon_deallocate_stack(unsigned HOST_WIDE_INT size);
static tree hexagon_special_case_memcpy_fn(const char *name);
static void hexagon_emit_special_case_memcpy_fn(
              tree *fn,
              const char *name,
              rtx dst,
              rtx src,
              rtx size,
              bool tailcall);
static void hexagon_expand_movmem_inline(rtx operands[], bool volatile_p);

void hexagon_print_insn_info(FILE *file, struct hexagon_insn_info *insn_info);
void hexagon_debug_insn_info(struct hexagon_insn_info *insn_info);
void hexagon_print_packet(FILE *file, struct hexagon_packet_info *packet);
void hexagon_print_packets(FILE *file, struct hexagon_packet_info *packet);
void hexagon_debug_packet(struct hexagon_packet_info *packet);
void hexagon_debug_packets(void);
void hexagon_print_bb_packets(FILE *file, basic_block bb);
void hexagon_debug_all_bb_packets(void);
void hexagon_debug_bb_packets(basic_block bb);

static int  hexagon_get_flags(rtx insn);
static struct hexagon_reg_access *hexagon_add_reg_access(
                                  struct hexagon_reg_access *accesses,
                                  rtx reg,
                                  int flags);
static struct hexagon_mem_access *hexagon_add_mem_access(
                                  struct hexagon_mem_access *accesses,
                                  rtx mem,
                                  int flags);
static int  hexagon_record_writes(rtx *x, void *insn_info);
static int  hexagon_record_reads(rtx *x, void *insn_info);
static struct hexagon_insn_info *hexagon_get_insn_info(rtx insn);
static struct hexagon_packet_info *hexagon_start_new_packet(void);
static void hexagon_add_insn_to_packet(
              struct hexagon_packet_info *packet,
              struct hexagon_insn_info *insn_info,
              bool add_to_beginning);
static void hexagon_remove_insn_from_packet(
              struct hexagon_packet_info *packet,
              struct hexagon_insn_info *insn_info);
static bool hexagon_can_speculate_p(
              struct hexagon_insn_info *insn_info,
              basic_block bb);
static void hexagon_add_live_out(struct hexagon_insn_info *insn_info, basic_block bb);
static bool hexagon_predicable_p(struct hexagon_insn_info *insn_info);
static struct hexagon_insn_info *hexagon_predicate_insn(
                                 struct hexagon_insn_info *insn_info,
                                 struct hexagon_insn_info *jump_insn_info,
                                 bool invert_condition);
static bool hexagon_gpr_dot_newable_p(
              struct hexagon_insn_info *producer,
              struct hexagon_insn_info *consumer,
              struct hexagon_dependence *dependence);
static struct hexagon_insn_info *hexagon_dot_newify_gpr(
                                 struct hexagon_insn_info *insn_info,
                                 struct hexagon_dependence *dependence);
static int hexagon_find_new_value(rtx *x, void *y);
static void hexagon_dot_oldify_gpr(struct hexagon_insn_info *insn_info);
static bool hexagon_predicate_dot_newable_p(struct hexagon_insn_info *insn_info);
static struct hexagon_insn_info *hexagon_dot_newify_predicate(
                                 struct hexagon_insn_info *insn_info);
static bool hexagon_prologue_insn_p(struct hexagon_insn_info *insn_info);
static struct hexagon_dependence *hexagon_add_dependence(
                                  struct hexagon_dependence *dependencies,
                                  enum hexagon_dependence_type type,
                                  rtx set,
                                  rtx use);
static struct hexagon_dependence *hexagon_remove_dependence(
                                  struct hexagon_dependence *dependencies,
                                  struct hexagon_dependence *dependence);
static struct hexagon_dependence *hexagon_concat_dependencies(
                                  struct hexagon_dependence *a,
                                  struct hexagon_dependence *b);
static struct hexagon_dependence *hexagon_control_dependencies(
                                  struct hexagon_insn_info *first,
                                  struct hexagon_insn_info *second);
static struct hexagon_dependence *hexagon_true_dependencies(
                                  struct hexagon_insn_info *writer,
                                  struct hexagon_insn_info *reader);
static struct hexagon_dependence *hexagon_output_dependencies(
                                  struct hexagon_insn_info *insn0,
                                  struct hexagon_insn_info *insn1);
static struct hexagon_dependence *hexagon_anti_dependencies(
                                  struct hexagon_insn_info *earlier,
                                  struct hexagon_insn_info *later);
static bool hexagon_packet_insn_dependence_p(
              struct hexagon_packet_info *packet,
              struct hexagon_insn_info **insn_info,
              bool ignore_jumps);
static bool hexagon_packet_insn_internal_dependence_p(
              struct hexagon_packet_info *packet,
              struct hexagon_insn_info *insn_info);
static bool hexagon_insn_fits_in_packet_p(
              struct hexagon_insn_info *insn,
              struct hexagon_packet_info *packet);
static bool hexagon_can_add_insn_to_packet_p(
              struct hexagon_insn_info **insn,
              struct hexagon_packet_info *packet);
static rtx  hexagon_bb_real_head_insn(basic_block bb);
static rtx  hexagon_bb_real_end_insn(basic_block bb);
static void hexagon_create_bb_sentinel_packet(struct hexagon_packet_info *packet);
static void hexagon_finalize_transformations(
              struct hexagon_packet_info *first,
              struct hexagon_packet_info *last);
static void hexagon_pack_insns(bool need_bb_info);
static void hexagon_move_insn(
              struct hexagon_insn_info *old_insn,
              struct hexagon_packet_info *from_packet,
              struct hexagon_insn_info *new_insn,
              struct hexagon_packet_info *to_packet,
              bool move_to_beginning);
static void hexagon_sanity_check_cfg_packet_info(void);
static void hexagon_pull_up_insns(void);
static void hexagon_init_packing_info(bool need_bb_info);
static void hexagon_remove_new_values(void);
static void hexagon_free_packing_info(bool free_bb_info);
static void hexagon_packet_optimizations(void);
static bool hexagon_move_insn_down_p(struct hexagon_insn_info* insn, 
             struct hexagon_packet_info* pred_packet, 
             struct hexagon_packet_info* succ_packet);

static void hexagon_final_pack_insns(void);
static void hexagon_pack_duplex_insns(void);


bool is_restrict_qualified (tree t);

static bool hexagon_can_be_new_value_store_p(
  struct hexagon_insn_info *producer, 
  struct hexagon_insn_info *consumer,
  struct hexagon_dependence *dependencer);

static bool hexagon_can_be_new_value_p(
  struct hexagon_insn_info *producer, 
  struct hexagon_insn_info *consumer,
  struct hexagon_dependence *dependencer);

/*generate a new value nump for V4 */
static bool hexagon_can_be_new_value_jump_p(
  struct hexagon_insn_info *consumer,
  struct hexagon_dependence *dependencer);
static void hexagon_new_value_jump(void ); 
static struct hexagon_insn_info * hexagon_nvj_query_jump(
              struct hexagon_packet_info *packet, 
              bool *dot_new_predicate,
              basic_block bb);
static struct hexagon_insn_info * hexagon_nvj_query_compare (
              struct hexagon_packet_info *packet,
              struct hexagon_insn_info *jump_p_insn_info);
static bool hexagon_used_operands( 
              struct hexagon_packet_info *packet, 
              struct hexagon_insn_info *jump_p_insn_info,
              struct hexagon_insn_info *compare_insn_info);
static bool hexagon_register_defined(
              struct hexagon_insn_info *insn, 
              unsigned int reg_no );
static bool hexagon_register_used(
              struct hexagon_insn_info *insn,
              unsigned int reg_no  );
static struct hexagon_packet_info * hexagon_get_source_packet(
              struct hexagon_packet_info *packet, 
              rtx feeder_reg, 
              struct hexagon_insn_info *d_insn,
              struct hexagon_insn_info **s_insn);
static bool hexagon_move_insn_across_packet_down( 
              struct hexagon_packet_info *from_packet, 
              struct hexagon_packet_info *to_packet, 
              struct hexagon_insn_info *insn);
static bool hexagon_nvj_move_possible(
              struct hexagon_packet_info *candidate_packet,
              struct hexagon_packet_info *prev_packet,
              struct hexagon_insn_info *jump_p_insn_info, 
              struct hexagon_insn_info *compare_info_info, 
              rtx *operator, 
              rtx *pred,
              rtx *op1, 
              rtx *op2,
              rtx *b_label,
              struct hexagon_packet_info **src_packet,
              struct hexagon_insn_info **src_insn,
              int *op_cnt);

static bool hexagon_nvj_compare_p(rtx insn);
static int  hexagon_get_reads_count(struct hexagon_insn_info *insn_info);

static bool hexagon_nvj_new_gpr_p(
              struct hexagon_insn_info *consumer,
              struct hexagon_dependence *dependence);
static bool hexagon_nvj_check_resources ( 
              struct hexagon_insn_info *q_insn, 
              struct hexagon_packet_info *nvj_packet,
              struct hexagon_insn_info *comp_insn, 
              struct hexagon_insn_info *jump_insn, 
              rtx nvj_insn_rtx );
static bool hexagon_in_bb_live_out( 
              basic_block bb, 
              struct hexagon_insn_info *q_insn);
static void hexagon_remove_empty_packet( 
              basic_block bb,
              struct hexagon_packet_info *packet);
static bool hexagon_predicate_use_DImode( struct hexagon_insn_info *insn_info);
static rtx hexagon_nvj_swap_operands(rtx insn);
static rtx hexagon_nvj_get_compare( rtx nvj_insn, int elem_num);
static rtx hexagon_nvj_get_operand( rtx insn, int op_count);
void 
hexagon_duplicate_doloop_begin(basic_block condition_bb, struct loop *loop);


/* Initialize the GCC target structure. */

/*---------------------------
Run-time Target Specification
---------------------------*/

#undef TARGET_DEFAULT_TARGET_FLAGS
#define TARGET_DEFAULT_TARGET_FLAGS \
  (MASK_LITERAL_POOL | MASK_LITERAL_POOL_ADDRESSES | MASK_HARDWARE_LOOPS \
   | MASK_NEW_PREDICATES | MASK_NEW_VALUE_STORES | MASK_BASE_PLUS_INDEX \
   | MASK_MEMOPS | MASK_SECTION_SORTING | MASK_SECTION_SORTING_CODE_SUPPORT \
   | MASK_DEEP_PHI_MATCH)

#undef TARGET_HANDLE_OPTION
#define TARGET_HANDLE_OPTION hexagon_handle_option


/*------------
Storage Layout
------------*/

/* Integer arguments and return values should be sign- or zero-extended to a 
   full register or register pair before being passed/returned. */
#undef TARGET_PROMOTE_FUNCTION_MODE
#define TARGET_PROMOTE_FUNCTION_MODE default_promote_function_mode_always_promote

#undef TARGET_ALIGN_ANON_BITFIELD
#define TARGET_ALIGN_ANON_BITFIELD hexagon_align_anon_bitfield

/*bool TARGET_VECTOR_OPAQUE_P (tree type)*/ /* ??? Should this be true? */


/*----------------------------------
Layout of Source Language Data Types
----------------------------------*/

#undef TARGET_DEFAULT_SHORT_ENUMS
#define TARGET_DEFAULT_SHORT_ENUMS hexagon_default_short_enums


/*--------------
Register Classes
--------------*/

#undef TARGET_SECONDARY_RELOAD
#define TARGET_SECONDARY_RELOAD hexagon_secondary_reload


/*----------------------------
Passing Arguments in Registers
----------------------------*/

#undef TARGET_MUST_PASS_IN_STACK
#define TARGET_MUST_PASS_IN_STACK hexagon_must_pass_in_stack

#undef TARGET_VECTOR_MODE_SUPPORTED_P
#define TARGET_VECTOR_MODE_SUPPORTED_P hexagon_vector_mode_supported_p


/*-------------------------------------
How Scalar Function Values Are Returned
-------------------------------------*/

#undef TARGET_FUNCTION_VALUE
#define TARGET_FUNCTION_VALUE hexagon_function_value


/*---------------------------
How Large Values Are Returned
---------------------------*/

#undef TARGET_RETURN_IN_MEMORY
#define TARGET_RETURN_IN_MEMORY hexagon_return_in_memory


/*---------------------
Function Entry and Exit
---------------------*/

#undef TARGET_ASM_FUNCTION_PROLOGUE
#define TARGET_ASM_FUNCTION_PROLOGUE hexagon_asm_function_prologue


/*-------------------
Permitting tail calls
-------------------*/

#undef  TARGET_FUNCTION_OK_FOR_SIBCALL
#define TARGET_FUNCTION_OK_FOR_SIBCALL hexagon_function_ok_for_sibcall


/*-----------------------------
Implementing the Varargs Macros
-----------------------------*/

#undef TARGET_STRICT_ARGUMENT_NAMING
#define TARGET_STRICT_ARGUMENT_NAMING hook_bool_CUMULATIVE_ARGS_true


/*--------------------------------
Implicit Calls to Library Routines
--------------------------------*/

#if HEXAGON_DINKUMWARE
#undef TARGET_INIT_LIBFUNCS
#define TARGET_INIT_LIBFUNCS hexagon_init_libfuncs
#endif /* HEXAGON_DINKUMWARE */


/*--------------
Addressing Modes
--------------*/

#undef TARGET_VECTORIZE_BUILTIN_MASK_FOR_LOAD
#define TARGET_VECTORIZE_BUILTIN_MASK_FOR_LOAD \
  hexagon_vectorize_builtin_mask_for_load


/*-------------------------------------
Describing Relative Costs of Operations
-------------------------------------*/

#undef TARGET_RTX_COSTS
#define TARGET_RTX_COSTS hexagon_rtx_costs

#undef TARGET_ADDRESS_COST
#define TARGET_ADDRESS_COST hexagon_address_cost


/*---------------------------------
Adjusting the Instruction Scheduler
---------------------------------*/

#undef TARGET_SCHED_ISSUE_RATE
#define TARGET_SCHED_ISSUE_RATE hexagon_sched_issue_rate

#undef TARGET_SCHED_FIRST_CYCLE_MULTIPASS_DFA_LOOKAHEAD
#define TARGET_SCHED_FIRST_CYCLE_MULTIPASS_DFA_LOOKAHEAD \
  hexagon_sched_first_cycle_multipass_dfa_lookahead

/*--------------------------------------------------
Dividing the Output into Sections (Texts, Data, ...)
--------------------------------------------------*/

#undef TARGET_ASM_SELECT_RTX_SECTION
#define TARGET_ASM_SELECT_RTX_SECTION hexagon_asm_select_rtx_section

#undef TARGET_IN_SMALL_DATA_P
#define TARGET_IN_SMALL_DATA_P hexagon_in_small_data_p

#undef TARGET_ASM_UNIQUE_SECTION
#define TARGET_ASM_UNIQUE_SECTION hexagon_unique_section // _LSY_ 

#undef TARGET_ASM_SELECT_SECTION
#define TARGET_ASM_SELECT_SECTION hexagon_select_section // _LSY_ 

#undef TARGET_ASM_NAMED_SECTION
#define TARGET_ASM_NAMED_SECTION  hexagon_elf_asm_named_section // _LSY_ 

//#undef TARGET_IRA_COVER_CLASSES
//#define TARGET_IRA_COVER_CLASSES hexagon_ira_cover_classes


/*------------
Output of Data
------------*/

#undef TARGET_ASM_ALIGNED_HI_OP
#define TARGET_ASM_ALIGNED_HI_OP "\t.hword\t"

#undef TARGET_ASM_ALIGNED_SI_OP
#define TARGET_ASM_ALIGNED_SI_OP "\t.word\t"


/*----------------------
Miscellaneous Parameters
----------------------*/

#undef TARGET_MACHINE_DEPENDENT_REORG
#define TARGET_MACHINE_DEPENDENT_REORG hexagon_machine_dependent_reorg

#undef TARGET_INIT_BUILTINS
#define TARGET_INIT_BUILTINS  hexagon_init_builtins

#undef TARGET_BUILTIN_DECL
#define TARGET_BUILTIN_DECL hexagon_builtin_decl

#undef TARGET_EXPAND_BUILTIN
#define TARGET_EXPAND_BUILTIN hexagon_expand_builtin

/*tree TARGET_RESOLVE_OVERLOADED_BUILTIN (tree fndecl, tree arglist)*/
/*tree TARGET_FOLD_BUILTIN (tree fndecl, tree arglist, bool ignore)*/

#undef TARGET_INVALID_WITHIN_DOLOOP
#define TARGET_INVALID_WITHIN_DOLOOP hexagon_invalid_within_doloop

/* ??? Should this be GENERAL_REGS? */
/*int TARGET_BRANCH_TARGET_REGISTER_CLASS (void)*/

#undef TARGET_PRINT_RTL_PSEUDO_ASM
#define TARGET_PRINT_RTL_PSEUDO_ASM hexagon_print_rtl_pseudo_asm

#undef TARGET_LOOP_INVALID_FOR_FORCED_UNROLL
#define TARGET_LOOP_INVALID_FOR_FORCED_UNROLL   hexagon_loop_invalid_for_forced_unroll


struct gcc_target targetm = TARGET_INITIALIZER;

static enum section_category	hexagon_categorize_decl_for_section (const_tree decl, int reloc); 
void default_unique_section_2 (tree decl, int reloc); 
unsigned HOST_WIDE_INT  smallest_accessable_entity_in_declaration(tree decl); 
bool has_this_tree_been_visited(tree node); 
void remember_this_tree(tree node); 
unsigned int descent_smallest(const char *prefix, tree node, unsigned int smallest); 
int hexagon_named_section_sbss (tree decl, const char *name, int reloc); 
extern section * get_named_section (tree decl, const char *name, int reloc); 
/*---------------------------
Run-time Target Specification
---------------------------*/

static const struct hexagon_arch_table_entry hexagon_arch_table[NUM_HEXAGON_ARCH] =
  HEXAGON_ARCH_TABLE_INITIALIZER;

static const struct hexagon_abi_table_entry hexagon_abi_table[NUM_HEXAGON_ABI] =
  HEXAGON_ABI_TABLE_INITIALIZER;

/* Implements hook TARGET_HANDLE_OPTION

   Process command-line options such as -march. */

static bool
hexagon_handle_option(size_t code, const char *arg, int value ATTRIBUTE_UNUSED)
{
  int i;

  switch(code){
    case OPT_march_:
    case OPT_mcpu_:
      for(i = 0; i < NUM_HEXAGON_ARCH; i++){
        if(strcmp(arg, hexagon_arch_table[i].name) == 0){
          hexagon_arch = hexagon_arch_table[i].arch;
          hexagon_features = hexagon_arch_table[i].features;
          return true;
        }
      }
      error("bad value (%s) for -m%s= option",
            arg, code == OPT_march_ ? "arch" : "cpu");
      return false;
    case OPT_mabi_:
      for(i = 0; i < NUM_HEXAGON_ABI; i++){
        if(strcmp(arg, hexagon_abi_table[i].name) == 0){
          hexagon_abi = hexagon_abi_table[i].abi;
          return true;
        }
      }
      error("bad value (%s) for -mabi= option", arg);
      return false;
    case OPT_mno_falign:
      hexagon_falign = HEXAGON_NO_FALIGN;
      return true;
    case OPT_mfalign_loops:
      hexagon_falign = HEXAGON_FALIGN_LOOPS;
      return true;
    case OPT_mfalign_labels:
      hexagon_falign = HEXAGON_FALIGN_LABELS;
      return true;
    case OPT_mfalign_all:
      hexagon_falign = HEXAGON_FALIGN_ALL;
      return true;
    case OPT_mqdsp6_compat:
      hexagon_qdsp6_compat = 1;
      return true;
  }
  return true;
}




/* Implements macro OVERRIDE_OPTIONS

   Make any necessary final decisions about command-line options. */

void
hexagon_override_options(void)
{
  int arch_index;
  int abi_index;

  if(hexagon_arch == HEXAGON_ARCH_UNSPECIFIED){
    arch_index = HEXAGON_ARCH_TABLE_DEFAULT_INDEX;
    hexagon_arch = hexagon_arch_table[arch_index].arch;
    hexagon_features = hexagon_arch_table[arch_index].features;
  }

  if(hexagon_arch == HEXAGON_ARCH_V1){
    error("Architecture hexagonv1 is no longer supported.");
  }

  if(hexagon_abi == HEXAGON_ABI_UNSPECIFIED){
    abi_index = HEXAGON_ABI_TABLE_DEFAULT_INDEX;
    hexagon_abi = hexagon_abi_table[abi_index].abi;
  }

  if(TARGET_UNCACHED_DATA){
    if(hexagon_arch == HEXAGON_ARCH_V1 || hexagon_arch == HEXAGON_ARCH_V2){
      hexagon_dual_memory_accesses = false;
    }
    else {
      warning(0, "Ignoring the -mv1-v2-uncached-data option as it is only valid for V1 an V2.");
    }
  }

  if(!TARGET_PACKETS){
    target_flags &= ~MASK_PULLUP;
  }

  if(!optimize){
    target_flags &= ~MASK_PACKETS;
    target_flags &= ~MASK_PULLUP;
    hexagon_falign = HEXAGON_NO_FALIGN;
  }

  if(!g_switch_set){
#ifdef LINUX
  /* On Linux, use -G0 as the default */
    g_switch_value = 0;
#else
    g_switch_value = 8;
#endif
  }

  /* Align functions to 16-byte boundaries to prevent
     target-packet-crosses-16-byte-boundary (falign) stalls. */
  if(align_functions == 0){
    align_functions = 16;
  }

  if(!TARGET_CONST32 || !TARGET_LITERAL_POOL_ADDRESSES || hexagon_arch >= HEXAGON_ARCH_V4)
    target_flags &= ~MASK_AGGREGATE_ACCESS;

  /* Taxis code degraded immensely because of the subreg1 pass.  The pass splits
     double word opcodes into single words, which resulted in larger packet
     size.  See Qualcomm Bugzilla #3659 for the details.  To enable the subreg1
     pass, use -menable-subreg1 */
  if(!TARGET_ENABLE_SUBREG1){
    flag_split_wide_types = false;
  }

}




/* Implements macro OPTIMIZATION_OPTIONS

   Set defaults for flags based on optimization level. */

void
hexagon_optimization_options(int level, int size)
{
  if(size){
    target_flags |= MASK_EXTENDED_CROSSJUMPING;
    target_flags |= MASK_LOCAL_COMBINE;
    target_flags |= MASK_DUPLEX_SCHEDULING;
  }

  if(level >= 2){
    target_flags |= MASK_PACKETS;
    target_flags |= MASK_PULLUP;
    target_flags |= MASK_AGGREGATE_ACCESS;
    target_flags |= MASK_LOCAL_COMBINE;
  }

  hexagon_falign = HEXAGON_NO_FALIGN;
  if(level >= 3 && !size){
    hexagon_falign = HEXAGON_FALIGN_ALL;
  }
  else if(level >= 1 && !size){
    hexagon_falign = HEXAGON_FALIGN_LOOPS;
  }
}




/*---------------------------------------------------
Defining data structures for per-function information
---------------------------------------------------*/

/* Implements macro INIT_EXPANDERS */

void
hexagon_init_expanders(void)
{
  init_machine_status = hexagon_init_machine_status;
}




/* initializes the machine specific per-function data */

static struct machine_function *
hexagon_init_machine_status(void)
{
  struct machine_function *mf;
  mf = (struct machine_function *)ggc_alloc_cleared(sizeof(struct machine_function));
  return mf;
}




/*------------
Storage Layout
------------*/

/* Return the TYPE of the elements comprising
   the innermost dimension of ARRAY.  */

static tree
get_inner_array_type (const_tree array)
{
  tree type = TREE_TYPE (array);

  while (TREE_CODE (type) == ARRAY_TYPE)
    type = TREE_TYPE (type);

  return type;
}




/* Helper function for the alignment routines

   Aligns arrays whose element sizes are <= BITS_PER_WORD
   to BIGGEST_ALIGNMENT.  This facilitates vectorization. */

static int
hexagon_array_alignment(tree type, int align)
{
  tree elem_type = get_inner_array_type(type);

  if(TYPE_SIZE (elem_type)
     && TREE_CODE (TYPE_SIZE (elem_type)) == INTEGER_CST
     && TREE_INT_CST_LOW (TYPE_SIZE (elem_type)) <= BITS_PER_WORD){
    return BIGGEST_ALIGNMENT;
  }
  else {
    return align;
  }
}




/* Implements macro DATA_ALIGNMENT

   Align a static variable
   Doubleword align arrays whose element size <= 4 bytes to facilitate
   vectorization. */

int
hexagon_data_alignment(tree type, int align)
{
  if(TREE_CODE (type) == ARRAY_TYPE){
    return hexagon_array_alignment(type, align);
  }

  return align;
}




/* Implements macro CONSTANT_ALIGNMENT

   Doubleword align constant strings. */

int
hexagon_constant_alignment(tree constant, int align)
{
  if(!optimize_size && TREE_CODE (constant) == STRING_CST
     && TREE_STRING_LENGTH (constant) >= BIGGEST_ALIGNMENT
     && (align) < BIGGEST_ALIGNMENT){
    return BIGGEST_ALIGNMENT;
  }

  return align;
}




/* Implements macro LOCAL_ALIGNMENT

   Align a local variable on the stack
   Doubleword align arrays whose element size <= 4 bytes to facilitate
   vectorization. */

unsigned int
hexagon_local_alignment(tree type, int align)
{
  if(TREE_CODE (type) == ARRAY_TYPE){
    return hexagon_array_alignment(type, align);
  }

  return align;
}




/* Implements hook TARGET_ALIGN_ANON_BITFIELD

   Unnamed (anonymous) bitfields affect alignment and padding the same way named
   bitfields do. */

static bool
hexagon_align_anon_bitfield(void)
{
  return true;
}




/*----------------------------------
Layout of Source Language Data Types
----------------------------------*/

/* Implements hook TARGET_DEFAULT_SHORT_ENUMS

   The default ABI specifies that enumerated types behave like the smallest
   integer type that can hold all of the enumerated constants associated with
   the enumerated type.  Linux requires its ABI to specify non-short enums. */

static bool
hexagon_default_short_enums(void)
{
  return hexagon_abi != HEXAGON_ABI_LINUX;
}




/*--------------------------------
Basic Characteristics of Registers
--------------------------------*/

/* Implements macro CONDITIONAL_REGISTER_USAGE

   HEXAGON ABI 2 increases the number of callee save registers from 4 to 12. */

void
hexagon_conditional_register_usage(void)
{
  int i;
  if(hexagon_abi != HEXAGON_ABI_1){
    for(i = 16; i < 24; i++){
      if(!fixed_regs[i]){
        call_used_regs[i] = 0;
      }
    }
  }

  /* For PIC, we reserve a register for the GOT pointer */
  if (flag_pic) {
    fixed_regs[PIC_OFFSET_TABLE_REGNUM] = 1;
    call_used_regs[PIC_OFFSET_TABLE_REGNUM] = 1;
  }
}




/*--------------
Register Classes
--------------*/

/* Implements macro CANNOT_CHANGE_MODE_CLASS

   Prevent predicates from being represented as QImode SUBREGs of SImode. */

bool
hexagon_cannot_change_mode_class(
  enum machine_mode from,
  enum machine_mode to,
  enum reg_class rclass
)
{
  if(from == to){
    return false;
  }

  if(rclass == PREDICATE_REGS
     && from == SImode
     && to == QImode){
    return true;
  }

  return false;
}




/* Implements macro CONST_OK_FOR_CONSTRAINT_P

   IsN means signed, two's complement integers in [-2^(N-1), 2^(N-1) - 1]
   IuN means unsigned integers in [0, 2^N - 1]
   InN means negative integers in [-(2^N - 1), 0]
   ImN means signed magnitude integers in [-(2^(N-1) - 1), 2^(N-1) - 1]

   J[sunm]N_M means I[sunm]N shifted left M bits
   
   K-1 means -1
   K01 means  1
   K16 means 16
   K32 means 32
   Ku7p1 integers in [1, 128]
   Ks8p1 integers in [-127, 128]
   Ku5_3p8 integers in [8, 256]
   Ku9p1 integers in [1, 512]
   Ks10p1 integers in [-511, 512]
   Ks8s8 means integers that can be formed using combine(#s8,#s8)
   Konehot32 means power of 2 integers that can be represented in 32 bits
   Konenot32 means one's complements of Konehot32 constants */

bool
hexagon_const_ok_for_constraint_p(HOST_WIDE_INT value, char c, const char *str)
{
  const char *p;
  HOST_WIDE_INT bits;
  HOST_WIDE_INT low;
  HOST_WIDE_INT high;
  HOST_WIDE_INT scale;
  HOST_WIDE_INT scale_bits;

  switch(c){
    case 'I':
    case 'J':
      if(!((str[1] == 's' || str[1] == 'u' || str[1] == 'n' || str[1] == 'm')
           && ISDIGIT (str[2]))){
        return false;
      }

      bits = 0;
      low = 0;
      high = 0;
      scale = 0;
      scale_bits = 0;

      p = &str[2];
      do {
        bits = (10 * bits) + (*p++ - '0');
      }while(ISDIGIT (*p));

      if(str[1] == 's'){
        if(bits == 0){
          return false;
        }
        else {
          low = -(1 << (bits - 1));
          high = (1 << (bits - 1)) - 1;
        }
      }
      else if(str[1] == 'u'){
        low = 0;
        high = (1 << bits) - 1;
      }
      else if(str[1] == 'n'){
        low = -((1 << bits) - 1);
        high = 0;
      }
      else if(str[1] == 'm'){
        high = (1 << (bits - 1)) - 1;
        low = -high;
      }

      if(c == 'J'){
        if(!(p[0] == '_' && ISDIGIT (p[1]))){
          return false;
        }

        p++;
        do {
          scale = (10 * scale) + (*p++ - '0');
        }while(ISDIGIT (*p));

        high <<= scale;
        low <<= scale;
        scale_bits = value & ((1 << scale) - 1);
      }

      return low <= value && value <= high && scale_bits == 0;

    case 'K':
      if(HEXAGON_CONSTRAINT_P(str, -1)){
        return value == -1;
      }
      else if(HEXAGON_CONSTRAINT_P(str, 01)){
        return value == 1;
      }
      else if(HEXAGON_CONSTRAINT_P(str, 16)){
        return value == 16;
      }
      else if(HEXAGON_CONSTRAINT_P(str, 32)){
        return value == 32;
      }
      else if(HEXAGON_CONSTRAINT_P(str, u7p1)){
        return IN_RANGE (value, 1, 128);
      }
      else if(HEXAGON_CONSTRAINT_P(str, s8p1)){
        return IN_RANGE (value, -127, 128);
      }
      else if(HEXAGON_CONSTRAINT_P(str, u5_3p8)){
        return IN_RANGE (value, 8, 256);
      }
      else if(HEXAGON_CONSTRAINT_P(str, u9p1)){
        return IN_RANGE (value, 1, 512);
      }
      else if(HEXAGON_CONSTRAINT_P(str, s10p1)){
        return IN_RANGE (value, -511, 512);
      }
      else if(HEXAGON_CONSTRAINT_P(str, s8s8)){
        high = value >> 32ULL;
        low = value & 0xFFFFFFFFULL;
        return ((high & 0xFFFFFF00) == (high & 0x80 ? 0xFFFFFF00 : 0))
            && ((low  & 0xFFFFFF00) == (low  & 0x80 ? 0xFFFFFF00 : 0));
      }
      else if(HEXAGON_CONSTRAINT_P(str, onehot32)){
        value &= 0xFFFFFFFFULL;
        return value == (value & -value);
      }
      else if(HEXAGON_CONSTRAINT_P(str, onenot32)){
        value = ~value & 0xFFFFFFFFULL;
        return value == (value & -value);
      }
      return false;

    default:
      return false;
  }
}




/* Implements hook TARGET_SECONDARY_RELOAD

   Predicate registers can not be directly loaded from or stored to memory.
   The value must first be moved to a general purpose register. */

static enum reg_class
hexagon_secondary_reload(
  bool in_p ATTRIBUTE_UNUSED,
  rtx x,
  enum reg_class reload_class,
  enum machine_mode reload_mode ATTRIBUTE_UNUSED,
  secondary_reload_info *sri ATTRIBUTE_UNUSED
)
{
  switch(reload_class){
    case PREDICATE_REGS:
      if(true_regnum(x) < 0){
        return GENERAL_REGS;
      }
      break;
    default:
      break;
  }
  return NO_REGS;
}




/*----------------
Basic Stack Layout
----------------*/

/* Implements macro RETURN_ADDR_RTX

   Return an RTX indicating where the return address can be found given FRAME,
   the address of the stack frame COUNT frames above the current one. */

rtx
hexagon_return_addr_rtx(int count, rtx frame)
{
  rtx return_addr;

  cfun->machine->calls_builtin_return_address = true;

  if(count == 0){
    frame = gen_rtx_REG(Pmode, HARD_FRAME_POINTER_REGNUM);
  }

  return_addr = memory_address(Pmode,
                               plus_constant(frame, GET_MODE_SIZE (Pmode)));
  return_addr = gen_rtx_MEM (Pmode, return_addr);
  set_mem_alias_set(return_addr, get_frame_alias_set());

  return return_addr;
}




/*---------------------------------------
Eliminating Frame Pointer and Arg Pointer
---------------------------------------*/

/* HEXAGON stack frames look like:

             Before call                       After call


        +-----------------------+       +-----------------------+
        | 4 bytes save area for |       | 4 bytes save area for |
        | each of LR and prevFP |       | each of LR and prevFP |
        | (8 bytes total)       |       | (8 bytes total)       |
  FP+0->+-----------------------+       +-----------------------+
        |                       |       |                       |
   high |  local variables,     |       |  local variables,     |
   mem  |  reg save area, etc.  |       |  reg save area, etc.  |
        |                       |       |                       |
        +-----------------------+       +-----------------------+
        |                       |       |                       |
        |  arguments on stack.  |       |  arguments on stack.  |
        |                       |       |                       |
  SP+0->+-----------------------+       +-----------------------+
                                        | 4 bytes save area for |
                                        | each of LR and prevFP |
                                        | (8 bytes total)       |
                                  FP+0->+-----------------------+
                                        |                       |
                                        |  register save area   |
                                        |  (callee saved)       |
                                        |                       |
                                        +-----------------------+
                                        |                       |
                                        |  local variables      |
                                        |                       |
                                        +-----------------------+
                                        |                       |
                                        |  alloca allocations   |
                                        |                       |
                                        +-----------------------+
                                        |                       |
                 arguments grow updards |  arguments on stack   |
                                        |                       |
                                  SP+0->+-----------------------+
   low
   memory

*/

/* Helper function for computing the frame info

   True if register REGNO should be saved/restored in the prologue/epilogue. */

static bool
hexagon_save_register_p(unsigned int regno)
{
  unsigned int eh_regno;
  unsigned int i;

  if(regno >= FIRST_PSEUDO_REGISTER){
    return false;
  }

  if(crtl->calls_eh_return){
    i = 0;
    do {
      eh_regno = EH_RETURN_DATA_REGNO (i);
      if(eh_regno == regno){
        return true;
      }
      i++;
    }while(eh_regno != INVALID_REGNUM);
  }

  /* The return address and frame pointer are treated separately.  Don't
     consider them here. */
  return regno != LINK_REGNUM
      && regno != HARD_FRAME_POINTER_REGNUM
      && !call_used_regs[regno]
      && (df_regs_ever_live_p(regno)
          || crtl->calls_eh_return);
}




/* The allocframe instruction takes an unsigned,
   double word aligned, 14-bit immediate */
#define MAX_ALLOCFRAME_IMMED ((1U << 14) - 8)
/* The add instruction takes a signed 16-bit immediate */
#define MIN_ADD_IMMED        (-(1 << 15))
#define MAX_ADD_IMMED        ( (1 << 15) - 1)
/* The mem* instructions take a signed 11-bit immediate scaled by access size */
#define MAX_MEMW_OFFSET      ( (1 << 12) - 4)
#define MAX_MEMD_OFFSET      ( (1 << 13) - 8)

#define HEXAGON_BIGGEST_ALIGN(SIZE) \
  (((SIZE) + BIGGEST_ALIGNMENT / 8 - 1) & ~(BIGGEST_ALIGNMENT / 8 - 1))

/* Helper function for hexagon_frame_info

   Make all of the decisions about how to generate the prologue and epilogue. */

static void
hexagon_make_prologue_epilogue_decisions(struct hexagon_frame_info *info)
{
  static struct {
    enum insn_code prologue_function;
    unsigned int num_function_saved_pairs;
    enum insn_code epilogue_function;
    unsigned int num_function_restored_pairs;
    enum insn_code sibcall_epilogue_function;
    unsigned int num_sibcall_function_restored_pairs;
  }
    prologue_epilogue_functions_abi1[] =
      {
        {
          CODE_FOR_nothing, 0,
          CODE_FOR_deallocframe_function, 0,
          CODE_FOR_nothing, 0
        },
        {
          CODE_FOR_nothing, 0,
          CODE_FOR_restore_r24_through_r25_and_deallocframe, 1,
          CODE_FOR_restore_r24_through_r25_and_deallocframe_before_sibcall, 1
        },
        {
          CODE_FOR_save_r24_through_r27, 2,
          CODE_FOR_restore_r24_through_r27_and_deallocframe, 2,
          CODE_FOR_restore_r24_through_r27_and_deallocframe_before_sibcall, 2
        }
      },
    prologue_epilogue_functions_abi2[] =
      {
        {
          CODE_FOR_nothing, 0,
          CODE_FOR_deallocframe_function, 0,
          CODE_FOR_nothing, 0
        },
        {
          CODE_FOR_nothing, 0,
          CODE_FOR_restore_r16_through_r17_and_deallocframe, 1,
          CODE_FOR_restore_r16_through_r17_and_deallocframe_before_sibcall, 1
        },
        {
          CODE_FOR_save_r16_through_r19, 2,
          CODE_FOR_restore_r16_through_r19_and_deallocframe, 2,
          CODE_FOR_restore_r16_through_r19_and_deallocframe_before_sibcall, 2
        },
        {
          CODE_FOR_save_r16_through_r21, 3,
          CODE_FOR_restore_r16_through_r21_and_deallocframe, 3,
          CODE_FOR_restore_r16_through_r21_and_deallocframe_before_sibcall, 3
        },
        {
          CODE_FOR_save_r16_through_r23, 4,
          CODE_FOR_restore_r16_through_r23_and_deallocframe, 4,
          CODE_FOR_restore_r16_through_r23_and_deallocframe_before_sibcall, 4
        },
        {
          CODE_FOR_save_r16_through_r25, 5,
          CODE_FOR_restore_r16_through_r25_and_deallocframe, 5,
          CODE_FOR_restore_r16_through_r25_and_deallocframe_before_sibcall, 5
        },
        {
          CODE_FOR_save_r16_through_r27, 6,
          CODE_FOR_restore_r16_through_r27_and_deallocframe, 6,
          CODE_FOR_restore_r16_through_r27_and_deallocframe_before_sibcall, 6
        }
      },
    *prologue_epilogue_functions;

  static const enum insn_code
    allocframe_insn[] = {
      CODE_FOR_allocframe,
      CODE_FOR_allocframe_and_save_r16,
      CODE_FOR_allocframe_and_save_r16_and_r17
    },
    allocate_stack_insn[] = {
      CODE_FOR_increment_stack_pointer,
      CODE_FOR_allocate_stack_and_save_r16,
      CODE_FOR_allocate_stack_and_save_r16_and_r17,
      CODE_FOR_allocate_stack_and_save_r16_through_r18,
      CODE_FOR_allocate_stack_and_save_r16_through_r19
    };

  bool use_common_functions;
  unsigned int max_function_saved_pairs = 0;
  unsigned int first_callee_save_regno = 0;
  unsigned int num_regs_to_save_while_allocating = 0;
  unsigned int regno;
  unsigned int i = 0;
  unsigned int j;

  /* Select the set of prologue and epilogue functions for the target ABI. */
  if(hexagon_abi == HEXAGON_ABI_2){
    prologue_epilogue_functions = prologue_epilogue_functions_abi2;
    max_function_saved_pairs = ARRAY_SIZE (prologue_epilogue_functions_abi2)
                               - 1;
    first_callee_save_regno = 16;
  }
  else {
    prologue_epilogue_functions = prologue_epilogue_functions_abi1;
    max_function_saved_pairs = ARRAY_SIZE (prologue_epilogue_functions_abi1)
                               - 1;
    first_callee_save_regno = 24;
  }

  /* For V4, don't call the __deallocframe function, since we have the
     dealloc_return instruction. */
  if(TARGET_V4_FEATURES){
    prologue_epilogue_functions[0].epilogue_function
      = CODE_FOR_nothing;
  }
  else {
    prologue_epilogue_functions[0].epilogue_function
      = CODE_FOR_deallocframe_function;
  }

  /* Can we omit the allocframe and deallocframe instructions? */
  if(!info->use_allocframe){
    info->allocframe_size = 0;
    info->sp_adjustment = info->frame_size;
    info->base_reg = stack_pointer_rtx;
    info->offset = info->frame_size;
  }
  else {
    /* Can we allocate the entire stack frame with one allocframe
       instruction? */
    if(info->frame_size <= MAX_ALLOCFRAME_IMMED){
      info->allocframe_size = info->frame_size;
      info->sp_adjustment = 0;
    }
    else {
      info->allocframe_size = MAX_ALLOCFRAME_IMMED;
      info->sp_adjustment = info->frame_size - MAX_ALLOCFRAME_IMMED;
    }
    /* Use SP as the base if the offset would be small, making the loads and
       stores candidates for duplexes. */
    if(info->frame_size <= 256){
      info->base_reg = stack_pointer_rtx;
      info->offset = info->frame_size;
    }
    else {
      info->base_reg = hard_frame_pointer_rtx;
      info->offset = 0;
    }
  }

  use_common_functions = (optimize_size || optimize == 2)
                         && info->use_allocframe && !crtl->calls_eh_return;

  /* If we are using a function to save or restore callee-save registers or we
     are forming packets, then maximize the number of registers saved as pairs,
     since the common prologue and epilogue functions only save registers as
     pairs and doubleword store subinstructions have larger offsets than word
     store subinstructions. */
  if((use_common_functions || TARGET_PACKETS)
     && info->num_saved_singles % 2 == 1){

    /* Count the number of contiguous callee-save register pairs being saved. */
    for(i = 0, regno = first_callee_save_regno;
        i < info->num_saved_pairs && info->saved_pairs[i] == regno;
        i++, regno += 2);

    /* If the first single callee-save register is part of the next pair that
       could be saved, then remove it from the list of single callee-save
       registers and insert it into the list of paired callee-save
       registers. */
    if((   info->saved_singles[0] == regno
        || info->saved_singles[0] == regno + 1)
       && !call_used_regs[regno]
       && !call_used_regs[regno + 1]){

      for(j = 0; j < info->num_saved_singles - 1; j++){
        info->saved_singles[j] = info->saved_singles[j + 1];
      }
      for(j = info->num_saved_pairs; j > i; j--){
        info->saved_pairs[j] = info->saved_pairs[j - 1];
      }
      info->saved_pairs[i] = regno;
      info->num_saved_pairs++;
      info->num_saved_singles--;

      /* The callee-save registers being saved must still fit in the space
         allocated. */
      gcc_assert(info->reg_size >= 2 * UNITS_PER_WORD
                                     * info->num_saved_pairs
                                   + UNITS_PER_WORD
                                     * info->num_saved_singles);
    }
  }

  info->prologue_function = CODE_FOR_nothing;
  info->epilogue_function = CODE_FOR_nothing;
  info->sibcall_epilogue_function = CODE_FOR_nothing;

  /* Determine whether we can save code size by using functions to implement
     common prologue or epilogue sequences. */
  if(use_common_functions){

    /* Count the number of callee-save register pairs that can be saved or
       restored by function calls in the prologue and epilogue. */
    for(i = 0, regno = first_callee_save_regno;
        i < info->num_saved_pairs && info->saved_pairs[i] == regno;
        i++, regno += 2);
    if(i > max_function_saved_pairs){
      i = max_function_saved_pairs;
    }

    /* At -O2, use the common prologe and epilogue functions only if they save
       and restore 3 or more pairs of callee-save registers. */
    if(optimize_size || i >= 3){
      #define SET_PROLOGUE_EPILOGUE_FUNCTION_INFO(FIELD) \
        info->FIELD = prologue_epilogue_functions[i].FIELD
      SET_PROLOGUE_EPILOGUE_FUNCTION_INFO (prologue_function);
      SET_PROLOGUE_EPILOGUE_FUNCTION_INFO (num_function_saved_pairs);
      SET_PROLOGUE_EPILOGUE_FUNCTION_INFO (epilogue_function);
      SET_PROLOGUE_EPILOGUE_FUNCTION_INFO (num_function_restored_pairs);
      SET_PROLOGUE_EPILOGUE_FUNCTION_INFO (sibcall_epilogue_function);
      SET_PROLOGUE_EPILOGUE_FUNCTION_INFO (num_sibcall_function_restored_pairs);
    }
    info->num_specially_saved_pairs = info->num_function_saved_pairs;
  }

  info->allocframe_insn = CODE_FOR_allocframe;
  info->allocate_stack_insn = CODE_FOR_increment_stack_pointer;

  /* If possible, save one or more callee-save registers while allocating
     stack. */
  if(TARGET_PACKETS
     && (info->use_allocframe || info->sp_adjustment != 0)
     && info->num_function_saved_pairs == 0){

    if(TARGET_V4_FEATURES && !info->use_allocframe){
      switch(info->num_saved_pairs){
        case 0:
          if(info->num_saved_singles == 1 && info->saved_singles[0] == 16){
            num_regs_to_save_while_allocating = 1;
          }
          break;
        case 1:
          if(info->saved_pairs[0] == 16){
            if(info->num_saved_singles == 1 && info->saved_singles[0] == 18){
              num_regs_to_save_while_allocating = 3;
            }
            else {
              num_regs_to_save_while_allocating = 2;
            }
          }
          break;
        default:
          if(info->saved_pairs[0] == 16){
            if(info->saved_pairs[1] == 18){
              num_regs_to_save_while_allocating = 4;
            }
            else {
              num_regs_to_save_while_allocating = 2;
            }
          }
          break;
      }
    }
    else if(TARGET_V4_FEATURES || !info->use_allocframe){
      if(info->num_saved_pairs == 0){
        if(info->num_saved_singles == 1 && info->saved_singles[0] == 16){
          num_regs_to_save_while_allocating = 1;
        }
      }
      else if(info->saved_pairs[0] == 16){
        num_regs_to_save_while_allocating = 2;
      }
    }

    if(info->use_allocframe){
      info->allocframe_insn
        = allocframe_insn[num_regs_to_save_while_allocating];
    }
    else {
      info->allocate_stack_insn
        = allocate_stack_insn[num_regs_to_save_while_allocating];
    }
    info->num_specially_saved_pairs = num_regs_to_save_while_allocating / 2;
    info->num_specially_saved_singles = num_regs_to_save_while_allocating % 2;
  }
}




/* Fills in the frame info in the frame_info structure
   and returns a pointer to that structure */

static struct hexagon_frame_info *
hexagon_frame_info(void)
{
  struct hexagon_frame_info *info;
  unsigned int regno;

  info = &cfun->machine->frame_info;

  if(info->computed){
    return info;
  }

  /* Space for outgoing arguments */
  info->args_size = HEXAGON_BIGGEST_ALIGN (crtl->outgoing_args_size);

  /* Space for local variables, temporaries, and spills */
  info->var_size = HEXAGON_BIGGEST_ALIGN (get_frame_size());

  /* Space needed for callee-save registers */
  info->num_saved_pairs = 0;
  info->num_saved_singles = 0;
  for(regno = 0; regno < FIRST_PSEUDO_REGISTER; regno += 2){
    if(hexagon_save_register_p(regno)){
      if(hexagon_save_register_p(regno + 1)){
        info->saved_pairs[info->num_saved_pairs++] = regno;
      }
      else {
        info->saved_singles[info->num_saved_singles++] = regno;
      }
    }
    else if(hexagon_save_register_p(regno + 1)){
      info->saved_singles[info->num_saved_singles++] = regno + 1;
    }
  }
  info->reg_size = 2 * UNITS_PER_WORD * info->num_saved_pairs
                   + UNITS_PER_WORD * info->num_saved_singles;
  info->reg_size = HEXAGON_BIGGEST_ALIGN (info->reg_size);

  info->frame_size = info->args_size + info->var_size + info->reg_size;


  /* We omit the allocframe/deallocframe instructions in leaf functions when
     possible. */
  if(optimize
     && current_function_is_leaf
     && !frame_pointer_needed
     && !cfun->machine->calls_builtin_return_address
     && !crtl->calls_eh_return             
     && !crtl->profile            
     && !df_regs_ever_live_p(HARD_FRAME_POINTER_REGNUM)
     && !df_regs_ever_live_p(LINK_REGNUM)
     /* If the callee-save register area of the stack frame would be out of
        range of SP using a base+offset store, then use the allocframe and
        deallocframe instructions so the callee-save register area can be
        addressed via FP. */
     && !((info->num_saved_pairs || info->num_saved_singles)
          && info->frame_size - (info->num_saved_pairs
                                 ? 2 * UNITS_PER_WORD : UNITS_PER_WORD)
             > (info->num_saved_singles
                ? MAX_MEMW_OFFSET : MAX_MEMD_OFFSET))
     /* If the epilogue is more than a return instruction, then we can save
        code size by using one of the common epilogue functions, which require
        the frame pointer to point to the current frame. */
     /* ??? unless all function exits are tail calls and no callee-save
        registers are allocated. */
     && !(optimize_size && info->frame_size != 0)){
    info->lrfp_size = 0;
  }
  else {
    info->lrfp_size = 2 * UNITS_PER_WORD;
  }
  info->use_allocframe = info->lrfp_size != 0;

  info->total_size = info->frame_size + info->lrfp_size;

  if(reload_completed){
    hexagon_make_prologue_epilogue_decisions(info);
  }

  info->computed = reload_completed != 0;

  gcc_assert(info->frame_size % 8 == 0);

  return info;
}




/* Implements macro INITIAL_ELIMINATION_OFFSET

   Returns the number of bytes offset between FROM_REG and TO_REG
   for the current function. */

HOST_WIDE_INT
hexagon_initial_elimination_offset(int from_reg, int to_reg)
{
  struct hexagon_frame_info *frame;

  frame = hexagon_frame_info();

  if(      from_reg == ARG_POINTER_REGNUM
          && to_reg == STACK_POINTER_REGNUM){
    return frame->total_size;
  }
  else if( from_reg == FRAME_POINTER_REGNUM
          && to_reg == STACK_POINTER_REGNUM){
    return frame->args_size + frame->var_size;
  }
  else if( from_reg == HARD_FRAME_POINTER_REGNUM
          && to_reg == STACK_POINTER_REGNUM){
    return frame->frame_size;
  }
  else if( from_reg == ARG_POINTER_REGNUM
          && to_reg == HARD_FRAME_POINTER_REGNUM){
    return frame->lrfp_size;
  }
  else if( from_reg == FRAME_POINTER_REGNUM
          && to_reg == HARD_FRAME_POINTER_REGNUM){
    return -(frame->reg_size);
  }

  return 0;
}




/*----------------------------
Passing Arguments in Registers
----------------------------*/

/* Implements macro FUNCTION_ARG

   Determine whether a function argument is passed in a register,
   and if so, which register. */

rtx
hexagon_function_arg(
  CUMULATIVE_ARGS cum,
  enum machine_mode mode,
  tree type,
  int named
)
{
  int size;

  if(named == 0){
    return NULL_RTX;
  }

  if(hexagon_must_pass_in_stack(mode, type)){
    return NULL_RTX;
  }

  /* Check for even/odd pairs when size > 32 bits */
  if(type && mode == BLKmode){
    size = int_size_in_bytes(type);
  }
  else {
    size = GET_MODE_SIZE (mode);
  }

  if(size > UNITS_PER_WORD){
    /* If not an even register number, bump the counter */
    if(cum & 1){
      cum++;
    }
  }

  if(cum >= HEXAGON_NUM_ARG_REGS){
    return NULL_RTX;
  }

  return gen_rtx_REG (mode, FIRST_ARG_REGNUM + cum);
}




/* Implements hook TARGET_MUST_PASS_IN_STACK

   True if we do not know how to pass TYPE solely in registers.
   We cannot do so in the following cases:

   - if the type has variable size
   - if the type is marked as addressable (it is required to be constructed into
     the stack)
   - if the type is > 8 bytes. */

static bool
hexagon_must_pass_in_stack(enum machine_mode mode ATTRIBUTE_UNUSED, const_tree type)
{
  return type && TYPE_SIZE (type)
         && (TREE_CODE (TYPE_SIZE (type)) != INTEGER_CST
             || TREE_ADDRESSABLE (type)
             || int_size_in_bytes(type) > 8);
}




/* Implements macro FUNCTION_ARG_ADVANCE

   Advance the cumulative arg pointer past the current argument. */

int
hexagon_function_arg_advance(
  CUMULATIVE_ARGS cum,
  enum machine_mode mode,
  tree type,
  int named
)
{
  int size;

  if(named == 0){
    return cum;
  }

  if(hexagon_must_pass_in_stack(mode, type)){
    return cum;
  }

  if(type && mode == BLKmode){
    size = int_size_in_bytes(type);
  }
  else {
    size = GET_MODE_SIZE (mode);
  }

  /* Check for even/odd pairs when size > 32 bits */
  if(size > UNITS_PER_WORD){
    /* If not an even register number, bump the counter */
    if(cum & 1){
      cum++;
    }
  }

  return cum + (size + UNITS_PER_WORD - 1) / UNITS_PER_WORD;
}




/* Implements hook TARGET_VECTOR_MODE_SUPPORTED_P */

static bool
hexagon_vector_mode_supported_p(enum machine_mode mode)
{
  return    mode == V2SImode
         || mode == V4HImode
         || mode == V8QImode
         || mode == V2HImode
         || mode == V4QImode;
}




/*-------------------------------------
How Scalar Function Values Are Returned
-------------------------------------*/

/* Implements hook TARGET_FUNCTION_VALUE */

static rtx
hexagon_function_value(
  const_tree ret_type,
  const_tree fn_decl_or_type ATTRIBUTE_UNUSED,
  bool outgoing ATTRIBUTE_UNUSED
)
{
  enum machine_mode mode;
  int unsignedp ATTRIBUTE_UNUSED;

  mode = TYPE_MODE (ret_type);
  mode = promote_mode(ret_type, mode, &unsignedp);
  return gen_rtx_REG (mode, RETURN_VALUE_REGNUM);
}




/*---------------------------
How Large Values Are Returned
---------------------------*/

/* Implements hook TARGET_RETURN_IN_MEMORY

   Return true if function return value returned in memory.
   Return false if it is in a register. */

static bool
hexagon_return_in_memory(const_tree type, const_tree fntype ATTRIBUTE_UNUSED)
{
  enum machine_mode mode;
  HOST_WIDE_INT byte_size;

  mode = TYPE_MODE (type);
  byte_size = GET_MODE_SIZE (mode);
  if(mode == BLKmode){
    byte_size = int_size_in_bytes(type);
  }

  return !IN_RANGE (byte_size, 0, 8);
}




/*---------------------
Function Entry and Exit
---------------------*/

/* Implements hook TARGET_ASM_FUNCTION_PROLOGUE */

static void
hexagon_asm_function_prologue(
  FILE *file,
  HOST_WIDE_INT size ATTRIBUTE_UNUSED
)
{
  struct hexagon_frame_info *frame;
  frame = hexagon_frame_info();
  fprintf(file, "\t%s saved LR + FP regs size (bytes) = "
                HOST_WIDE_INT_PRINT_UNSIGNED "\n"
                "\t%s callee saved regs size (bytes) = "
                HOST_WIDE_INT_PRINT_UNSIGNED "\n"
                "\t%s local vars size (bytes) = "
                HOST_WIDE_INT_PRINT_UNSIGNED "\n"
                "\t%s fixed args size (bytes) = "
                HOST_WIDE_INT_PRINT_UNSIGNED "\n",
                ASM_COMMENT_START, frame->lrfp_size,
                ASM_COMMENT_START, frame->reg_size,
                ASM_COMMENT_START, frame->var_size,
                ASM_COMMENT_START, frame->args_size
         );

  hexagon_final_pack_insns();

  hexagon_compute_dwarf_frame_information();
}




/*-------------------
Permitting tail calls
-------------------*/

/* Implements hook TARGET_FUNCTION_OK_FOR_SIBCALL */

static bool
hexagon_function_ok_for_sibcall(tree decl, tree exp ATTRIBUTE_UNUSED)
{
  if(TARGET_LONG_CALLS){
    return false;
  }
  return decl != NULL;
}




/*--------------------------------
Implicit Calls to Library Routines
--------------------------------*/

#if HEXAGON_DINKUMWARE
/* Implements hook TARGET_INIT_LIBFUNCS */

static void
hexagon_init_libfuncs(void)
{
  set_optab_libfunc(sdiv_optab, SImode, "__qdsp_divsi3");
  set_optab_libfunc(sdiv_optab, DImode, "__qdsp_divdi3");

  set_optab_libfunc(udiv_optab, SImode, "__qdsp_udivsi3");
  set_optab_libfunc(udiv_optab, DImode, "__qdsp_udivdi3");

  set_optab_libfunc(smod_optab, SImode, "__qdsp_modsi3");
  set_optab_libfunc(smod_optab, DImode, "__qdsp_moddi3");

  set_optab_libfunc(umod_optab, SImode, "__qdsp_umodsi3");
  set_optab_libfunc(umod_optab, DImode, "__qdsp_umoddi3");

  set_optab_libfunc(sdivmod_optab, SImode, "__qdsp_divmodsi4");
  set_optab_libfunc(sdivmod_optab, DImode, "__qdsp_divmoddi4");

  set_optab_libfunc(udivmod_optab, SImode, "__qdsp_udivmodsi4");
  set_optab_libfunc(udivmod_optab, DImode, "__qdsp_udivmoddi4");

  if (flag_unsafe_math_optimizations)
    {
      set_optab_libfunc(add_optab, DFmode, "__qdsp_fast_adddf3");
    }
  else 
    {
      set_optab_libfunc(add_optab, DFmode, "__qdsp_adddf3");
    }

  set_optab_libfunc(add_optab, SFmode, "__qdsp_addsf3");

  if (flag_unsafe_math_optimizations)
    {
      set_optab_libfunc(sub_optab, DFmode, "__qdsp_fast_subdf3");
    }
  else
    {
      set_optab_libfunc(sub_optab, DFmode, "__qdsp_subdf3");
    }

  set_optab_libfunc(sub_optab, SFmode, "__qdsp_subsf3");

  if (flag_unsafe_math_optimizations)
    {
      set_optab_libfunc(smul_optab, DFmode, "__qdsp_fast_muldf3");
    }
  else
    {
      set_optab_libfunc(smul_optab, DFmode, "__qdsp_muldf3");
    }

  set_optab_libfunc(smul_optab, SFmode, "__qdsp_mulsf3");
    
  if (flag_unsafe_math_optimizations)
    {
      set_optab_libfunc(sdiv_optab, DFmode, "__qdsp_fast_divdf3");
    }
  else
    {
      set_optab_libfunc(sdiv_optab, DFmode, "__qdsp_divdf3");
    }

  set_optab_libfunc(sdiv_optab, SFmode, "__qdsp_divsf3");
  
  if (flag_unsafe_math_optimizations)
    {
      set_optab_libfunc(neg_optab, DFmode, "__qdsp_fast_negdf2");
    }
  else
    {
      set_optab_libfunc(neg_optab, DFmode, "__qdsp_negdf2");
    }

  set_optab_libfunc(neg_optab, SFmode, "__qdsp_negsf3");

  set_optab_libfunc(cmp_optab, SFmode, "__qdsp_cmpsf2");
  set_optab_libfunc(cmp_optab, DFmode, "__qdsp_cmpdf2");

  set_optab_libfunc(unord_optab, SFmode, "__qdsp_unordsf2");
  set_optab_libfunc(unord_optab, DFmode, "__qdsp_unorddf2");

  set_optab_libfunc(eq_optab, SFmode, "__qdsp_eqsf2");
  set_optab_libfunc(eq_optab, DFmode, "__qdsp_eqdf2");

  set_optab_libfunc(ne_optab, SFmode, "__qdsp_nesf2");
  set_optab_libfunc(ne_optab, DFmode, "__qdsp_nedf2");

  set_optab_libfunc(ge_optab, SFmode, "__qdsp_gesf2");
  set_optab_libfunc(ge_optab, DFmode, "__qdsp_gedf2");

  if (flag_unsafe_math_optimizations)
    {
      set_optab_libfunc(lt_optab, DFmode, "__qdsp_fast_ltdf2");
    }
  else
    {
      set_optab_libfunc(lt_optab, DFmode, "__qdsp_ltdf2");
    }

  set_optab_libfunc(lt_optab, SFmode, "__qdsp_ltsf2");

  set_optab_libfunc(le_optab, SFmode, "__qdsp_lesf2");
  set_optab_libfunc(le_optab, DFmode, "__qdsp_ledf2");

  if (flag_unsafe_math_optimizations)
    {
      set_optab_libfunc(gt_optab, DFmode, "__qdsp_fast_gtdf2");
    }
  else 
    {
      set_optab_libfunc(gt_optab, DFmode, "__qdsp_gtdf2");
    }

  set_optab_libfunc(gt_optab, SFmode, "__qdsp_gtsf2");

  set_conv_libfunc(sext_optab, DFmode, SFmode, "__qdsp_extendsfdf2");
  set_conv_libfunc(trunc_optab, SFmode, DFmode, "__qdsp_truncdfsf2");

  set_conv_libfunc(sfix_optab, SImode, SFmode, "__qdsp_fixsfsi");
  set_conv_libfunc(sfix_optab, DImode, SFmode, "__qdsp_fixsfdi");

  set_conv_libfunc(sfix_optab, SImode, DFmode, "__qdsp_fixdfsi");
  set_conv_libfunc(sfix_optab, DImode, DFmode, "__qdsp_fixdfdi");

  set_conv_libfunc(ufix_optab, SImode, SFmode, "__qdsp_fixunssfsi");
  set_conv_libfunc(ufix_optab, DImode, SFmode, "__qdsp_fixunssfdi");

  set_conv_libfunc(ufix_optab, SImode, DFmode, "__qdsp_fixunsdfsi");
  set_conv_libfunc(ufix_optab, DImode, DFmode, "__qdsp_fixunsdfdi");

  set_conv_libfunc(sfloat_optab, SFmode, SImode, "__qdsp_floatsisf");
  set_conv_libfunc(sfloat_optab, SFmode, DImode, "__qdsp_floatdisf");

  set_conv_libfunc(sfloat_optab, DFmode, SImode, "__qdsp_floatsidf");
  set_conv_libfunc(sfloat_optab, DFmode, DImode, "__qdsp_floatdidf");

  if (flag_unsafe_math_optimizations)
    {
      set_optab_libfunc(sqrt_optab, DFmode, "__qdsp_fast_sqrt_df");
    }

  set_conv_libfunc(ufloat_optab, SFmode, SImode, "__qdsp_floatunsisf");
  set_conv_libfunc(ufloat_optab, SFmode, DImode, "__qdsp_floatundisf");

  set_conv_libfunc(ufloat_optab, DFmode, SImode, "__qdsp_floatunsidf");
  set_conv_libfunc(ufloat_optab, DFmode, DImode, "__qdsp_floatundidf");
}
#endif /* HEXAGON_DINKUMWARE */




/*--------------
Addressing Modes
--------------*/

/* Helper for hexagon_legitimate_address_p

   Determine if the constant fits in the encoding
     - Check the range based on the number of bits and signedness
     - Check that the "scaling" bits are zero */

static bool
hexagon_legit_addr_const_p(
  HOST_WIDE_INT value,
  enum machine_mode mode,
  int num_bits
)
{
  int size;
  HOST_WIDE_INT min, max, scaling_bits;

  size = GET_MODE_SIZE (mode);

  if(num_bits < 0){
    num_bits = -num_bits;
    min = -(1 << (num_bits - 1)) * size;
    max = ((1 << (num_bits - 1)) - 1) * size;
  }
  else {
    min = 0;
    max = ((1 << num_bits) - 1) * size;
  }
  scaling_bits = value & (size - 1);

  return min <= value && value <= max && scaling_bits == 0;
}




/* Helper function for hexagon_legitimate_address_p */

static bool
hexagon_reg_ok_for_base_p(rtx x, bool reg_ok_strict_p)
{
  if(reg_ok_strict_p){
    return G_REG_P (x) || REGNO (x) == FRAME_POINTER_REGNUM
                       || REGNO (x) == ARG_POINTER_REGNUM;
  }
  else {
    return G_REG_P (x) || REGNO (x) == FRAME_POINTER_REGNUM
                       || REGNO (x) == ARG_POINTER_REGNUM
                       || REGNO (x) >= FIRST_PSEUDO_REGISTER;
  }
}




/* Helper function for hexagon_legitimate_address_p */

static bool
hexagon_reg_ok_for_index_p(rtx x, bool reg_ok_strict_p)
{
  if(reg_ok_strict_p){
    return G_REG_P (x);
  }
  else {
    return G_REG_P (x) || REGNO (x) >= FIRST_PSEUDO_REGISTER;
  }
}




/* Used by macro GO_IF_LEGITIMATE_ADDRESS

   The CONSTRAINT argument is the constraint string excluding any initial 'A'.
   The different constraints correspond to differnt types of instuctions, each
   of which can utilize a different set of addressing modes.  The possible
   values for the constraint string are:

   m       basic loads and stores, allowing an immediate extender
   dm3     stores and loads for sub-instructions with an #u3 offset
   dm4     stores and loads for sub-instructions with an #u4 offset
   dmsp5   stores and loads for sub-instructions from SP with an #u5 offset
   dmsp6   stores and loads for sub-instructions from SP with an #s6 offset
   noext   basic loads and stores
   cond    conditional loads and stores
   econd   conditional loads and stores, allowing an immediate extender
   si      store immediate
   csi     conditional store immediate
   memop   load-op-stores
   ememop  load-op-stores, allowing an immediate extender */

bool
hexagon_legitimate_address_p(
  enum machine_mode mode,
  rtx x,
  bool reg_ok_strict_p,
  const char *constraint
)
{
  rtx xop0 = NULL_RTX;
  rtx xop1 = NULL_RTX;
  rtx xop1op0 = NULL_RTX;
  rtx xop1op1 = NULL_RTX;
  bool allow_extension = false;
  bool allow_gp = false;
  bool allow_absolute = false;
  bool allow_immediate_base = false;
  bool allow_base_plus_index = false;
  bool allow_post_inc = false;
  int offset_bits = 6;

  if(TARGET_V4_FEATURES
     && (crtl->combine_in_progress || crtl->combine_completed)
     && (   !strcmp(constraint, "m")
         || !strcmp(constraint, "econd")
         || !strcmp(constraint, "ememop"))){
    allow_extension = true;
  }

  if (TARGET_V4_FEATURES && !strcmp (constraint, "dmsp5")) {
    /* For memw(r29 + #u5:2) and memd(r29+#u5:3) */
    if (GET_CODE (x) == PLUS) {
      xop0 = XEXP (x, 0);
      xop1 = XEXP (x, 1);
      if (REG_P (xop0)
          && REGNO (xop0) == STACK_POINTER_REGNUM
          && GET_CODE (xop1) == CONST_INT) {
        offset_bits = 5;
      }
    }
    else if (REG_P(x) && (REGNO (x) == STACK_POINTER_REGNUM)) {
        offset_bits = 5;
    }
    else {
      return false;
    }
  }
  else if (TARGET_V4_FEATURES && !strcmp (constraint, "dm4")) {
    /* For memw(Rs+#u4:2) */
    offset_bits = 4;
  }
  else if (TARGET_V4_FEATURES && !strcmp (constraint, "dm3")) {
    /* For Rd = memb(Rs+#u3:0) */
    offset_bits = 3;
  }
  else if (TARGET_V4_FEATURES && !strcmp (constraint, "dmsp6")) {
    if (GET_CODE (x) == PLUS) {
      xop0 = XEXP (x, 0);
      xop1 = XEXP (x, 1);
      if (REG_P (xop0)
          && REGNO (xop0) == STACK_POINTER_REGNUM 
          && GET_CODE (xop1) == CONST_INT) {
        /* For memd(r29+#s6:3) */
        offset_bits = -6;
      }
    }
    /* For memd(r29) */
    else if (REG_P(x) && (REGNO (x) == STACK_POINTER_REGNUM)) {
      offset_bits = -6;
    }
    else {
      return false;
    }
  }
  else if(!strcmp(constraint, "m") || !strcmp(constraint, "noext")){
    if(TARGET_V4_FEATURES){
      allow_absolute = true;
      allow_immediate_base = true;
      allow_base_plus_index = true;
    }
    allow_gp = true;
    allow_post_inc = true;
    offset_bits = -11;
  }
  else if(!strcmp(constraint, "cond") || !strcmp(constraint, "econd")){
    if(TARGET_V4_FEATURES){
      allow_absolute = true;
      allow_base_plus_index = true;
    }
    allow_post_inc = true;
  }
  else if(!TARGET_V4_FEATURES){
    return false;
  }
  else if(!strcmp(constraint, "si")){
  }
  else if(!strcmp(constraint, "csi")){
  }
  else if(!strcmp(constraint, "memop") || !strcmp(constraint, "ememop")){
    if(!TARGET_MEMOPS){
      return false;
    }
  }
  else {
    gcc_unreachable();
  }

  if(!TARGET_BASE_PLUS_INDEX){
    allow_base_plus_index = false;
  }

  /* Extract operands and canonicalize commutitive operators. */
  if(GET_CODE (x) == PLUS || GET_CODE (x) == POST_MODIFY){
    xop0 = XEXP (x, 0);
    xop1 = XEXP (x, 1);
    if(GET_CODE (x) == PLUS && GET_CODE (x) != POST_MODIFY
       && ((REG_P (xop1) || CONSTANT_P (xop1)) && !REG_P (xop0))){
      xop0 = XEXP (x, 1);
      xop1 = XEXP (x, 0);
    }
    if(   GET_CODE (xop1) == PLUS
       || GET_CODE (xop1) == MULT
       || GET_CODE (xop1) == ASHIFT){
      xop1op0 = XEXP (xop1, 0);
      xop1op1 = XEXP (xop1, 1);
      if(GET_CODE (xop1) != ASHIFT && !REG_P (xop1op0)){
        xop1op0 = XEXP (xop1, 1);
        xop1op1 = XEXP (xop1, 0);
      }
    }
  }
  else if(GET_CODE (x) == POST_INC || GET_CODE (x) == POST_DEC){
    xop0 = XEXP (x, 0);
  }

  /* GP-relative address */
  if(allow_gp){
    if(sdata_symbolic_operand(x, Pmode)){
      return true;
    }
  }

  /* absolute address */
  if(allow_absolute && allow_extension && CONSTANT_P (x)){
    return true;
  }

  /* register-indirect address */
  if(REG_P (x)){
    return hexagon_reg_ok_for_base_p(x, reg_ok_strict_p);
  }

  /* We allow FP+offset addresses here because that is necessary for SP+offset
     addresses later.  Note that we don't check the range of the constant. */
  if(!reg_ok_strict_p
     && GET_CODE (x) == PLUS
     && REG_P (xop0)
     && REGNO (xop0) == FRAME_POINTER_REGNUM
     && GET_CODE (xop1) == CONST_INT){
    return true;
  }

  /* base+offset/index address */
  if(   GET_CODE (x) == PLUS
     && ((REG_P (xop0) && hexagon_reg_ok_for_base_p(xop0, reg_ok_strict_p))
         || (allow_immediate_base && allow_extension
             && CONSTANT_P (xop0) && !CONSTANT_P (xop1)))){
    rtx offset = xop1;
    rtx index = xop1op0;
    rtx scale = xop1op1;

    /* base+extended offset address */
    if(allow_extension && CONSTANT_P (offset)){
      if(GET_CODE (offset) == CONST_INT){
        return (INTVAL (offset) & (GET_MODE_SIZE (mode) - 1)) == 0;
      }
      return allow_immediate_base;
    }

    /* base+offset address */
    if(GET_CODE (offset) == CONST_INT){
      return hexagon_legit_addr_const_p(INTVAL (offset), mode, offset_bits);
    }

    /* base+index address */
    if(allow_base_plus_index){
      if(REG_P (offset)){
        return hexagon_reg_ok_for_base_p(offset, reg_ok_strict_p);
      }
      if(GET_CODE (offset) == MULT){
        return    REG_P (index)
               && hexagon_reg_ok_for_index_p(index, reg_ok_strict_p)
               && GET_CODE (scale) == CONST_INT
               && (   INTVAL (scale) == 1
                   || INTVAL (scale) == 2
                   || INTVAL (scale) == 4
                   || INTVAL (scale) == 8);
      }
      if(GET_CODE (offset) == ASHIFT){
        return    REG_P (index)
               && hexagon_reg_ok_for_index_p(index, reg_ok_strict_p)
               && GET_CODE (scale) == CONST_INT
               && IN_RANGE (INTVAL (scale), 0, 3);
      }
    }
  }

  if(allow_post_inc){
    /* post increment/decrement address with the increment/decrement equal to
       the access size */
    if(GET_CODE (x) == POST_INC || GET_CODE (x) == POST_DEC){
      return REG_P (xop0) && hexagon_reg_ok_for_base_p(xop0, reg_ok_strict_p);
    }

    /* post increment/decrement address */
    if(GET_CODE (x) == POST_MODIFY){
      return    REG_P (xop0)
             && hexagon_reg_ok_for_base_p(xop0, reg_ok_strict_p)
             && GET_CODE (xop1) == PLUS
             && REG_P (xop1op0)
             && REGNO (xop1op0) == REGNO (xop0)
             && GET_CODE (xop1op1) == CONST_INT
             && hexagon_legit_addr_const_p(INTVAL (xop1op1), mode, -4);
    }
  }

  return false;
}

/*                                           
 ---------------------------------------------
    Begin Position Independent Code Support  
 ---------------------------------------------
*/                                          

/* 
 *  Helper function for hexagon_legitimate_pic_operand_p()
 *  Return TRUE if X references a symbol  
 *  Simple proposition for now; can be expanded
 */
int
symbol_mentioned_p (rtx x)
{
  return (GET_CODE (x) == SYMBOL_REF);
}


/* 
 *  Helper function for hexagon_legitimate_pic_operand_p()
 *  Return TRUE if X references a label  
 *  Simple proposition for now; can be expanded
 */
int
label_mentioned_p (rtx x)
{
  return (GET_CODE (x) == LABEL_REF);
}


/*
 * Implements macro LEGITIMATE_PIC_OPERAND_P
 */
bool
hexagon_legitimate_pic_operand_p(rtx operand) 
{
  /* Taken from the ARM code.  It recogonizes the case when a pic symbol
   * is used within an expression, which we disallow because the symbol
   * will not be generated with a @GOT/GOTOFF extension.
   */
  if (symbol_mentioned_p (operand) 
	 || (GET_CODE (operand) == CONST
	     && GET_CODE (XEXP (operand, 0)) == PLUS
	     && symbol_mentioned_p (XEXP (XEXP (operand, 0), 0)))) {
    return 0;
  }

  return (!(symbol_mentioned_p (operand)
	    || label_mentioned_p (operand)
	    || (GET_CODE (operand) == SYMBOL_REF
		&& CONSTANT_POOL_ADDRESS_P (operand)
		&& (symbol_mentioned_p (get_pool_constant (operand))
		    || label_mentioned_p (get_pool_constant (operand))))));
}


/*
 * Mark that the compiled function accesses the PIC register. This implies that
 * code must be added in the prologue to set up the PIC register
 */
void
require_pic_register (void)
{
  /* Set gcc global flag */
  crtl->uses_pic_offset_table = 1;
}


/*
  There must be a better way to do this. We need a register to use as a temporary
  while saving and restoring gp. We cannot create a new virtual register since
  the save and restore code is invoked after reload has finished. 
  The temporary register must be a caller-saved register and not an argument
  register
*/
#define NON_ARG_CALLER_SAVE_REGISTER_1 10

/*
 * Setup the pic register in the function prologue.  This function
 * assumes the pic option has been set.
 */
static void
hexagon_load_pic_register() {
  
  rtx dummy_pic, pic_reg, label, seq;
  
  /* Materialize GOT base for PIC */

  label = gen_label_rtx();    
  rtx temp_reg = gen_rtx_REG (SImode, NON_ARG_CALLER_SAVE_REGISTER_1);
  /* emit insn sequence for computing the GOT base */
  emit_insn(gen_compute_got_base(pic_offset_table_rtx, label));
  emit_insn(gen_pic_movsi_hi_gotoff(temp_reg, 
				    gen_rtx_LABEL_REF(SImode, label)));
  emit_insn(gen_pic_movsi_lo_gotoff(temp_reg, temp_reg,
				    gen_rtx_LABEL_REF(SImode, label)));
  emit_insn(gen_subsi3(pic_offset_table_rtx, pic_offset_table_rtx, temp_reg));
}

/*
 * Helper function for hexagon_legitimize_address() for PIC compilation
 * Make addresses conform to PIC mode
 */
rtx
legitimize_pic_address(rtx orig, enum machine_mode mode, rtx reg) 
{

  if (GET_CODE (orig) == SYMBOL_REF
      || GET_CODE (orig) == LABEL_REF)
    {
      rtx pic_ref, address, dummy_pic, add_reg;
      rtx insn;
      rtx temp_physical_reg;
 
      /* module_owns: set if this module owns the data (orig) */
      int module_owns = 0;
      int subregs = 0;

      /* Record that we generate a pic reference  */
      require_pic_register ();

      /* TODO: why do we need the following 2 if clauses? */
      if (reg == 0)
	{
	  gcc_assert (can_create_pseudo_p());
	  reg = gen_reg_rtx (Pmode);

	  subregs = 1;
	}

      if (subregs) 
	{
	  address = gen_reg_rtx (Pmode);
	}
      else
	{
	  address = reg;
	}


      /* 
       * Normalize the address to a PIC address via @GOT or @GOTOFF
       */

      /* Check if the module owns this data. The module always owns a label */
      module_owns = (GET_CODE (orig) == LABEL_REF) || SYMBOL_REF_LOCAL_P(orig);

      /* 1. Load GOT-relative address */
      if (module_owns) {
	/* rx.h = #HI(addr@GOTOFF); rx.l = #LO(addr@GOTOFF) */
	emit_insn (gen_pic_movsi_hi_gotoff(address, orig));
	emit_insn (gen_pic_movsi_lo_gotoff(address, address, orig));
	/* address = CONST32(#address@GOTOFF) */
      }
      else {
	if (flag_pic == 1) {
	  /* rx = #addr@GOT */
	  emit_insn (gen_pic_movsi(address, gen_rtx_CONST(SImode, orig)));
	} 
	else {
	  /* rx.h = #HI(addr@GOT); rx.l = #LO(addr@GOT) */
	  emit_insn(gen_pic_movsi_hi_got(address, orig));
	  emit_insn(gen_pic_movsi_lo_got(address, address, orig));
	  /* address = CONST32(#address@GOT) */
	}
      }

      /* 2. Add the absolute address of the GOT to the GOT-relative address */
      /* reg = add(address, pic_reg) */
      //      emit_insn(gen_addsi3(reg, pic_offset_table_rtx, address));
      if (module_owns) {
	/* If the module owns this data, then we are done. reg holds the
	   gotoff-adjusted address */
	pic_ref = gen_rtx_PLUS(Pmode, pic_offset_table_rtx, address);
      }
      else {
       	/* reg = memw(address) */
	// emit_move_insn(reg, gen_rtx_MEM(SImode, reg));
	pic_ref = gen_const_mem (Pmode, 
				 gen_rtx_PLUS (Pmode, pic_offset_table_rtx,
					       address));
      }
      insn = emit_move_insn (reg, pic_ref);
      set_unique_reg_note (insn, REG_EQUAL, orig);

      return reg;
    }
  else if (CONSTANT_P(orig)) 
    {
     /* Taken from arm code */
     if (GET_CODE (orig) == CONST)
       {  
         if (GET_CODE (XEXP (orig, 0)) == PLUS)
	   {
	     rtx base, offset;
	     base = legitimize_pic_address (XEXP (XEXP (orig, 0), 0), Pmode, reg);
	     offset = legitimize_pic_address (XEXP (XEXP (orig, 0), 1), Pmode,
					      base == reg ? 0 : reg);
	     return gen_rtx_PLUS (Pmode, base, offset);
	   }
       } 
    }

  return orig;
}


/*
 * Implements macro LEGITIMIZE_ADDRESS
 * Disabled for now. We may need to enable this
 */
rtx
hexagon_legitimize_address (rtx x, rtx old_x, enum machine_mode mode)
{

  if (flag_pic) 
    {
      rtx pic_x = legitimize_pic_address(old_x, mode, NULL_RTX);
      if (old_x != pic_x) 
	{
	  x = pic_x;
	}
    }
  return(x);
}


/*                                           
 ---------------------------------------------
    End Position Independent Code Support  
 ---------------------------------------------
*/                                          



/* Construct a unique section name based on the decl name and the
   categorization performed above.  Original in gcc/varasm.c  */
void
default_unique_section_2 (tree decl, int reloc)
{
  /* We only need to use .gnu.linkonce if we don't have COMDAT groups.  */
  bool one_only = DECL_ONE_ONLY (decl) && !HAVE_COMDAT_GROUP;
  const char *prefix, *name;
  size_t nlen, plen;
  char *string;

  switch (categorize_decl_for_section (decl, reloc))
    {
    case SECCAT_TEXT:
      prefix = one_only ? ".gnu.linkonce.t." : ".text.";
      break;
    case SECCAT_RODATA:
    case SECCAT_RODATA_MERGE_STR:
    case SECCAT_RODATA_MERGE_STR_INIT:
    case SECCAT_RODATA_MERGE_CONST:
      prefix = one_only ? ".gnu.linkonce.r." : ".rodata.";
      break;
    case SECCAT_SRODATA:
      prefix = one_only ? ".gnu.linkonce.s2." : ".sdata2.";
      break;
    case SECCAT_DATA:
      prefix = one_only ? ".gnu.linkonce.d." : ".data.";
      break;
    case SECCAT_DATA_REL:
      prefix = one_only ? ".gnu.linkonce.d.rel." : ".data.rel.";
      break;
    case SECCAT_DATA_REL_LOCAL:
      prefix = one_only ? ".gnu.linkonce.d.rel.local." : ".data.rel.local.";
      break;
    case SECCAT_DATA_REL_RO:
      prefix = one_only ? ".gnu.linkonce.d.rel.ro." : ".data.rel.ro.";
      break;
    case SECCAT_DATA_REL_RO_LOCAL:
      prefix = one_only ? ".gnu.linkonce.d.rel.ro.local."
	       : ".data.rel.ro.local.";
      break;
	case SECCAT_SDATA:
      if(TARGET_SECTION_SORTING){
        switch(smallest_accessable_entity_in_declaration(decl)){
           case 1: prefix = one_only ? ".gnu.linkonce.s.1." : ".sdata.1."; break;
           case 2: prefix = one_only ? ".gnu.linkonce.s.2." : ".sdata.2."; break;
           case 4: prefix = one_only ? ".gnu.linkonce.s.4." : ".sdata.4."; break;
           case 8: prefix = one_only ? ".gnu.linkonce.s.8." : ".sdata.8."; break;
           default:     // Dev warning. fprintf(stderr,"Warning. smallest_accessable_entity_in_declaration (%d)\n",smallest_accessable_entity_in_declaration(decl));
                prefix = one_only ? ".gnu.linkonce.s." : ".sdata.";
                break;
        }
      }
      else      prefix = one_only ? ".gnu.linkonce.s." : ".sdata.";
      break;
    case SECCAT_BSS:
      prefix = one_only ? ".gnu.linkonce.b." : ".bss.";
      break;
    case SECCAT_SBSS:
      if(TARGET_SECTION_SORTING){
        switch(smallest_accessable_entity_in_declaration(decl)){
           case 1: prefix = one_only ? ".gnu.linkonce.sb.1." : ".sbss.1."; break;
           case 2: prefix = one_only ? ".gnu.linkonce.sb.2." : ".sbss.2."; break;
           case 4: prefix = one_only ? ".gnu.linkonce.sb.4." : ".sbss.4."; break;
           case 8: prefix = one_only ? ".gnu.linkonce.sb.8." : ".sbss.8."; break;
           default:     // Dev warning. fprintf(stderr,"Warning. smallest_accessable_entity_in_declaration (%d)\n",smallest_accessable_entity_in_declaration(decl));
                prefix = one_only ? ".gnu.linkonce.sb." : ".sbss.";
                break;
        }
      }
      else      prefix = one_only ? ".gnu.linkonce.sb." : ".sbss.";
      break;
    case SECCAT_TDATA:
      prefix = one_only ? ".gnu.linkonce.td." : ".tdata.";
      break;
    case SECCAT_TBSS:
      prefix = one_only ? ".gnu.linkonce.tb." : ".tbss.";
      break;
    default:
      gcc_unreachable ();
    }
  plen = strlen (prefix);

  name = IDENTIFIER_POINTER (DECL_ASSEMBLER_NAME (decl));
  name = targetm.strip_name_encoding (name);
  nlen = strlen (name);

  string = (char *) alloca (nlen + plen + 1);
  memcpy (string, prefix, plen);
  memcpy (string + plen, name, nlen + 1);

  DECL_SECTION_NAME (decl) = build_string (nlen + plen, string);
}




static void
hexagon_unique_section (tree decl, int reloc)
{
  default_unique_section_2 (decl, reloc);
}




/* _LSY_ Loks for smallest addressable entity in
   a declaration, not overall declaration size. */  
unsigned HOST_WIDE_INT 
sdata_symbolic_operand_smallest_accessable_size(rtx op)
{
  unsigned HOST_WIDE_INT size = 16;
  tree t;

  switch(GET_CODE (op)){
    case CONST:
      op = XEXP (op, 0);
      if(!(GET_CODE (op) == PLUS
           && GET_CODE (XEXP (op, 0)) == SYMBOL_REF
           && GET_CODE (XEXP (op, 1)) == CONST_INT)){
        return size;
      }
      op = XEXP (op, 0);
      /* FALL THROUGH */
    case SYMBOL_REF:
      if(CONSTANT_POOL_ADDRESS_P (op)){
        size = GET_MODE_SIZE (get_pool_mode(op));
      }
      else {
        if(!SYMBOL_REF_SMALL_P (op))    return size;
        t = SYMBOL_REF_DECL (op);
	/* if we want to take overall declaration size
	   the following code will work just fine:
	   if(DECL_P (t))  t = DECL_SIZE_UNIT (t);
           else            t = TYPE_SIZE_UNIT (TREE_TYPE (t));
           if(t && host_integerp(t, 0)){
             size = tree_low_cst(t, 0);
             if(size < 0)  size = -1;
           }
 	*/ 
 	if(t)
          size = smallest_accessable_entity_in_declaration(t);
      }
    default:
      return size;
  }
}




static GTY(()) tree hexagon_builtin_mask_for_load;

/* Implements hook TARGET_VECTORIZE_BUILTIN_MASK_FOR_LOAD */

static tree
hexagon_vectorize_builtin_mask_for_load(void)
{
  return hexagon_builtin_mask_for_load;
}




/*-------------------------------------
Describing Relative Costs of Operations
-------------------------------------*/

/* Implements hook STORE_BY_PIECES_P */

bool
hexagon_store_by_pieces_p(unsigned HOST_WIDE_INT size, unsigned int alignment)
{
  unsigned HOST_WIDE_INT ninsns;
  unsigned int store_width = MIN (MAX (alignment, 1), 4);

  ninsns = size / store_width * (TARGET_V4_FEATURES ? 2 : 3);
  size %= store_width;   
  if(optimize_size){
    while(size){
      store_width /= 2;
      ninsns += size / store_width * 2;
      size %= store_width;   
    }
    return ninsns <= 3;
  }
  else {
    return ninsns <= 16;
  }
}




/* Helper function for hexagon_rtx_costs */

static bool
hexagon_free_immediate(rtx x ATTRIBUTE_UNUSED, int outer_code ATTRIBUTE_UNUSED, int value ATTRIBUTE_UNUSED)
{
  return true;
}




/* Implements hook TARGET_RTX_COSTS */

static bool
hexagon_rtx_costs(rtx x, int code, int outer_code, int *total, bool speed ATTRIBUTE_UNUSED)
{
  enum machine_mode mode = GET_MODE (x);

  switch(code){
    case CONST_INT:
      if(hexagon_free_immediate(x,outer_code,INTVAL(x))){
        *total = 0;
        return true;
      }
    /* Handle more stuff here ? */
    /* FALL THROUGH */
    case CONST_DOUBLE:
    case CONST:
    case HIGH:
    case SYMBOL_REF:
      *total = COSTS_N_INSNS (2);
      return true;

    case MEM:
      *total = optimize_size ? COSTS_N_INSNS (2) : (COSTS_N_INSNS (1) + 1);
      return true;

    case LABEL_REF:
      /* Branches I think */
      *total = 0;
      return true;

    case PLUS:
    case MINUS:
      if(mode == DFmode || mode == SFmode){
        *total = COSTS_N_INSNS (50);
      }
      else if(outer_code == PLUS || outer_code == MINUS){
        /* Add/Sub and Accumulate */
        /* OK, we'd like to tell GCC something here, but
         * It's a little bit tricky, because otherwise
         * GCC will think that (+ A, (+ (+ B B) (+ B B)))
         * is only cost 1, and choose it instead of
         * (+ A (<< B 2)) which is obviously better for us
         */
        /* ??? change to look to make sure that args are regs
         * and then choose 0? */
        *total = COSTS_N_INSNS (1) - 1;
      }
      else {
        *total = COSTS_N_INSNS (1);
      }
      return false;

    case MULT:
      if(mode == DFmode || mode == SFmode){
        *total = COSTS_N_INSNS (50);
      }
      else if(outer_code == PLUS || outer_code == MINUS){
        /* MAC */
        *total = 0;
      }
      else {
        *total = COSTS_N_INSNS (1);
      }
      /* TODO: "real" DI mults should cost more */
      return false;

    case UDIV:
    case UMOD:
    case DIV:
    case MOD:
      *total = optimize_size ? COSTS_N_INSNS (2) : COSTS_N_INSNS (40);
      return false;

    case CLZ:
    case FFS:
      *total = COSTS_N_INSNS(1);
      return false;

    case NOT:
    case AND:
    case IOR:
    case XOR:
    case SMIN:
    case UMIN:
    case SMAX:
    case UMAX:
    case ZERO_EXTRACT:
      *total = COSTS_N_INSNS (1);
      return false;

    case ASHIFT:
      /* Mult with high part */
      if(outer_code == TRUNCATE
         && GET_CODE (XEXP (x, 0)) == MULT
         && mode == SImode){
        return COSTS_N_INSNS (1);
      }
      else if(outer_code == PLUS){
        /* Shift plus acc */
        *total = 0;
      }
      else if(outer_code == MINUS){
        /* Shift plus acc */
        *total = 0;
      }
      else if(outer_code == AND){
        /* Shift plus logical */
        *total = 0;
      }
      else if(outer_code == IOR){
        /* Shift plus logical */
        *total = 0;
      }
      return false;

    case ASHIFTRT:
      /* Mult with high part */
      if(outer_code == TRUNCATE
         && GET_CODE (XEXP (x, 0)) == MULT
         && mode == SImode){
        return COSTS_N_INSNS (1);
      }
      else if(outer_code == PLUS){
        /* Shift plus acc */
        *total = 0;
      }
      else if(outer_code == MINUS){
        /* Shift plus acc */
        *total = 0;
      }
      return false;

    case LSHIFTRT:
      /* Mult with high part */
      if(outer_code == TRUNCATE
         && GET_CODE (XEXP (x, 0)) == MULT
         && mode == SImode){
        return COSTS_N_INSNS (1);
      }
      else if(outer_code == AND){
        /* Shift plus logical */
        *total = 0;
      }
      else if(outer_code == IOR){
        /* Shift plus logical */
        *total = 0;
      }
      return false;

    case SIGN_EXTEND:
    case ZERO_EXTEND:
      if(GET_CODE (XEXP (x, 0)) == MEM){
        *total = 0;
      }
      else {
        *total = COSTS_N_INSNS (1);
      }
      return false;

    case NEG:
    case ABS:
      /* Yes, even float mode */
      *total = COSTS_N_INSNS (1);
      return false;

    case COMPARE:
      if(mode == DFmode || mode == SFmode){
        *total = COSTS_N_INSNS (50);
      }
      else {
        *total = COSTS_N_INSNS (1);
      }
      return false;

    case FLOAT:
    case UNSIGNED_FLOAT:
    case FIX:
    case UNSIGNED_FIX:
    case FLOAT_TRUNCATE:
    case FLOAT_EXTEND:
      *total = COSTS_N_INSNS (50);
      return false;

    case CALL:
    case IF_THEN_ELSE:
      *total = COSTS_N_INSNS (1);
      return true;

    default:
      /* Guess is good enough */
      return false;
  }
  return false;
}




bool
hexagon_rtx_costs_debug(rtx x, int code, int outer_code, int *total, bool speed)
{
  bool retval;

  debug_rtx(x);
  retval = hexagon_rtx_costs(x, code, outer_code, total, speed);
  fprintf(stderr, "rtx_cost:  %d, %s\n\n", *total, retval ? "true" : "false");

  return retval;
}




/* Implements hook TARGET_ADDRESS_COST */

static int
hexagon_address_cost(rtx address, bool speed ATTRIBUTE_UNUSED)
{
  enum rtx_code code = GET_CODE(address);
  rtx mod;

  switch(code){
    case SYMBOL_REF:
    case CONST:
      if(g_switch_value > 0){
        return COSTS_N_INSNS (1) - 2;
      }
      if(TARGET_V4_FEATURES){
        return COSTS_N_INSNS (1) + 1;
      }
      return COSTS_N_INSNS (3);
    case PRE_INC:
    case PRE_DEC:
      return COSTS_N_INSNS (3);
    case POST_INC:
    case POST_DEC:
      return COSTS_N_INSNS (1) - 3;
    case POST_MODIFY:
      mod = XEXP (address, 1);
      if(GET_CODE (mod) == PLUS
         && REG_P (XEXP (mod, 0))
         && GET_CODE (XEXP (mod, 1)) == CONST_INT){
        return COSTS_N_INSNS (1) - 3;
      }
      return COSTS_N_INSNS (3);
    case REG:
      return COSTS_N_INSNS (1);
    case PLUS:
      {
        rtx base = XEXP (address, 0);
        rtx offset = XEXP (address, 1);
        if((REG_P (offset) || CONSTANT_P (offset)) && !REG_P (base)){
          base = XEXP (address, 1);
          offset = XEXP (address, 0);
        }
        if(REG_P (base)
           || (TARGET_V4_FEATURES && CONSTANT_P (base))){
          if(GET_CODE (offset) == CONST_INT
             && IN_RANGE (INTVAL (offset), -(1 << 12), (1 << 12) - 4)){
            return COSTS_N_INSNS (1);
          }
          if(TARGET_V4_FEATURES && CONSTANT_P (offset)){
            return COSTS_N_INSNS (1) + 2;
          }
          if(TARGET_V4_FEATURES && TARGET_BASE_PLUS_INDEX){
            if(REG_P (offset)){
              return COSTS_N_INSNS (1) - 1;
            }
            if(GET_CODE (offset) == MULT || GET_CODE (offset) == ASHIFT){
              rtx index = XEXP (offset, 0);
              rtx scale = XEXP (offset, 1);
              if(GET_CODE (offset) == MULT && !REG_P (index)){
                index = XEXP (offset, 1);
                scale = XEXP (offset, 0);
              }
              if(REG_P (index)
                 && GET_CODE (scale) == CONST_INT){
                if(REG_P (base)){
                  return COSTS_N_INSNS (1) - 2;
                }
                return COSTS_N_INSNS (1) + 1;
              }
            }
          }
        }
      }
      return COSTS_N_INSNS (3);
    case CONST_INT:
    case LABEL_REF:
      if(TARGET_V4_FEATURES){
        return COSTS_N_INSNS (1) + 1;
      }
      /* FALL THROUGH */
    default:
      return COSTS_N_INSNS (3);
  }
  /* Should never get here */
  gcc_unreachable();
}




int
hexagon_address_cost_debug(rtx address, bool speed)
{
  int retval;

  debug_rtx(address);
  retval = hexagon_address_cost(address, speed);
  fprintf(stderr, "address_cost:  %d\n\n", retval);

  return retval;
}




/*---------------------------------
Adjusting the Instruction Scheduler
---------------------------------*/

/* Implements hook TARGET_SCHED_ISSUE_RATE */

static int
hexagon_sched_issue_rate(void)
{
  return 6; /* ??? 4 or 6? */
}

static tree
get_mem_expr_from_mem_rtx (rtx mem)
{
  tree mem_expr;
  mem_expr = MEM_EXPR (mem);
  if (!mem_expr)
    {
      rtx addr, reg;
      reg = NULL_RTX;
      addr = XEXP (mem, 0);
      if (GET_CODE (addr) == PLUS)
        reg = XEXP (addr, 0);
      else if (GET_CODE (addr) == REG)
        reg = addr;
      
      if (reg)
        mem_expr = REG_EXPR (reg);
   }
  return mem_expr;
}

/*
  --------------------------------------------------------------- 
 | * - \ | / - \ | / - \ | / - \ | / - \ | / - \ | / - \ | / - * | 
 | |  -------------------------------------------------------  | |
 | / |    The Instruction Scheduler calculates Instruction   | \ |
 | - |        Dependencies.  Evaluate the dependencies       | - |
 | \ |      calculated by the Scheduler. Specifically,       | / |
 | | |     remove dependencies between stores to addresses   | | |
 | / |    based on __restrict qualified pointers and loads   | \ |
 | - |                    from addresses.                    | - |
 | \ |                       --==*==--                       | / |
 | |  -------------------------------------------------------  | |
 | * - / | \ - / | \ - / | \ - / | \ - / | \ - / | \ - / | \ - * |
  --------------------------------------------------------------- 
*/ 

static inline unsigned int 
get_pair_comp_reg (unsigned int reg)  
{ 
    return (reg & 0x1) ? reg - 1 : reg + 1; 
} 

static inline bool
pair_match (unsigned int x_reg,int x_pair,unsigned int y_reg,int y_pair)
{
     /*  x) r0     y) r0   */
    if (x_reg == y_reg)  return true; 
    
    if (y_pair)
      {
        if (x_pair)
          { /*   x) r1:0    y) r0:1    */ 
            if (get_pair_comp_reg(x_reg) == get_pair_comp_reg(y_reg)
                || get_pair_comp_reg(x_reg) == y_reg
                || get_pair_comp_reg(y_reg) == x_reg)   return true;  
          }
        else
          { /*   x) r1      y) r0:1    */
            if (get_pair_comp_reg(y_reg) == x_reg)   return true;  
          }
    }
    else
      {
        if (x_pair)
          { /*   x) r1:0    y) r1    */
            if (get_pair_comp_reg(x_reg) == y_reg)   return true;  
          }
      }
    
    return false; 
}
     
static bool
get_usable_reg_num
(rtx dst_0,unsigned int *reg_number, int *updated, int *reg_pair)
{
    if (!dst_0)  return false; 
       
    switch (GET_CODE (dst_0))
      {
        case REG:
            if (GET_MODE(dst_0) == DImode)   (*reg_pair)++; 
            *reg_number = REGNO(dst_0);
            return true; 
        break; 
        case POST_INC: 
        case POST_DEC:
        case PRE_INC:
        case PRE_DEC:
        case POST_MODIFY:
        case PLUS:
        case MINUS: 
            (*updated)++;            
            return get_usable_reg_num(XEXP (dst_0 ,0), reg_number,
                                      updated, reg_pair); 
        break;
        default:
            return false; 
        break;
    }
    return false; 
}


/* Implements hook TARGET_SCHED_FIRST_CYCLE_MULTIPASS_DFA_LOOKAHEAD */

static int
hexagon_sched_first_cycle_multipass_dfa_lookahead(void)
{
  return 8; /* ??? dunno */
}




/*--------------------------------------------------
Dividing the Output into Sections (Texts, Data, ...)
--------------------------------------------------*/

/* Implements hook TARGET_ASM_SELECT_RTX_SECTION */

static section *
hexagon_asm_select_rtx_section(
  enum machine_mode mode,
  rtx x,
  unsigned HOST_WIDE_INT align
)
{
  if(GET_MODE_SIZE (mode) > 0 && GET_MODE_SIZE (mode) <= g_switch_value){
      if(TARGET_SECTION_SORTING){ 
          const char *sname;

          switch(GET_MODE_SIZE (mode))
            {
            case 1: sname = ".sdata.1";	  break; 
            case 2: sname = ".sdata.2";   break;
            case 4: sname = ".sdata.4";   break;
            case 8: sname = ".sdata.8";   break;	
            default: sname = ".sdata";    break; 
            }
          return get_named_section (NULL_TREE, sname, 0);
      } 
      return sdata_section;
  }
  else {
      return default_elf_select_rtx_section(mode, x, align);
  }
}




extern void switch_to_section (section *);                 

#define MAX_DECLARE_RECURSION   1024
static tree  list_of_visited_declaration [MAX_DECLARE_RECURSION];
static int     list_of_visited_declaration_counter;

bool
has_this_tree_been_visited(tree node){
   int i;

   for(i=0;i<list_of_visited_declaration_counter;i++){
        if(list_of_visited_declaration[i]       == node)        return  1;
   }
   return 0;
}




void
remember_this_tree(tree node){
   int i;

   for(i=0;i<list_of_visited_declaration_counter;i++){
        if(list_of_visited_declaration[i]       == node)        return;
   }
   /* No, have not seen it, so remember visiting it */
   list_of_visited_declaration[list_of_visited_declaration_counter++]   = node;
   if(list_of_visited_declaration_counter >= MAX_DECLARE_RECURSION){
        fprintf(stderr,"Error. Declaration recursion overflow (%d)\n",MAX_DECLARE_RECURSION);
        abort();
   }
   return;
}




/* descent_smallest designed to identify the smallest addressable entity
   in a declaration. Used for sdata elements sorting */ 
unsigned int 
descent_smallest(const char *prefix ATTRIBUTE_UNUSED, tree node, unsigned int smallest){
  unsigned int	new_smallest	= smallest; 

  if ((node == 0) || (smallest == 1))	return	new_smallest; 
  if (TREE_CODE (node) == ERROR_MARK)	return  new_smallest; 
  if(has_this_tree_been_visited(node))  return  new_smallest;
  
   switch (TREE_CODE_CLASS (TREE_CODE (node))){ 
    case tcc_declaration:  /* A decl node */
      remember_this_tree(node); 
      /* Also true for enums */  
      if(TREE_CODE (node) == FIELD_DECL && DECL_PACKED(node))		return 1; 
      if(TREE_CODE (node) == FIELD_DECL && DECL_BIT_FIELD(node))	return 1; 
      /* Now Look at the type */  
      new_smallest    = descent_smallest ("type",TREE_TYPE (node), new_smallest);  
      new_smallest    = descent_smallest ("attributes",DECL_ATTRIBUTES (node), new_smallest); 

      if (TREE_CODE (node) == PARM_DECL)
          new_smallest	= descent_smallest ("arg-type", DECL_ARG_TYPE (node), new_smallest);
      
      if (TREE_CODE (TREE_TYPE(node)) == RECORD_TYPE || TREE_CODE (TREE_TYPE(node)) == UNION_TYPE || TREE_CODE (TREE_TYPE(node)) == QUAL_UNION_TYPE){ 
		tree tchain_ptr = TYPE_FIELDS(TREE_TYPE(node));
        while(tchain_ptr != NULL_TREE){
			new_smallest    = descent_smallest ("field from declare", TREE_CHAIN (tchain_ptr), new_smallest); 
            tchain_ptr      = TREE_CHAIN(tchain_ptr);
        }
      }
      break;
    case tcc_type:  /* a type node */
      if(POINTER_TYPE_P(node)){
		if((POINTER_SIZE/BITS_PER_UNIT) < new_smallest)      new_smallest    = (POINTER_SIZE/BITS_PER_UNIT);
        return  new_smallest;
      }
      else	new_smallest    = descent_smallest ("Descend type",TREE_TYPE (node), new_smallest); 
      /* Bail out right away - report the smallest possible unit */  
      if (TYPE_PACKED (node))	return 1; 

      new_smallest	= descent_smallest ("unit size", TYPE_SIZE_UNIT (node), new_smallest);
      new_smallest 	= descent_smallest ("attributes", TYPE_ATTRIBUTES (node), new_smallest);

      if (TREE_CODE (node) == ENUMERAL_TYPE)
        new_smallest	= descent_smallest ("values", TYPE_VALUES (node), new_smallest);
      else if (TREE_CODE (node) == ARRAY_TYPE)	new_smallest    = descent_smallest ("array_type",TYPE_DOMAIN(node), new_smallest); 
      else if (TREE_CODE (node) == OFFSET_TYPE)	new_smallest    = descent_smallest ("offset_type", TYPE_OFFSET_BASETYPE(node), new_smallest); 
      else if (TREE_CODE (node) == VECTOR_TYPE)	new_smallest    = descent_smallest ("vector_type", TYPE_VECTOR_SUBPARTS(node), new_smallest); 
      else if (TREE_CODE (node) == RECORD_TYPE || TREE_CODE (node) == UNION_TYPE || TREE_CODE (node) == QUAL_UNION_TYPE){  
		new_smallest	= descent_smallest ("fields", TYPE_FIELDS (node), new_smallest);
      }
      break;

    case tcc_expression:  	/* an expression */
    case tcc_comparison:  	/* a comparison expression */
    case tcc_unary:  		/* a unary arithmetic expression */
    case tcc_binary:  		/* a binary arithmetic expression */
    case tcc_reference:		/* a reference */
    case tcc_statement:	 	/* an expression with side effects */
    case tcc_vl_exp: 
      if (TREE_CODE (node) == BIND_EXPR){ 
          new_smallest	= descent_smallest ("vars", TREE_OPERAND (node, 0), new_smallest);
          new_smallest	= descent_smallest ("body", TREE_OPERAND (node, 1), new_smallest);
          new_smallest	= descent_smallest ("block", TREE_OPERAND (node, 2), new_smallest);
          break;
      }
      if (TREE_CODE (node) == CONSTRUCTOR){
		  new_smallest    = descent_smallest ("Descend constructor type",TREE_TYPE (node), new_smallest); 
      }
      new_smallest	= descent_smallest ("chain", TREE_CHAIN (node), new_smallest);
      break;
    case tcc_constant:  	/* a constant */
    case tcc_exceptional: 	/* something random, like an identifier.  */
      switch (TREE_CODE (node)){ 
        case INTEGER_CST:
          if (TREE_INT_CST_HIGH (node) == 0){ 
            if(TREE_INT_CST_LOW (node) < new_smallest)	new_smallest	= TREE_INT_CST_LOW (node); 
	  }   
          else if (TREE_INT_CST_HIGH (node) == -1 && TREE_INT_CST_LOW (node) != 0){
			// Dev warning. fprintf(stderr,"Error. Negative field size (%d)\n",TREE_INT_CST_LOW (node)); 
			new_smallest	= 1; 
	  }
          else{
			if(TREE_INT_CST_LOW (node) < new_smallest)	new_smallest	= TREE_INT_CST_LOW (node); 
	  }
          break;

        case REAL_CST:
		case FIXED_CST: 
        case VECTOR_CST:
        case COMPLEX_CST:
        case STRING_CST:
	    // Dev warning. warning("Usupported constant type."); 
            new_smallest	= descent_smallest ("chain", TREE_CHAIN (node), new_smallest);
          break;

        case IDENTIFIER_NODE:
          // Dev warning. warning("Usupported constant type IDENTIFIER_NODE.");
		  new_smallest	= 1; 
          break;
        case TREE_LIST:
          new_smallest	= descent_smallest ("purpose", TREE_PURPOSE (node),new_smallest);
          new_smallest	= descent_smallest ("value", TREE_VALUE (node), new_smallest);
          new_smallest	= descent_smallest ("chain", TREE_CHAIN (node), new_smallest);
          break;
        case TREE_VEC:
	case CONSTRUCTOR:
	case STATEMENT_LIST:
          ; // Dev warning. warning("Usupported constant type TREE_VEC.");
          break;
	case BLOCK:
		  new_smallest	= descent_smallest ("vars", BLOCK_VARS (node), new_smallest);
          new_smallest	= descent_smallest ("supercontext", BLOCK_SUPERCONTEXT (node), new_smallest);
          new_smallest	= descent_smallest ("subblocks", BLOCK_SUBBLOCKS (node), new_smallest);
          new_smallest	= descent_smallest ("chain", BLOCK_CHAIN (node), new_smallest);
          new_smallest	= descent_smallest ("abstract_origin",BLOCK_ABSTRACT_ORIGIN (node), new_smallest); 
		  break; 
		case SSA_NAME:
		case OMP_CLAUSE:
		  ; // Dev warning. warning("Usupported constant type TREE_VEC.");
          break;
        default:
		  new_smallest	= descent_smallest ("default chain", TREE_CHAIN (node), new_smallest);
          break;
        }
      break;
    }
    return new_smallest;  
}




/* smallest_accessable_entity_in_declaration designed to identify the smallest addressable entity
in a declaration. Used for sdata elements sorting */ 
unsigned HOST_WIDE_INT
smallest_accessable_entity_in_declaration(tree decl)
{
   list_of_visited_declaration_counter  = 0;
   /* Here I assume there are no atomic data types larger than 128 bytes in this machine */ 
   return descent_smallest(" top ", decl, DEFAULT_LARGEST_ALIGNMENT); 
}




static bool
bss_initializer_p (const_tree decl)
{
  return (DECL_INITIAL (decl) == NULL
          || DECL_INITIAL (decl) == error_mark_node
          || (flag_zero_initialized_in_bss
              /* Leave constant zeroes in .rodata so they  can be shared.  */
              && !TREE_READONLY (decl)
              && initializer_zerop (DECL_INITIAL (decl))));
}




/* Copycat from similar internal declaration */ 
enum section_category
hexagon_categorize_decl_for_section (const_tree decl, int reloc)
{
  enum section_category ret;

  if (TREE_CODE (decl) == FUNCTION_DECL)    return SECCAT_TEXT;
  else if (TREE_CODE (decl) == STRING_CST)
    {
	  if (flag_mudflap)  /* or !flag_merge_constants */ /*_LSY_ store strings in data segment disable this if */ 
			return SECCAT_RODATA;
      else	return SECCAT_RODATA_MERGE_STR;
    }
  else if (TREE_CODE (decl) == VAR_DECL)
    {
	  if (bss_initializer_p (decl))	ret = SECCAT_BSS;
      else if (! TREE_READONLY (decl)
	       || TREE_SIDE_EFFECTS (decl)
	       || ! TREE_CONSTANT (DECL_INITIAL (decl)))
	{
	  /* Here the reloc_rw_mask is not testing whether the section should
	     be read-only or not, but whether the dynamic link will have to
	     do something.  If so, we wish to segregate the data in order to
	     minimize cache misses inside the dynamic linker.  */
	  if (reloc & targetm.asm_out.reloc_rw_mask ())
			ret = reloc == 1 ? SECCAT_DATA_REL_LOCAL : SECCAT_DATA_REL;
	  else	ret = SECCAT_DATA;
	}
      else if (reloc & targetm.asm_out.reloc_rw_mask ())
			ret = reloc == 1 ? SECCAT_DATA_REL_RO_LOCAL : SECCAT_DATA_REL_RO;
      else if (reloc || flag_merge_constants < 2)
	/* C and C++ don't allow different variables to share the same
	   location.  -fmerge-all-constants allows even that (at the
	   expense of not conforming).  */
	ret = SECCAT_RODATA;
      else if (TREE_CODE (DECL_INITIAL (decl)) == STRING_CST)
			ret = SECCAT_RODATA_MERGE_STR_INIT;
      else	ret = SECCAT_RODATA_MERGE_CONST;
    }
  else if (TREE_CODE (decl) == CONSTRUCTOR)
    {
      if ((reloc & targetm.asm_out.reloc_rw_mask ())
	  || TREE_SIDE_EFFECTS (decl)
	  || ! TREE_CONSTANT (decl))
			ret = SECCAT_DATA;
      else	ret = SECCAT_RODATA;
    }
  else    ret = SECCAT_RODATA;

  /* There are no read-only thread-local sections.  */
  if (TREE_CODE (decl) == VAR_DECL && DECL_THREAD_LOCAL_P (decl))
    {
      /* Note that this would be *just* SECCAT_BSS, except that there's
	 no concept of a read-only thread-local-data section.  */
      if (ret == SECCAT_BSS
	  || (flag_zero_initialized_in_bss
	      && initializer_zerop (DECL_INITIAL (decl))))
			ret = SECCAT_TBSS;
      else	ret = SECCAT_TDATA;
    }

  /* If the target uses small data sections, select it.  */
  else if (targetm.in_small_data_p (decl))
    {
      if (ret == SECCAT_BSS)	ret = SECCAT_SBSS;
      else if (targetm.have_srodata_section && ret == SECCAT_RODATA)
		ret = SECCAT_SRODATA;
      else	ret = SECCAT_SDATA;
    }

  return ret;
}




/* Similar to default_elf_select_section from varasm.c  but is capable of sorting sdata 
   into subsections. sbss is also handled in a similar way, but not in this 
   function */ 
   
extern section *mergeable_string_section (tree decl ATTRIBUTE_UNUSED,unsigned HOST_WIDE_INT align ATTRIBUTE_UNUSED,unsigned int flags ATTRIBUTE_UNUSED); 

section *
hexagon_select_section (tree decl, int reloc,
                        unsigned HOST_WIDE_INT align)
{
  const char *sname;

  switch (hexagon_categorize_decl_for_section (decl, reloc)){ 
    case SECCAT_TEXT:
      /* We're not supposed to be called on FUNCTION_DECLs.  */
      gcc_unreachable ();
	case SECCAT_RODATA:
      return readonly_data_section;
    case SECCAT_RODATA_MERGE_STR:
      return mergeable_string_section (decl, align, 0);
    case SECCAT_RODATA_MERGE_STR_INIT:
      return mergeable_string_section (DECL_INITIAL (decl), align, 0);
    case SECCAT_RODATA_MERGE_CONST:
      return mergeable_constant_section (DECL_MODE (decl), align, 0); 
    case SECCAT_SRODATA:
      sname = ".sdata2";
      break;
    case SECCAT_DATA:
      return data_section;
      break;
    case SECCAT_DATA_REL:
      sname = ".data.rel";
      break;
    case SECCAT_DATA_REL_LOCAL:
      sname = ".data.rel.local";
      break;
    case SECCAT_DATA_REL_RO:
      sname = ".data.rel.ro";
      break;
    case SECCAT_DATA_REL_RO_LOCAL:
      sname = ".data.rel.ro.local";
      break;
    case SECCAT_SDATA:
      if(TARGET_SECTION_SORTING){ 
      	switch(smallest_accessable_entity_in_declaration(decl)){ 
			case 1: sname = ".sdata.1";	  break; 
			case 2: sname = ".sdata.2";   break;
			case 4: sname = ".sdata.4";   break;
			case 8: sname = ".sdata.8";   break;	
			default:	// Dev warning. fprintf(stderr,"Warning. smallest_accessable_entity_in_declaration (%d)\n",smallest_accessable_entity_in_declaration(decl)); 
				sname = ".sdata";   break; 
  	}
      } 
      else	sname = ".sdata";
      break;
    case SECCAT_TDATA:
      sname = ".tdata";
      break;
    case SECCAT_BSS:
	  if (bss_section)   return bss_section;
      sname = ".bss";
      break;
    case SECCAT_SBSS:
      sname = ".sbss";
      break;
    case SECCAT_TBSS:
      sname = ".tbss";
      break;
    default:
      gcc_unreachable ();
    }

	if (!DECL_P (decl))
    decl = NULL_TREE;
  return get_named_section (decl, sname, reloc);
}




void
hexagon_elf_asm_named_section (const char *name, unsigned int flags,
			       tree decl ATTRIBUTE_UNUSED)
{
  char flagchars[10], *f = flagchars;

  /* _LSY_ Note, unique section name does not matter for .comm declarations - it will be managed by linker, 
         so here we do not construct unique section name even if flag_data_sections is specified */ 

  /* If we have already declared this section, we can use an
     abbreviated form to switch back to it -- unless this section is
     part of a COMDAT groups, in which case GAS requires the full
     declaration every time.  */
  if (!(HAVE_COMDAT_GROUP && (flags & SECTION_LINKONCE))
      && (flags & SECTION_DECLARED))
    {
      fprintf (asm_out_file, "\t.section\t%s\n", name);
      /* But we still need to output subsection information
         or we can end up with same section split and
         sorted in different subsections of the same section */
      if(TARGET_SECTION_SORTING && decl && (smallest_accessable_entity_in_declaration(decl) > 1))
        fprintf (asm_out_file, "\t.subsection\t-%d\n",
                 floor_log2(smallest_accessable_entity_in_declaration(decl)));
      return;
    }

  if (!(flags & SECTION_DEBUG))
    *f++ = 'a';
  if (flags & SECTION_WRITE)
    *f++ = 'w';
  if (flags & SECTION_CODE)
    *f++ = 'x';
  if (flags & SECTION_SMALL)
    *f++ = 's';
  if (flags & SECTION_MERGE)
    *f++ = 'M';
  if (flags & SECTION_STRINGS)
    *f++ = 'S';
  if (flags & SECTION_TLS)
    *f++ = 'T';
  if (HAVE_COMDAT_GROUP && (flags & SECTION_LINKONCE))
    *f++ = 'G';
  *f = '\0';

  fprintf (asm_out_file, "\t.section\t%s,\"%s\"", name, flagchars);

  if (!(flags & SECTION_NOTYPE))
    {
      const char *type;
      const char *format;

      if (flags & SECTION_BSS)
	type = "nobits";
      else
	type = "progbits";

      format = ",@%s";
#ifdef ASM_COMMENT_START
      /* On platforms that use "@" as the assembly comment character,
	 use "%" instead.  */
      if (strcmp (ASM_COMMENT_START, "@") == 0)
	format = ",%%%s";
#endif
    fprintf (asm_out_file, format, type);

      if (flags & SECTION_ENTSIZE)
	fprintf (asm_out_file, ",%d", flags & SECTION_ENTSIZE);
      if (HAVE_COMDAT_GROUP && (flags & SECTION_LINKONCE))
	fprintf (asm_out_file, ",%s,comdat",
		 lang_hooks.decls.comdat_group (decl));
    }

  putc ('\n', asm_out_file);
  
  /* _LSY_ Also put subsection for better sorting */ 
  if(TARGET_SECTION_SORTING && decl && (smallest_accessable_entity_in_declaration(decl) > 1))
     fprintf (asm_out_file, "\t.subsection\t-%d\n",floor_log2(smallest_accessable_entity_in_declaration(decl)));
}




/* Implements hook TARGET_IN_SMALL_DATA_P */

static bool
hexagon_in_small_data_p(const_tree exp)
{
  /* We want to merge strings, so we never consider them small data. */
  if(TREE_CODE (exp) == STRING_CST){
    return false;
  }

  /* Functions are never small data. */
  if(TREE_CODE (exp) == FUNCTION_DECL){
    return false;
  }

  if(TREE_CODE (exp) == VAR_DECL && DECL_SECTION_NAME (exp)){
    const char *section = TREE_STRING_POINTER (DECL_SECTION_NAME (exp));
    if(!strcmp(section, ".sdata")
       || !strncmp(section, ".sdata.", 7)
       || !strncmp(section, ".gnu.linkonce.s.", 16)
       || !strcmp(section, ".sbss")
       || !strncmp(section, ".sbss.", 6)
       || !strncmp(section, ".gnu.linkonce.sb.", 17)){
      return true;
    }
  }
  else {
    unsigned HOST_WIDE_INT size = int_size_in_bytes(TREE_TYPE (exp));
    if((size > 0) && (size <= g_switch_value)){
      return true;
    }
  }
  return false;
}




/*-------------------------------
Output of Uninitialized Variables
-------------------------------*/

/* Implements macro ASM_OUTPUT_ALIGNED_DECL_COMMON */

void
hexagon_asm_output_aligned_decl_common(
  FILE *stream,
  tree decl,
  const char *name,
  unsigned HOST_WIDE_INT size,
  unsigned HOST_WIDE_INT alignment
){
    unsigned int flags = SECTION_WRITE | SECTION_BSS | SECTION_NAMED; 

	if(decl && sdata_symbolic_operand(XEXP (DECL_RTL (decl), 0), Pmode))
			switch_to_section(get_section(".sbss",flags,decl)); 
	else 	switch_to_section(get_section(".bss",flags,decl)); 
  
	if(TARGET_SECTION_SORTING && decl){ 
    	fprintf(stream, "\t.comm\t");
    	assemble_name(stream, name);
    	fprintf(stream, "," HOST_WIDE_INT_PRINT_UNSIGNED
                "," HOST_WIDE_INT_PRINT_UNSIGNED
		"," HOST_WIDE_INT_PRINT_UNSIGNED "\n",
                  size, alignment / BITS_PER_UNIT, smallest_accessable_entity_in_declaration(decl)); 
	}
	else{ 
		fprintf(stream, "\t.comm\t");
		assemble_name(stream, name);
		fprintf(stream, "," HOST_WIDE_INT_PRINT_UNSIGNED
                  "," HOST_WIDE_INT_PRINT_UNSIGNED "\n",
                  size, alignment / BITS_PER_UNIT);
	}
}




/* Implements macro ASM_OUTPUT_ALIGNED_DECL_LOCAL

   Define a local (static) uninitialized variable.
   For some reason, the default behavior of:
     .local <name>
     .comm <name>,<size>,<align>
   is not working--the assembler appears to ignore the
   ".local" directive--so we change it to:
     .lcomm <name>,<size>,<align> */
/* ??? Is that still true? */

void
hexagon_asm_output_aligned_decl_local(
  FILE *stream,
  tree decl,
  const char *name,
  unsigned HOST_WIDE_INT size,
  unsigned HOST_WIDE_INT alignment
){
  unsigned int flags = SECTION_WRITE | SECTION_BSS | SECTION_NAMED;
  
  if(decl && sdata_symbolic_operand(XEXP (DECL_RTL (decl), 0), Pmode)) 
		switch_to_section(get_section(".sbss",flags,decl));
  else 	switch_to_section(get_section(".bss",flags,decl));

  if(TARGET_SECTION_SORTING && decl){ 
    	fprintf(stream, "\t.lcomm\t");
    	assemble_name(stream, name);
    	fprintf(stream, "," HOST_WIDE_INT_PRINT_UNSIGNED
                "," HOST_WIDE_INT_PRINT_UNSIGNED
		"," HOST_WIDE_INT_PRINT_UNSIGNED "\n",
                  size, alignment / BITS_PER_UNIT, smallest_accessable_entity_in_declaration(decl)); 
   }
   else{
	fprintf(stream, "\t.lcomm\t");
	assemble_name(stream, name);
	fprintf(stream, "," HOST_WIDE_INT_PRINT_UNSIGNED
                  "," HOST_WIDE_INT_PRINT_UNSIGNED "\n",
                  size, alignment / BITS_PER_UNIT);
   }
}




/*------------------------------
Output of Assembler Instructions
------------------------------*/

/* Helper function for hexagon_asm_output_opcode */

static void
hexagon_output_operand(FILE *f, rtx x, int code ATTRIBUTE_UNUSED)
{
  if(x && GET_CODE (x) == SUBREG){
    x = alter_subreg(&x);
  }

  /* X must not be a pseudo reg. */
  gcc_assert(!x || !REG_P (x) || REGNO (x) < FIRST_PSEUDO_REGISTER);

  PRINT_OPERAND (f, x, code);
}

/* Used by macro ASM_OUTPUT_OPCODE

   Outputs the assembly corresponding to the current insn
   and adds brackets as needed */

const char *
hexagon_asm_output_opcode(FILE *f, const char *ptr)
{
  struct hexagon_final_info *final_info;
  int c;
  int oporder[MAX_RECOG_OPERANDS];
  char opoutput[MAX_RECOG_OPERANDS];
  int ops = 0;

  if(!TARGET_PACKETS){
    return ptr;
  }

  final_info = &cfun->machine->final_info;

  /* Ignore the output template for this insn. */
  if(!final_info->print_insn){
    for(; *ptr; ptr++);
  }

  /* Begin packet. */
  if(final_info->start_packet){
    fputs("{\n\t", f);
  }

  if (TARGET_ANNOTATE_DUPLEX && final_info->duplex) {
    fputs("//duplex\n\t", f);
  }

  if(final_info->indent_insn){
    fputc('\t', f);
  }

  memset(opoutput, 0, sizeof(opoutput));
  /* Output the assembly insn.  Copied from output_asm_insn(). */
  while((c = *ptr)){
    ptr++;
    switch(c){
      case '\n':
        ops = 0;
        memset(opoutput, 0, sizeof(opoutput));

        putc(c, f);
        if(final_info->indent_insn){
          putc('\t', f);
        }
        break;

      case '%':
        /* %% outputs a single %. */
        if(*ptr == '%'){
          ptr++;
          putc(c, f);
        }
        /* % followed by a letter and some digits
           outputs an operand in a special way depending on the letter.
           Letters `acln' are implemented directly.
           Other letters are passed to `hexagon_output_operand' so that
           the PRINT_OPERAND macro can define them. */
        else if(ISALPHA (*ptr)){
          int letter = *ptr++;
          unsigned long opnum;
          char *endptr;

          opnum = strtoul(ptr, &endptr, 10);

          if(endptr == ptr){
            output_operand_lossage("operand number missing after %%-letter");
          }
          else if(letter == 'l'){
            output_asm_label(final_info->insn_ops[opnum]);
          }
          else if(letter == 'a'){
            output_address(final_info->insn_ops[opnum]);
          }
          else if(letter == 'c'){
            if(CONSTANT_ADDRESS_P (final_info->insn_ops[opnum])){
              output_addr_const(f, final_info->insn_ops[opnum]);
            }
            else {
              hexagon_output_operand(f, final_info->insn_ops[opnum], 'c');
            }
          }
          else if(letter == 'n'){
            if(GET_CODE (final_info->insn_ops[opnum]) == CONST_INT){
              fprintf(f, HOST_WIDE_INT_PRINT_DEC,
                      -INTVAL (final_info->insn_ops[opnum]));
            }
            else {
              putc('-', f);
              output_addr_const(f, final_info->insn_ops[opnum]);
            }
          }
          else {
            hexagon_output_operand(f, final_info->insn_ops[opnum], letter);
          }

          if(!opoutput[opnum]){
            oporder[ops++] = opnum;
          }
          opoutput[opnum] = 1;

          ptr = endptr;
          c = *ptr;
        }
        /* % followed by a digit outputs an operand the default way. */
        else if(ISDIGIT (*ptr)){
          unsigned long opnum;
          char *endptr;

          opnum = strtoul(ptr, &endptr, 10);
          hexagon_output_operand(f, final_info->insn_ops[opnum], 0);

          if(!opoutput[opnum]){
            oporder[ops++] = opnum;
          }
          opoutput[opnum] = 1;

          ptr = endptr;
          c = *ptr;
        }
        else {
          output_operand_lossage("invalid %%-code");
        }
        break;

      default:
        putc (c, f);
    }
  }

  /* End packet. */
  if(final_info->print_endloop0){
    fputs("}:endloop0 // start=", f);
    output_asm_label(final_info->endloop_label);
  }
  else if(final_info->print_endloop1){
    if(final_info->endloop0){
      fputc(' ', f);
    }
    else {
      fputc('}', f);
    }
    fputs(":endloop1 // start=", f);
    output_asm_label(final_info->endloop_label);
  }
  else if(final_info->end_packet){
    fputs("\n\t}", f);
  }

  if(final_info->print_falign){
    fputs("\n\t.falign", f);
  }

  return ptr;
}




/* Implements macro FINAL_PRESCAN_INSN

   Looks at the current and next insns to determine how to format the next insn
   to be printed and whether or not to print open or close curly brackets in
   order to begin or end a packet. */

void
hexagon_final_prescan_insn(
  rtx insn,
  rtx *ops,
  int numops ATTRIBUTE_UNUSED
)
{
  static struct hexagon_packet_info *current_packet = NULL;
  static int current_insn = 0;

  struct hexagon_final_info *final_info;
  int i;

  if(!TARGET_PACKETS){
    return;
  }

  final_info = &cfun->machine->final_info;

  final_info->duplex = (get_attr_duplex(insn) == DUPLEX_YES);
    
  final_info->insn_ops = ops;
  final_info->start_packet = false;
  final_info->end_packet = false;
  final_info->indent_insn = true;
  final_info->print_insn = true;
  final_info->print_endloop0 = false;
  final_info->print_endloop1 = false;
  final_info->print_falign = false;
  final_info->dot_new_gpr_p = false;
  final_info->dot_new_predicate_p = false;

  gcc_assert(hexagon_head_packet && hexagon_head_packet->num_insns > 0);

  /* If CURRENT_PACKET is NULL, then we are at the start of a new function. */
  if(!current_packet){
    current_packet = hexagon_head_packet;
    current_insn = 0;
  }

  /* Skip ASM_INPUTs. */
  while(GET_CODE (PATTERN (current_packet->insns[current_insn]->insn))
        == ASM_INPUT){
    /* Advance to the next insn. */
    current_insn++;
    if(current_insn == current_packet->num_insns){
      /* Advance to the next packet. */
      current_packet = current_packet->next;
      current_insn = 0;
    }
    gcc_assert(current_packet);
  }

  if(!INSN_P (insn) || get_attr_type(insn) == TYPE_MULTIPLE){
    final_info->indent_insn = false;
  }

  /* Skip over any insns not considered part of a packet. */
  if(insn != current_packet->insns[current_insn]->insn){
    return;
  }

  if(HEXAGON_NEW_PREDICATE_P (current_packet->insns[current_insn])){
    final_info->dot_new_predicate_p = true;
  }
  if(HEXAGON_NEW_GPR_P (current_packet->insns[current_insn])){
    final_info->dot_new_gpr_p = true;
  }

  /* If this is the first insn in a packet, then start the packet. */
  if(current_insn == 0){
    final_info->start_packet = true;
    final_info->endloop0 = false;
  }

  /* Print endloops specially instead of using the template in the machine
     description. */
  if(INSN_CODE (insn) == CODE_FOR_endloop0){
    /* Record that this packet ends an inner hardware loop. */
    final_info->endloop0 = true;
    final_info->indent_insn = false;
    final_info->print_insn = false;
    final_info->print_endloop0 = true;
    final_info->endloop_label = ops[0];
  }
  if(INSN_CODE (insn) == CODE_FOR_endloop1){
    final_info->indent_insn = false;
    final_info->print_insn = false;
    final_info->print_endloop1 = true;
    final_info->endloop_label = ops[0];
  }

  /* If we are fetch-aligning packets following calls, and this is the last insn
     in the current packet, and this is not the end of the function, and the
     next insn is not already an .falign, and the current packet contains a
     call, then print an .falign directive after the current packet. */
  if(hexagon_falign == HEXAGON_FALIGN_ALL
     && current_insn + 1 == current_packet->num_insns
     && current_packet->next
     && INSN_CODE (current_packet->next->insns[0]->insn) != CODE_FOR_falign){
    for(i = 0; i < current_packet->num_insns; i++){
      if(HEXAGON_CALL_P (current_packet->insns[i])
         || HEXAGON_EMULATION_CALL_P (current_packet->insns[i])){
        final_info->print_falign = true;
        break;
      }
    }
  }

  /* Advance to the next insn. */
  current_insn++;

  /* If this is the last insn in a packet, then end the packet. */
  if(current_insn == current_packet->num_insns){
    final_info->end_packet = true;

    /* Advance to the next packet. */
    current_packet = current_packet->next;
    current_insn = 0;
  }

  /* If this is not actually a packet but a sequence of serial instructions,
     then it should not be grouped with any other insns, and it should not
     have curly brackets printed around it. */
  if(get_attr_type(insn) == TYPE_MULTIPLE){
    final_info->print_insn = true;
    final_info->indent_insn = false;
    final_info->start_packet = false;
    final_info->end_packet = false;
    final_info->print_endloop0 = false;
    final_info->print_endloop1 = false;
  }

  /* If there is no next packet, then we are done with the current function. */
  if(!current_packet){
    hexagon_free_packing_info(false);
  }
}




/* globals used to pass information from hexagon_print_operand to
   hexagon_print_operand_address */

/* whether the current operand contains an extended constant */
static bool hexagon_extended_constant;

/* the mode of the current address being printed */
static enum machine_mode hexagon_address_mode;

/* Implements macro PRINT_OPERAND */

void
hexagon_print_operand(FILE *stream, const_rtx x, int code)
{
  hexagon_extended_constant = false;

  switch(code){
    case 'P':
      /* Output a register pair. */
      if(G_REG_P (x) && REGNO (x) % 2 == 0){
        fprintf(stream, "%s:%d", reg_names[REGNO (x) + 1], REGNO (x));
      }
      else {
        output_operand_lossage("hexagon_print_operand: invalid operand for %%P");
      }
      return;

    case 'H':
      /* Output the second register of a register pair. */
      if(G_REG_P (x) && REGNO (x) % 2 == 0){
        fputs(reg_names[REGNO (x) + 1], stream);
      }
      else {
        output_operand_lossage("hexagon_print_operand: invalid operand for %%H");
      }
      return;

    case 'L':
      /* Output the first register of a register pair. */
      if(G_REG_P (x) && REGNO (x) % 2 == 0){
        fputs(reg_names[REGNO (x)], stream);
      }
      else {
        output_operand_lossage("hexagon_print_operand: invalid operand for %%L");
      }
      return;

    case 'C':
    case 'I':
      if((GET_CODE (x) == NE || GET_CODE (x) == EQ)
         && P_REG_P (XEXP (x, 0)) && XEXP (x, 1) == const0_rtx){
        if((GET_CODE (x) == EQ) ^ (code == 'I')){
          fputc('!', stream);
        }
        fputs(reg_names[REGNO (XEXP (x, 0))], stream);
        if(cfun->machine->final_info.dot_new_predicate_p){
          fputs(".new", stream);
        }
      }
      else {
        if(code == 'C'){
          output_operand_lossage("hexagon_print_operand: invalid operand for %%C");
        }
        else {
          output_operand_lossage("hexagon_print_operand: invalid operand for %%I");
        }
      }
      return;

    case 'h':
      /* Output a branch hint if the current insn is predicated on a newly
         generated predicate or a compare with a newly generated value. */
      if(GET_CODE (x) == CONST_INT){
        if(   cfun->machine->final_info.dot_new_gpr_p
           || cfun->machine->final_info.dot_new_predicate_p){
          if(INTVAL (x)){
            fputs(":t", stream);
          }
          else {
            fputs(":nt", stream);
          }
        }
      }
      else {
        output_operand_lossage("hexagon_print_operand: invalid operand for %%h");
      }
      return;

    case 'J':
      {
        int log = exact_log2(INTVAL (x) & 0xFFFFFFFFULL);
        if(log == -1){
          output_operand_lossage("hexagon_print_operand: invalid operand for %%J");
        }
        else {
          fprintf(stream, "%d", log);
        }
      }
      return;

    case 'K':
      {
        int log = exact_log2(~INTVAL (x) & 0xFFFFFFFFULL);
        if(log == -1){
          output_operand_lossage("hexagon_print_operand: invalid operand for %%K");
        }
        else {
          fprintf(stream, "%d", log);
        }
      }
      return;

    case 'E':
      gcc_assert(TARGET_V4_FEATURES);
      hexagon_extended_constant = true;
      /* handled below */
      break;

    case 0:
      /* handled below */
      break;

    default:
      output_operand_lossage("hexagon_print_operand: unknown code, 0x%x", code);
      return;
  }

  switch(GET_CODE (x)){
    case REG:
      {
        if(REGNO (x) < FIRST_PSEUDO_REGISTER){
          if(G_REG_P (x) && GET_MODE_SIZE (GET_MODE (x)) > UNITS_PER_WORD){
            fprintf(stream, "%s:%d", reg_names[REGNO (x) + 1], REGNO (x));
          }
          else {
            fputs(reg_names[REGNO (x)], stream);
          }
        }
        else {
          output_operand_lossage("hexagon_print_operand: invalid register");
        }
      }
      return;

    case MEM:
      hexagon_address_mode = GET_MODE (x);
      output_address(XEXP (x, 0));
      return;

    case CONST_INT:
      if(INTVAL (x) < -0xFFFFFFFFLL){
        fprintf(stream, HOST_WIDE_INT_PRINT_HEX, INTVAL (x));
      }
      else {
        fprintf(stream, HOST_WIDE_INT_PRINT_DEC, INTVAL (x));
      }
      return;

    case CONST_DOUBLE:
      if(GET_MODE (x) == SFmode){
        REAL_VALUE_TYPE rv;
        long l;

        REAL_VALUE_FROM_CONST_DOUBLE (rv, x);
        REAL_VALUE_TO_TARGET_SINGLE (rv, l);
        l &= 0xFFFFFFFFUL;
        fprintf(stream, "0x%08lx", l);
        return;
      }
      else if(GET_MODE (x) == DFmode){
        REAL_VALUE_TYPE rv;
        long l[2];

        REAL_VALUE_FROM_CONST_DOUBLE (rv, x);
        REAL_VALUE_TO_TARGET_DOUBLE (rv, l);
        l[0] &= 0xFFFFFFFFUL;
        l[1] &= 0xFFFFFFFFUL;
        fprintf(stream, "0x%08lx%08lx", l[1], l[0]);
        return;
      }
      /* FALL THROUGH.  Let output_addr_const deal with it. */

    default:
      output_addr_const(stream, x);
      break;
  }
}




/* Implements macro PRINT_OPERAND_ADDRESS

   Print a memory address as an operand to reference that memory location. */

void
hexagon_print_operand_address(FILE *stream, const_rtx x)
{
  switch(GET_CODE (x)){
    case REG:
      if(G_REG_P (x)){
        fputs(reg_names[REGNO (x)], stream);
        fputs("+#0", stream);
      }
      else {
        output_operand_lossage("hexagon_print_operand_address: invalid base register");
      }
      break;

    case PLUS:
      {
        rtx base = XEXP (x, 0);
        rtx offset = XEXP (x, 1);
        rtx index = NULL_RTX;
        rtx scale = NULL_RTX;

        if(!(REG_P (base)
             || (CONSTANT_P (base) && GET_CODE (base) != CONST_INT))
           || (CONSTANT_P (offset) && GET_CODE (offset) != CONST_INT)){
          base = XEXP (x, 1);
          offset = XEXP (x, 0);
        }
        if(GET_CODE (offset) == MULT || GET_CODE (offset) == ASHIFT){
          index = XEXP (offset, 0);
          scale = XEXP (offset, 1);
          if(!REG_P (index)){
            index = XEXP (offset, 1);
            scale = XEXP (offset, 0);
          }
        }

        if(G_REG_P (base)){
          fprintf(stream, "%s", reg_names[REGNO (base)]);
          fputc('+', stream);
        }
        else if(!CONSTANT_P (base)){
          output_operand_lossage("hexagon_print_operand_address: invalid base+index base");
          break;
        }

        if(CONSTANT_P (offset)){
          fputc('#', stream);
          if(hexagon_extended_constant){
            fputc('#', stream);
          }
          output_addr_const(stream, offset);
        }
        else if(REG_P (offset)){
          fprintf(stream, "%s<<#0", reg_names[REGNO (offset)]);
        }
        else if(   GET_CODE (offset) == MULT
                && REG_P (index)
                && GET_CODE (scale) == CONST_INT){
          int log = exact_log2(INTVAL (scale) & 0xFFFFFFFFULL);
          if(log == -1){
            output_operand_lossage("hexagon_print_operand_address: invalid base+index scale amount");
          }
          else {
            fprintf(stream, "%s<<#%d", reg_names[REGNO (index)], log);
          }
        }
        else if(   GET_CODE (offset) == ASHIFT
                && REG_P (index)
                && GET_CODE (scale) == CONST_INT){
          fprintf(stream, "%s<<#" HOST_WIDE_INT_PRINT_DEC, reg_names[REGNO (index)], INTVAL (scale));
        }
        else {
          output_operand_lossage("hexagon_print_operand_address: invalid base+index index");
        }

        if(CONSTANT_P (base)){
          fputc('+', stream);
          fputc('#', stream);
          if(hexagon_extended_constant){
            fputc('#', stream);
          }
          output_addr_const(stream, base);
        }
        break;
      }

    case POST_INC:
      if(G_REG_P (XEXP (x, 0))){
        fprintf(stream, "%s++#%d", reg_names[REGNO (XEXP (x, 0))], GET_MODE_SIZE (hexagon_address_mode));
      }
      else {
        output_operand_lossage("hexagon_print_operand_address: invalid post increment base register");
      }
      break;

    case POST_DEC:
      if(G_REG_P (XEXP (x, 0))){
        fprintf(stream, "%s++#-%d", reg_names[REGNO (XEXP (x, 0))], GET_MODE_SIZE (hexagon_address_mode));
      }
      else {
        output_operand_lossage("hexagon_print_operand_address: invalid post decrement base register");
      }
      break;

    case POST_MODIFY:
      {
        rtx basereg = XEXP (x, 0);
        rtx mod = XEXP (x, 1);
        if(G_REG_P (XEXP (x, 0))){
          fprintf(stream, "%s++#" HOST_WIDE_INT_PRINT_DEC, reg_names[REGNO (basereg)], INTVAL (XEXP (mod, 1)));
        }
        else {
          output_operand_lossage("hexagon_print_operand_address: invalid post modify base register");
        }
      }
      break;

    case SYMBOL_REF:
    case CONST:
    case CONST_INT:
    case LABEL_REF:
      if(sdata_symbolic_operand(x, Pmode) && !hexagon_extended_constant){
        fputc('#', stream);
      }
      else if(CONSTANT_P (x)){
        fputs("##", stream);
      }
      output_addr_const(stream, x);
      break;

    default:
      output_operand_lossage("hexagon_print_operand_address: invalid address code 0x%x", GET_CODE (x));
      break;
  }
}




/*----------------------
Miscellaneous Parameters
----------------------*/

static void
hexagon_fixup_cfg(void)
{
  basic_block bb;
  rtx head_insn;
  rtx end_insn;
  rtx insn;

  FOR_EACH_BB(bb){
    head_insn = BB_HEAD (bb);
    end_insn = BB_END (bb);
    insn = end_insn;
    while(insn && NEXT_INSN (insn) != head_insn){
      if(control_flow_insn_p(insn)){
        if(insn != end_insn){
          if(PREV_INSN (insn)){
            NEXT_INSN (PREV_INSN (insn)) = NEXT_INSN (insn);
          }
          PREV_INSN (NEXT_INSN (insn)) = PREV_INSN (insn);
          PREV_INSN (insn) = end_insn;
          NEXT_INSN (insn) = NEXT_INSN (end_insn);
          NEXT_INSN (end_insn) = insn;
          if(NEXT_INSN (insn)){
            PREV_INSN (NEXT_INSN (insn)) = insn;
          }
          BB_END (bb) = insn;
        }
        break;
      }
      insn = PREV_INSN (insn);
    }
  }
}

/* If this is HW loop, we should not allow 
   to unroll it forcefullt */ 

bool
hexagon_loop_invalid_for_forced_unroll(rtx tail){

    int tail_code;

    if(!tail)   return false;

    if(!INSN_P (tail)){
        tail = prev_real_insn(tail);
    }

    if(tail){ 
        tail_code = recog_memoized(tail);

        if(tail_code == CODE_FOR_endloop0
           || tail_code == CODE_FOR_endloop1)
          return true;
    }

    return false;
}


/* ggan:
 * Called in sms_schedule(), after loop_version.
 */
void
hexagon_duplicate_doloop_begin(basic_block condition_bb, struct loop *loop)
{
    
    edge true_edge = NULL;
    edge false_edge  = NULL;
    rtx begin_loop_insn = NULL; 
    rtx end_loop_insn = NULL;
    rtx insn = NULL;
    int opcode = 0;
    int begin_tag = 0;
    int end_tag = 0;
    rtx new_begin_loop_insn = NULL;

    gcc_assert (condition_bb != NULL);

    /* Get TRUE edge and FALSE edge of the cond bb */
    extract_cond_bb_edges (condition_bb, &true_edge, &false_edge);

    gcc_assert (true_edge != NULL);
    gcc_assert (false_edge != NULL);

    /* Get the bb that has the doloop_begin insn */
    basic_block loop_setup_bb = single_pred (condition_bb);

    /* Get the loop body bb of the duplicated loop. Because it is a 
     * single bb loop, so loop header bb is the loop body
     */
    basic_block new_loop_header = get_bb_copy (loop->header);
    
    /* Get the preheader bb of the duplicated loop */
    basic_block new_loop_preheader = false_edge->dest;
   
    /* find out the endloop0 insn */
    FOR_BB_INSNS_REVERSE(new_loop_header, insn) 
    {
        if (!INSN_P (insn)) continue;
            
        opcode = recog_memoized(insn);

        /* SWP is only performed on Single BB Loop.
         * It is not possible to have nested loops
         */
        if (opcode == CODE_FOR_endloop0)
        {
            end_loop_insn = insn;
            break;
        }
    }		

    gcc_assert (end_loop_insn != NULL);

    /* find out the loop0 insn */
    FOR_BB_INSNS_REVERSE(loop_setup_bb, insn) 
    {
        if (!INSN_P (insn)) continue;

        if (INSN_CODE (insn) == CODE_FOR_doloop_begin0)
        {
            begin_loop_insn = insn;
            break;
        } 
    }

    gcc_assert (begin_loop_insn != NULL);

    /* extract the tag for the original doloop */
    begin_tag = INTVAL (SET_SRC (XVECEXP (PATTERN (begin_loop_insn), 0, 1)));
    end_tag = INTVAL (XVECEXP (XVECEXP (PATTERN (end_loop_insn), 0, 2), 0, 1));
    gcc_assert (begin_tag == end_tag);

    /* insert the copy of the loop0 insn into the new preheader bb */
    new_begin_loop_insn = emit_copy_of_insn_after (begin_loop_insn, BB_END(new_loop_preheader));

#define DOLOOP_TAG_OFFSET   100000

    /* adjust the tag to make sure it is unique 
     * currently, we just offset the original tag by 100000
     */
    SET_SRC (XVECEXP (PATTERN (new_begin_loop_insn), 0, 1)) = GEN_INT (end_tag + DOLOOP_TAG_OFFSET);
    XVECEXP (XVECEXP (PATTERN (end_loop_insn), 0, 2), 0, 1) = GEN_INT (end_tag + DOLOOP_TAG_OFFSET);

    return;              
}


static void
hexagon_fixup_doloops(void)
{
  basic_block bb;
  rtx tail;
  rtx insn;
  rtx label;
  rtx loop_count;
  rtx clobber_reg;
  rtx loop_setup_insn;
  HOST_WIDE_INT tag;
  int tail_code;
  int loop_setup_code;
  rtx (*gen_loop_setup)(rtx, rtx);

  if(dump_file){
    fprintf(dump_file, ";; hexagon org loops starting\n");
  }

  FOR_EACH_BB (bb){
    tail = BB_END (bb);

    if(!INSN_P (tail)){
      tail = prev_real_insn(tail);
      if(tail == NULL_RTX){
	continue;
      }

    }

    tail_code = recog_memoized(tail);

    if(tail_code == CODE_FOR_endloop0 || tail_code == CODE_FOR_endloop1){
      label = XEXP (XEXP (SET_SRC (XVECEXP (PATTERN (tail), 0, 0)), 1), 0);
      tag = INTVAL (XVECEXP (XVECEXP (PATTERN (tail), 0, 2), 0, 1));
      if(tail_code == CODE_FOR_endloop0){
        loop_setup_code = CODE_FOR_doloop_begin0;
        gen_loop_setup = &gen_loop0;
      }
      else {
        loop_setup_code = CODE_FOR_doloop_begin1;
        gen_loop_setup = &gen_loop1;
      }
      /* ??? improve efficiency */
      for(insn = get_insns(); insn; insn = NEXT_INSN (insn)){
        if(active_insn_p(insn)
           && INSN_CODE (insn) == loop_setup_code
           && INTVAL (SET_SRC (XVECEXP (PATTERN (insn), 0, 1))) == tag){
          basic_block bb;
          loop_count = SET_SRC (XVECEXP (PATTERN (insn), 0, 0));
          clobber_reg = XEXP (XVECEXP (PATTERN (insn), 0, 2), 0);
          loop_setup_insn = gen_loop_setup(loop_count, label);
          XEXP (XVECEXP (loop_setup_insn, 0, 2), 0) = clobber_reg;
          FOR_EACH_BB (bb) if(BB_END (bb) == insn) break;
/*
          fprintf(stderr, "\ninsn:\n");
          debug_rtx(insn);
          fprintf(stderr, "\nbasic block:\n");
          debug_bb(bb);
          fprintf(stderr, "\nBB_END:\n");
          debug_rtx(BB_END (bb));
*/

          loop_setup_insn = emit_insn_before(loop_setup_insn, insn);

/*
          tail_code = recog_memoized(loop_setup_insn);  
          LABEL_START_LOOP(label) = 1;

          fprintf(stderr, "\nloop setup insn:\n");
          debug_rtx(loop_setup_insn);
          fprintf(stderr, "\nbasic block:\n");
          debug_bb(bb);
          fprintf(stderr, "\nBB_END:\n");
          debug_rtx(BB_END (bb));
          fprintf(stderr, "\n**DELETE**\n");
*/
          delete_insn(insn);
/*
          fprintf(stderr, "\nbasic block:\n");
          debug_bb(bb);
          fprintf(stderr, "\nBB_END:\n");
          debug_rtx(BB_END (bb));
*/
        }
      }
    }
  }

}




static void
hexagon_insert_faligns(void)
{
  rtx insn;
  rtx next;
  rtx label;

  if(hexagon_falign == HEXAGON_FALIGN_LABELS || hexagon_falign == HEXAGON_FALIGN_ALL){
    for(insn = get_insns(); insn; insn = NEXT_INSN (insn)){
      if(LABEL_P (insn)){
        if(!(next = next_real_insn(insn))){
          break;
        }
        if(!JUMP_TABLE_DATA_P (next)){
          emit_insn_before(gen_falign(), insn);
        }
        insn = next;
      }
    }
  }
  else if(hexagon_falign == HEXAGON_FALIGN_LOOPS){

    /* Go backwards and falign only labels that are targets for backward
       jumps. */
    for(insn = get_last_insn(); insn; insn = PREV_INSN (insn)){
      if(JUMP_P (insn)){
        /* If label first seen in jump, mark it */
        label = JUMP_LABEL (insn);
        if(label){
          LABEL_START_LOOP (label) = 1;
        }
      }
      else if(LABEL_P (insn)){
        if(LABEL_START_LOOP (insn)
           && !JUMP_TABLE_DATA_P (next_real_insn(insn))){
          emit_insn_before(gen_falign(), insn);
        }
      }
    }
  }
}




/* Implements hook TARGET_MACHINE_DEPENDENT_REORG */

static void
hexagon_machine_dependent_reorg(void)
{
  compute_bb_for_insn();

#if 0
  verify_flow_info();
#endif /* 0 */

  if(cfun->machine->has_hardware_loops
     || TARGET_PACKET_OPTIMIZATIONS){
    hexagon_fixup_cfg();
  }

  if (TARGET_LOCAL_COMBINE) 
    {
      hexagon_local_combine_pass();
    }

  if(TARGET_PACKET_OPTIMIZATIONS){
    hexagon_packet_optimizations();
  }

  /* doloop fixups */
  if(cfun->machine->has_hardware_loops){
    hexagon_fixup_doloops();
  }
  
  /* Insert .faligns. */
  if(hexagon_falign != HEXAGON_NO_FALIGN){
    hexagon_insert_faligns();
  }

#if 0
  verify_flow_info();
#endif /* 0 */
}

static GTY(()) tree hexagon_builtins[(int) CODE_FOR_nothing];



#define def_builtin(NAME, TYPE, CODE) \
  do { \
    tree t; \
    t = add_builtin_function(NAME, TYPE, END_BUILTINS + 1 + CODE, \
                             BUILT_IN_MD, NULL, \
                             tree_cons(get_identifier("const"), \
                                       NULL_TREE, NULL_TREE));  \
    hexagon_builtins[(int) END_BUILTINS + 1 + CODE] = t; \
    if (CODE == HEXAGON_BUILTIN_val_for_valignb) { \
      hexagon_builtin_mask_for_load = t; \
    } \
  } while (0);
#define def_builtin_nonconst(NAME, TYPE, CODE) \
  do { \
    tree t; \
    t = add_builtin_function(NAME, TYPE, END_BUILTINS + 1 + CODE, \
                             BUILT_IN_MD, NULL, NULL_TREE);  \
    if (CODE == HEXAGON_BUILTIN_val_for_valignb) { \
      hexagon_builtin_mask_for_load = t; \
    } \
  } while (0);

#define PTR_type_node ptr_type_node
#define BI_type_node boolean_type_node
#define QI_type_node char_type_node
#define HI_type_node short_integer_type_node
#define SI_type_node integer_type_node
#define USI_type_node unsigned_type_node
#define DI_type_node long_long_integer_type_node
#define UDI_type_node long_long_unsigned_type_node

/* Implements hook TARGET_INIT_BUILTINS */

static void
hexagon_init_builtins(void)
{
  tree endlink ATTRIBUTE_UNUSED;
  tree QI_ftype_MEM      ATTRIBUTE_UNUSED;
  tree void_ftype_SI     ATTRIBUTE_UNUSED;
  tree void_ftype_SISI   ATTRIBUTE_UNUSED;
  tree void_ftype_SISISI ATTRIBUTE_UNUSED;
  tree HI_ftype_SI       ATTRIBUTE_UNUSED;
  tree SI_ftype_SI       ATTRIBUTE_UNUSED;
  tree SI_ftype_SISI     ATTRIBUTE_UNUSED;
  tree USI_ftype_SISI    ATTRIBUTE_UNUSED;
  tree SI_ftype_SISISI   ATTRIBUTE_UNUSED;
  tree DI_ftype_SI       ATTRIBUTE_UNUSED;
  tree DI_ftype_SISI     ATTRIBUTE_UNUSED;
  tree UDI_ftype_SISI    ATTRIBUTE_UNUSED;
  tree DI_ftype_SIDI     ATTRIBUTE_UNUSED;
  tree DI_ftype_SISISI   ATTRIBUTE_UNUSED;
  tree SI_ftype_DI       ATTRIBUTE_UNUSED;
  tree SI_ftype_DISI     ATTRIBUTE_UNUSED;
  tree SI_ftype_DISISI   ATTRIBUTE_UNUSED;
  tree DI_ftype_DI       ATTRIBUTE_UNUSED;
  tree DI_ftype_DISI     ATTRIBUTE_UNUSED;
  tree DI_ftype_DISISI   ATTRIBUTE_UNUSED;
  tree SI_ftype_SIDI     ATTRIBUTE_UNUSED;
  tree SI_ftype_DIDI     ATTRIBUTE_UNUSED;
  tree DI_ftype_DIDI     ATTRIBUTE_UNUSED;
  tree UDI_ftype_DIDI    ATTRIBUTE_UNUSED;
  tree SI_ftype_SIDISI   ATTRIBUTE_UNUSED;
  tree DI_ftype_DIDISI   ATTRIBUTE_UNUSED;
  tree SI_ftype_SIDIDI   ATTRIBUTE_UNUSED;
  tree DI_ftype_DIDIDI   ATTRIBUTE_UNUSED;
  tree SI_ftype_SISISISI ATTRIBUTE_UNUSED;
  tree DI_ftype_DIDISISI ATTRIBUTE_UNUSED;
  tree SI_ftype_SISIDI   ATTRIBUTE_UNUSED;

  tree QI_ftype_SISI     ATTRIBUTE_UNUSED;
  tree QI_ftype_SIDI     ATTRIBUTE_UNUSED;
  tree QI_ftype_DISI     ATTRIBUTE_UNUSED;
  tree QI_ftype_DIDI     ATTRIBUTE_UNUSED;
  tree QI_ftype_QI       ATTRIBUTE_UNUSED;
  tree QI_ftype_SI       ATTRIBUTE_UNUSED;
  tree QI_ftype_DI       ATTRIBUTE_UNUSED;
  tree QI_ftype_QIQI     ATTRIBUTE_UNUSED;
  tree QI_ftype_QIQIQI   ATTRIBUTE_UNUSED;
  tree SI_ftype_QIQI     ATTRIBUTE_UNUSED;
  tree SI_ftype_QISISI   ATTRIBUTE_UNUSED;
  tree SI_ftype_QISI     ATTRIBUTE_UNUSED;
  tree DI_ftype_QISISI   ATTRIBUTE_UNUSED;
  tree DI_ftype_QIDIDI   ATTRIBUTE_UNUSED;
  tree DI_ftype_QI       ATTRIBUTE_UNUSED;
  tree SI_ftype_QI       ATTRIBUTE_UNUSED;
  tree DI_ftype_DIDIQI   ATTRIBUTE_UNUSED;

  tree PTR_ftype_PTRPTRSISI   ATTRIBUTE_UNUSED;

  tree PTR_ftype_PTRDISISI   ATTRIBUTE_UNUSED;
  tree PTR_ftype_PTRSISISI   ATTRIBUTE_UNUSED;
  tree PTR_ftype_PTRHISISI   ATTRIBUTE_UNUSED;
  tree PTR_ftype_PTRQISISI   ATTRIBUTE_UNUSED;

  tree PTR_ftype_PTRPTRSI   ATTRIBUTE_UNUSED;

  tree PTR_ftype_PTRDISI   ATTRIBUTE_UNUSED;
  tree PTR_ftype_PTRSISI   ATTRIBUTE_UNUSED;
  tree PTR_ftype_PTRHISI   ATTRIBUTE_UNUSED;
  tree PTR_ftype_PTRQISI   ATTRIBUTE_UNUSED;

  endlink = void_list_node;
  QI_ftype_MEM =      build_function_type( QI_type_node,
                        tree_cons(NULL_TREE, ptr_type_node,
                        endlink));
  void_ftype_SI =     build_function_type( void_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink));
  void_ftype_SISI =   build_function_type( void_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink)));
  void_ftype_SISISI = build_function_type( void_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink))));
  HI_ftype_SI =       build_function_type(   HI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink));
  SI_ftype_SI =       build_function_type(   SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink));
  SI_ftype_SISI =     build_function_type(   SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink)));
  USI_ftype_SISI =    build_function_type(  USI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink)));
  SI_ftype_QIQI =     build_function_type(   SI_type_node,
                        tree_cons(NULL_TREE, QI_type_node,
                        tree_cons(NULL_TREE, QI_type_node,
                        endlink)));
  SI_ftype_SISISI =   build_function_type(   SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink))));
  DI_ftype_SI =       build_function_type(   DI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink));
  DI_ftype_SISI =     build_function_type(   DI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink)));
  UDI_ftype_SISI =    build_function_type(  UDI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink)));
  DI_ftype_SISISI =   build_function_type(   DI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink))));
  DI_ftype_SIDI =     build_function_type(   DI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        endlink)));
  SI_ftype_DI =       build_function_type(   SI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        endlink));
  SI_ftype_DISI =     build_function_type(   SI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink)));
  SI_ftype_DISISI =   build_function_type(   SI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink))));
  DI_ftype_DI =       build_function_type(   DI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        endlink));
  DI_ftype_DISI =     build_function_type(   DI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink)));
  DI_ftype_DISISI =   build_function_type(   DI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink))));
  SI_ftype_SIDI =     build_function_type(   SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        endlink)));
  SI_ftype_DIDI =     build_function_type(   SI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        endlink)));
  DI_ftype_DIDI =     build_function_type(   DI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        endlink)));
  UDI_ftype_DIDI =    build_function_type(  UDI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        endlink)));
  SI_ftype_SIDISI =   build_function_type(   SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink))));
  DI_ftype_DIDISI =   build_function_type(   DI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink))));
  SI_ftype_SIDIDI =   build_function_type(   SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        endlink))));
  DI_ftype_DIDIDI =   build_function_type(   DI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        endlink))));
  SI_ftype_SISISISI = build_function_type(   SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink)))));
  DI_ftype_DIDISISI = build_function_type(   DI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink)))));
  SI_ftype_SISIDI =   build_function_type(   SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        endlink))));

  QI_ftype_SISI   =   build_function_type(   QI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink)));

  QI_ftype_SIDI   =   build_function_type(   QI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        endlink)));

  QI_ftype_DISI   =   build_function_type(   QI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink)));

  QI_ftype_DIDI   =   build_function_type(   QI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        endlink)));

  QI_ftype_QI     =   build_function_type(   QI_type_node,
                        tree_cons(NULL_TREE, QI_type_node,
                        endlink));

  QI_ftype_SI     =   build_function_type(   QI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink));

  QI_ftype_DI     =   build_function_type(   QI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        endlink));

  QI_ftype_QIQI   =   build_function_type(   QI_type_node,
                        tree_cons(NULL_TREE, QI_type_node,
                        tree_cons(NULL_TREE, QI_type_node,
                        endlink)));

  QI_ftype_QIQIQI =   build_function_type(   QI_type_node,
                        tree_cons(NULL_TREE, QI_type_node,
                        tree_cons(NULL_TREE, QI_type_node,
                        tree_cons(NULL_TREE, QI_type_node,
                        endlink))));

  SI_ftype_QISISI =   build_function_type(   SI_type_node,
                        tree_cons(NULL_TREE, QI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink))));

  SI_ftype_QISI   =   build_function_type(   SI_type_node,
                        tree_cons(NULL_TREE, QI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink)));

  DI_ftype_QISISI =   build_function_type(   DI_type_node,
                        tree_cons(NULL_TREE, QI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink))));

  DI_ftype_QIDIDI =   build_function_type(   DI_type_node,
                        tree_cons(NULL_TREE, QI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        endlink))));

  DI_ftype_QI     =   build_function_type(   DI_type_node,
                        tree_cons(NULL_TREE, QI_type_node,
                        endlink));

  SI_ftype_QI     =   build_function_type(   SI_type_node,
                        tree_cons(NULL_TREE, QI_type_node,
                        endlink));

  DI_ftype_DIDIQI =   build_function_type(   DI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        tree_cons(NULL_TREE, QI_type_node,
                        endlink))));

  PTR_ftype_PTRPTRSISI =   build_function_type(   PTR_type_node,
                        tree_cons(NULL_TREE, PTR_type_node,
                        tree_cons(NULL_TREE, PTR_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink)))));

  PTR_ftype_PTRDISISI =   build_function_type(   PTR_type_node,
                        tree_cons(NULL_TREE, PTR_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink)))));

  PTR_ftype_PTRSISISI =   build_function_type(   PTR_type_node,
                        tree_cons(NULL_TREE, PTR_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink)))));

  PTR_ftype_PTRHISISI =   build_function_type(   PTR_type_node,
                        tree_cons(NULL_TREE, PTR_type_node,
                        tree_cons(NULL_TREE, HI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink)))));

  PTR_ftype_PTRQISISI =   build_function_type(   PTR_type_node,
                        tree_cons(NULL_TREE, PTR_type_node,
                        tree_cons(NULL_TREE, QI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink)))));

  PTR_ftype_PTRPTRSI =   build_function_type(   PTR_type_node,
                        tree_cons(NULL_TREE, PTR_type_node,
                        tree_cons(NULL_TREE, PTR_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink))));

  PTR_ftype_PTRDISI =   build_function_type(   PTR_type_node,
                        tree_cons(NULL_TREE, PTR_type_node,
                        tree_cons(NULL_TREE, DI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink))));

  PTR_ftype_PTRSISI =   build_function_type(   PTR_type_node,
                        tree_cons(NULL_TREE, PTR_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink))));

  PTR_ftype_PTRHISI =   build_function_type(   PTR_type_node,
                        tree_cons(NULL_TREE, PTR_type_node,
                        tree_cons(NULL_TREE, HI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink))));

  PTR_ftype_PTRQISI =   build_function_type(   PTR_type_node,
                        tree_cons(NULL_TREE, PTR_type_node,
                        tree_cons(NULL_TREE, QI_type_node,
                        tree_cons(NULL_TREE, SI_type_node,
                        endlink))));

#define BUILTIN_INFO(TAG, TYPE, NARGS) \
  def_builtin("__builtin_" #TAG, TYPE, HEXAGON_BUILTIN_##TAG);
#define BUILTIN_INFO_NONCONST(TAG, TYPE, NARGS) \
  def_builtin_nonconst("__builtin_" #TAG, TYPE, HEXAGON_BUILTIN_##TAG);
#include "builtins.def"
#include "manual_builtins.def"
#undef BUILTIN_INFO
#undef BUILTIN_INFO_NONCONST

  gcc_assert(hexagon_builtin_mask_for_load);
}

static tree
hexagon_builtin_decl (unsigned code, bool initialize_p ATTRIBUTE_UNUSED)
{
  if (code >= CODE_FOR_nothing)
    return error_mark_node;

  return hexagon_builtins[code];
}



/* Helper function for hexagon_expand_builtin */

static rtx
expand_one_builtin(enum insn_code icode, rtx target, tree exp, int nargs)
{
  int i;
  rtx patrick; /* maybe he doesn't like being called "pat" */
  tree arg[5];
  rtx op[5];
  enum machine_mode mode[5];
  enum machine_mode tmode;
  int opi;
  tmode = insn_data[icode].operand[0].mode;
  opi = insn_data[icode].operand[0].constraint[0] == '=' ? 1 : 0;
  for(i = 0; i < nargs; i++) {
    arg[i] = CALL_EXPR_ARG (exp, i);
    mode[i] = insn_data[icode].operand[opi + i].mode;
    op[i] = expand_expr(arg[i], NULL_RTX, mode[i], 0);
    if(!(*insn_data[icode].operand[opi + i].predicate)(op[i], mode[i])){
      op[i] = copy_to_mode_reg(mode[i], op[i]);
    }
    if(GET_CODE (op[i]) == CONST_INT){
      /* do nothing */
    }
    else if(GET_MODE (op[i]) != mode[i]){
      abort();
    }
    if(!(*insn_data[icode].operand[opi + i].predicate)(op[i], mode[i])){
      copy_to_mode_reg(mode[i], op[i]);
    }
  }
  if(insn_data[icode].operand[0].constraint[0] == '='){
    if(target == 0
       || GET_MODE (target) != tmode
       || !(*insn_data[icode].operand[0].predicate)(target, tmode)){
      target = gen_reg_rtx(tmode);
    }
  }
  else {
    target = 0;
  }
  switch(nargs){
    case 0:
      patrick = GEN_FCN (icode)(target);
      break;
    case 1:
      if(target) {
        patrick = GEN_FCN (icode)(target, op[0]);
      }
      else {
        patrick = GEN_FCN (icode)(op[0]);
      }
      break;
    case 2:
      if(target) {
        patrick = GEN_FCN (icode)(target, op[0], op[1]);
      }
      else {
        patrick = GEN_FCN (icode)(op[0], op[1]);
      }
      break;
    case 3:
      if(target) {
        patrick = GEN_FCN (icode)(target, op[0], op[1], op[2]);
      }
      else {
        patrick = GEN_FCN (icode)(op[0], op[1], op[2]);
      }
      break;
    case 4:
      if(target) {
        patrick = GEN_FCN (icode)(target, op[0], op[1], op[2], op[3]);
      }
      else {
        patrick = GEN_FCN (icode)(op[0], op[1], op[2], op[3]);
      }
      break;
    default:
      abort();
  }
  if(!patrick) {
    /* Oh, Patrick, where have you gone to? */
    return 0;
  }
  emit_insn(patrick);
  return target;
}




/* Implements hook TARGET_EXPAND_BUILTIN */

static rtx
hexagon_expand_builtin(
  tree exp,
  rtx target,
  rtx subtarget ATTRIBUTE_UNUSED,
  enum machine_mode mode ATTRIBUTE_UNUSED,
  int ignore ATTRIBUTE_UNUSED
)
{
  tree fndecl = TREE_OPERAND (CALL_EXPR_FN (exp), 0);
  int fcode = DECL_FUNCTION_CODE (fndecl);
  switch(fcode - (END_BUILTINS + 1)){
#define BUILTIN_INFO(TAG, TYPE, NARGS) \
    case HEXAGON_BUILTIN_##TAG: \
      return expand_one_builtin(CODE_FOR_hexagon_builtin_##TAG, \
                                target, exp, NARGS);
#define BUILTIN_INFO_NONCONST(TAG, TYPE, NARGS) \
    case HEXAGON_BUILTIN_##TAG: \
      return expand_one_builtin(CODE_FOR_hexagon_builtin_##TAG, \
                                target, exp, NARGS);
#include "builtins.def"
#include "manual_builtins.def"
#undef BUILTIN_INFO
#undef BUILTIN_INFO_NONCONST
    default:
      abort();
      break;
  }
}




/* Implements hook TARGET_INVALID_WITHIN_DOLOOP

   Don't form a hardware loop around a call or a set or clobber of a loop
   register. */

static const char *
hexagon_invalid_within_doloop(const_rtx insn)
{
  rtx side_effect;
  rtx parallel;
  rtx reg;
  int i;

  /* Notes and labels are fine. */
  if(!INSN_P (insn)){
    return NULL;
  }

  /* Don't allow calls because the loop registers are call used. */
  if(CALL_P (insn)){
    return "The loop contains a call.";
  }

  i = 0;
  parallel = NULL_RTX;
  /* We can't form a loop around something that changes the loop registers. */
  side_effect = PATTERN (insn);
  switch(GET_CODE (side_effect)){
    case PARALLEL:
      parallel = side_effect;
      for(i = 0; i < XVECLEN (parallel, 0); i++){
        side_effect = XVECEXP (parallel, 0, i);
        if(GET_CODE (side_effect) == SET){
      /* FALL THROUGH */
    case SET:
          reg = SET_DEST (side_effect);
          if(REG_P (reg)){
            switch(REGNO (reg)){
              case LC0_REGNUM:
                return "lc0 is set in the loop.";
              case SA0_REGNUM:
                return "sa0 is set in the loop.";
              case LC1_REGNUM:
                return "lc1 is set in the loop.";
              case SA1_REGNUM:
                return "sa1 is set in the loop.";
              default:
                break;
            }
          }
          if(parallel){
            continue;
          }
          return NULL;
        }
        else if(GET_CODE (side_effect) == CLOBBER){
      /* FALL THROUGH */
    case CLOBBER:
          reg = XEXP (side_effect, 0);
          if(REG_P (reg)){
            switch(REGNO (reg)){
              case LC0_REGNUM:
                return "lc0 is clobbered in the loop.";
              case SA0_REGNUM:
                return "sa0 is clobbered in the loop.";
              case LC1_REGNUM:
                return "lc1 is clobbered in the loop.";
              case SA1_REGNUM:
                return "sa1 is clobbered in the loop.";
              default:
                break;
            }
          }
          if(parallel){
            continue;
          }
          return NULL;
        }
      }
      /* FALL THROUGH */
    default:
      return NULL;
  }
}




/* Helper function for hexagon_print_rtl_pseudo_asm

   (set (pc) (...)) */

static void
hexagon_print_jump(FILE *stream, const_rtx x)
{
  /* (set (pc) (if_then_else (...) (...) (...))) */
  if(x && GET_CODE (x) == SET
     && SET_SRC (x) && GET_CODE (SET_SRC (x)) == IF_THEN_ELSE){
    /* (set (pc) (if_then_else (...) (pc) (...))) */
    if(XEXP (SET_SRC (x), 1) && XEXP (SET_SRC (x), 1) == pc_rtx){
      hexagon_print_condition(stream, XEXP (SET_SRC (x), 0), false);
      /* (set (pc) (if_then_else (...) (pc) (label))) */
      if(GET_CODE (XEXP (SET_SRC (x), 2)) == LABEL_REF){
        fputs("jump", stream);
      }
      else {
        fputs("jump ", stream);
        hexagon_print_rtx(stream, XEXP (SET_SRC (x), 2));
      }
    }
    /* (set (pc) (if_then_else (...) (...) (pc))) */
    else if(XEXP (SET_SRC (x), 2) && XEXP (SET_SRC (x), 2) == pc_rtx){
      hexagon_print_condition(stream, XEXP (SET_SRC (x), 0), true);
      /* (set (pc) (if_then_else (...) (label) (pc))) */
      if(GET_CODE (XEXP (SET_SRC (x), 1)) == LABEL_REF){
        fputs("jump", stream);
      }
      else {
        fputs("jump ", stream);
        hexagon_print_rtx(stream, XEXP (SET_SRC (x), 1));
      }
    }
    else {
      fputs("jump ", stream);
      hexagon_print_rtx(stream, SET_SRC (x));
    }
  }
  /* (set (pc) (reg)) */
  else if(x && GET_CODE (x) == SET
          && SET_DEST (x) == pc_rtx
          && SET_SRC (x) && REG_P (SET_SRC (x))){
    fputs("jump ", stream);
    hexagon_print_rtx(stream, SET_SRC (x));
  }
  else {
    fputs("jump", stream);
  }
}




/* Helper function for hexagon_print_rtl_pseudo_asm

   (set (...) (...)) */

static void
hexagon_print_transfer(FILE *stream, const_rtx x)
{
  if(!x){
    hexagon_print_rtx(stream, x);
  }
  /* (set (pc) (...)) */
  else if(XEXP (x, 0) == pc_rtx){
    hexagon_print_jump(stream, x);
  }
  /* (set (reg) (call)) */
  else if(XEXP (x, 0) && REG_P (XEXP (x, 0))
          && XEXP (x, 1) && GET_CODE (XEXP (x, 1)) == CALL){
    fputs("call", stream);
  }
  /* (set (zero_extract (...) (...) (...)) (...)) */
  else if(XEXP (x, 0) && GET_CODE (XEXP (x, 0)) == ZERO_EXTRACT){
    hexagon_print_rtx(stream, XEXP (XEXP (x, 0), 0));
    fputs(" = insert(", stream);
    hexagon_print_rtx(stream, XEXP (x, 1));
    fputc(',', stream);
    hexagon_print_rtx(stream, XEXP (XEXP (x, 0), 1));
    fputc(',', stream);
    hexagon_print_rtx(stream, XEXP (XEXP (x, 0), 2));
    fputc(')', stream);
  }
  /* (set (...) (high (...))) */
  else if(XEXP (x, 1) && GET_CODE (XEXP (x, 1)) == HIGH){
    hexagon_print_rtx(stream, XEXP (x, 0));
    fputs(".h = ", stream);
    hexagon_print_rtx(stream, XEXP (XEXP (x, 1), 0));
  }
  /* (set (reg X) (lo_sum (reg X) (...))) */
  else if(XEXP (x, 1) && GET_CODE (XEXP (x, 1)) == LO_SUM
          && XEXP (x, 0) && REG_P (XEXP (x, 0))
          && XEXP (XEXP (x, 1), 0) && REG_P (XEXP (XEXP (x, 1), 0))
          && REGNO (XEXP (x, 0)) == REGNO (XEXP (XEXP (x, 1), 0))){
    hexagon_print_rtx(stream, XEXP (x, 0));
    fputs(".l = ", stream);
    hexagon_print_rtx(stream, XEXP (XEXP (x, 1), 1));
  }
/*
  else if(XEXP (x, 1) && (   GET_CODE (XEXP (x, 1)) == PLUS
                          || GET_CODE (XEXP (x, 1)) == MINUS
                          || GET_CODE (XEXP (x, 1)) == MULT
                          || GET_CODE (XEXP (x, 1)) == AND
                          || GET_CODE (XEXP (x, 1)) == IOR
                          || GET_CODE (XEXP (x, 1)) == XOR)
          && XEXP (x, 0) && REG_P (XEXP (x, 0))
          && XEXP (XEXP (x, 1), 0) && REG_P (XEXP (XEXP (x, 1), 0))){
    hexagon_print_rtx(stream, XEXP (x, 0));
    fputc(' ', stream);
    switch(GET_CODE (XEXP (x, 1))){
      case PLUS:
        fputc('+', stream);
        break;
      case MINUS:
        fputc('-', stream);
        break;
      case MULT:
        fputc('*', stream);
        break;
      case AND:
        fputc('&', stream);
        break;
      case IOR:
        fputc('|', stream);
        break;
      case XOR:
        fputc('^', stream);
        break;
      default:
        break;
    }
    fputs("= ", stream);
    hexagon_print_rtx(stream, XEXP (XEXP (x, 1), 1));
  }
  else if(XEXP (x, 1) && (   GET_CODE (XEXP (x, 1)) == PLUS
                          || GET_CODE (XEXP (x, 1)) == MULT
                          || GET_CODE (XEXP (x, 1)) == AND
                          || GET_CODE (XEXP (x, 1)) == IOR
                          || GET_CODE (XEXP (x, 1)) == XOR)
          && XEXP (x, 0) && REG_P (XEXP (x, 0))
          && XEXP (XEXP (x, 1), 1) && REG_P (XEXP (XEXP (x, 1), 1))){
    hexagon_print_rtx(stream, XEXP (x, 0));
    fputc(' ', stream);
    switch(GET_CODE (XEXP (x, 1))){
      case PLUS:
        fputc('+', stream);
        break;
      case MULT:
        fputc('*', stream);
        break;
      case AND:
        fputc('&', stream);
        break;
      case IOR:
        fputc('|', stream);
        break;
      case XOR:
        fputc('^', stream);
        break;
      default:
        break;
    }
    fputs("= ", stream);
    hexagon_print_rtx(stream, XEXP (XEXP (x, 1), 0));
  }
*/
  else {
    hexagon_print_rtx(stream, XEXP (x, 0));
    fputs(" = ", stream);
    hexagon_print_rtx(stream, XEXP (x, 1));
  }
}




/* Helper function for hexagon_print_rtl_pseudo_asm */

static void
hexagon_print_condition(FILE *stream, const_rtx x, bool non_inverted)
{
  fputs("if (", stream);
  if(!x){
    hexagon_print_rtx(stream, x);
  }
  /* (reg) */
  else if(REG_P (x)){
    if(GET_MODE (x) == BImode && !non_inverted){
      fputc('!', stream);
    }
    hexagon_print_rtx(stream, x);
    if(GET_MODE (x) != BImode){
      fputs(non_inverted ? "!=#0" : "==#0", stream);
    }
  }
  /* (ne (reg) (const_int 0)) */
  else if(GET_CODE (x) == NE && XEXP (x, 1) == const0_rtx
          && XEXP (x, 0) && REG_P (XEXP (x, 0))){
    if(GET_MODE (XEXP (x, 0)) == BImode && !non_inverted){
      fputc('!', stream);
    }
    hexagon_print_rtx(stream, XEXP (x, 0));
    if(GET_MODE (XEXP (x, 0)) != BImode){
      fputs(non_inverted ? "!=#0" : "==#0", stream);
    }
  }
  /* (eq (reg) (const_int 0)) */
  else if(GET_CODE (x) == EQ && XEXP (x, 1) == const0_rtx
          && XEXP (x, 0) && REG_P (XEXP (x, 0))){
    if(GET_MODE (XEXP (x, 0)) == BImode && non_inverted){
      fputc('!', stream);
    }
    hexagon_print_rtx(stream, XEXP (x, 0));
    if(GET_MODE (XEXP (x, 0)) != BImode){
      fputs(non_inverted ? "==#0" : "!=#0", stream);
    }
  }
  /* (gt (reg) (const_int 0/-1)) */
  else if(GET_CODE (x) == GT
          && XEXP (x, 0) && REG_P (XEXP (x, 0))
          && GET_MODE (XEXP (x, 0)) != BImode
          && (XEXP (x, 1) == const0_rtx || XEXP (x, 1) == constm1_rtx)){
    hexagon_print_rtx(stream, XEXP (x, 0));
    if(XEXP (x, 1) == const0_rtx){
      fputs(non_inverted ? ">#0" : "<=#0", stream);
    }
    else {
      fputs(non_inverted ? ">=#0" : "<#0", stream);
    }
  }
  /* (ge (reg) (const_int 0/1)) */
  else if(GET_CODE (x) == GE
          && XEXP (x, 0) && REG_P (XEXP (x, 0))
          && GET_MODE (XEXP (x, 0)) != BImode
          && (XEXP (x, 1) == const0_rtx || XEXP (x, 1) == const1_rtx)){
    hexagon_print_rtx(stream, XEXP (x, 0));
    if(XEXP (x, 1) == const0_rtx){
      fputs(non_inverted ? ">=#0" : "<#0", stream);
    }
    else {
      fputs(non_inverted ? ">#0" : "<=#0", stream);
    }
  }
  /* (lt (reg) (const_int 0/1)) */
  else if(GET_CODE (x) == LT
          && XEXP (x, 0) && REG_P (XEXP (x, 0))
          && GET_MODE (XEXP (x, 0)) != BImode
          && (XEXP (x, 1) == const0_rtx || XEXP (x, 1) == const1_rtx)){
    hexagon_print_rtx(stream, XEXP (x, 0));
    if(XEXP (x, 1) == const0_rtx){
      fputs(non_inverted ? "<#0" : ">=#0", stream);
    }
    else {
      fputs(non_inverted ? "<=#0" : ">#0", stream);
    }
  }
  /* (le (reg) (const_int 0/-1)) */
  else if(GET_CODE (x) == LE
          && XEXP (x, 0) && REG_P (XEXP (x, 0))
          && GET_MODE (XEXP (x, 0)) != BImode
          && (XEXP (x, 1) == const0_rtx || XEXP (x, 1) == constm1_rtx)){
    hexagon_print_rtx(stream, XEXP (x, 0));
    if(XEXP (x, 1) == const0_rtx){
      fputs(non_inverted ? "<=#0" : ">#0", stream);
    }
    else {
      fputs(non_inverted ? "<#0" : ">=#0", stream);
    }
  }
  else {
    hexagon_print_rtx(stream, x);
  }
  fputs(") ", stream);
}




/* Helper function for hexagon_print_rtl_pseudo_asm */

static void
hexagon_print_address(FILE *stream, const_rtx x)
{
  /* (plus (...) (...)) */
  if(x && GET_CODE (x) == PLUS){
    hexagon_print_rtx(stream, XEXP (x, 0));
    fputc('+', stream);
    hexagon_print_rtx(stream, XEXP (x, 1));
  }
  else {
    hexagon_print_rtx(stream, x);
  }
}




/* Helper function for hexagon_print_rtl_pseudo_asm

   (op (...)) */

static void
hexagon_print_unary_op(FILE *stream, const char *op, const_rtx x)
{
  fputs(op, stream);
  fputc('(', stream);
  hexagon_print_rtx(stream, XEXP (x, 0));
  fputc(')', stream);
}




/* Helper function for hexagon_print_rtl_pseudo_asm

   (op (...) (...)) */

static void
hexagon_print_binary_op(FILE *stream, const char *op, const_rtx x)
{
  fputs(op, stream);
  fputc('(', stream);
  hexagon_print_rtx(stream, XEXP (x, 0));
  fputc(',', stream);
  hexagon_print_rtx(stream, XEXP (x, 1));
  fputc(')', stream);
}




/* Helper function for hexagon_print_rtl_pseudo_asm

   (op (...) (...)) */

static void
hexagon_print_swapped_binary_op(FILE *stream, const char *op, const_rtx x)
{
  fputs(op, stream);
  fputc('(', stream);
  hexagon_print_rtx(stream, XEXP (x, 1));
  fputc(',', stream);
  hexagon_print_rtx(stream, XEXP (x, 0));
  fputc(')', stream);
}




/* Helper function for hexagon_print_rtl_pseudo_asm

   (op (...) (...)) */

static void
hexagon_print_binary_op_with_option(
  FILE *stream,
  const char *op,
  const char *option,
  const_rtx x
)
{
  fputs(op, stream);
  fputc('(', stream);
  hexagon_print_rtx(stream, XEXP (x, 0));
  fputc(',', stream);
  hexagon_print_rtx(stream, XEXP (x, 1));
  fputs("):", stream);
  fputs(option, stream);
}




/* Helper function for hexagon_print_rtl_pseudo_asm

   (op (...) (...) (...)) */

static void
hexagon_print_trinary_op(FILE *stream, const char *op, const_rtx x)
{
  fputs(op, stream);
  fputc('(', stream);
  hexagon_print_rtx(stream, XEXP (x, 0));
  fputc(',', stream);
  hexagon_print_rtx(stream, XEXP (x, 1));
  fputc(',', stream);
  hexagon_print_rtx(stream, XEXP (x, 2));
  fputc(')', stream);
}




/* Helper function for hexagon_print_rtl_pseudo_asm

   (parallel/unspec/unspec_volatile [...]) */

static void
hexagon_print_vecexp(
  FILE *stream,
  const char *open,
  const char *separator,
  const char *close,
  const_rtx x
)
{
  int i;
  fputs(open, stream);
  for(i = 0; i < XVECLEN (x, 0); i++){
    if(i > 0){
      fputs(separator, stream);
    }
    hexagon_print_rtx(stream, XVECEXP (x, 0, i));
  }
  fputs(close, stream);
}




/* Helper function for hexagon_print_rtl_pseudo_asm */

static void
hexagon_print_rtx(FILE *stream, const_rtx x)
{
  const char *op;
  int i;

  if(!x){
    fputs("[nil]", stream);
    return;
  }
  else if(GET_CODE (x) > NUM_RTX_CODE){
    fprintf(stream, "[??? bade code %d]", GET_CODE (x));
    return;
  }

  switch(GET_CODE (x)){
    case SET:
      hexagon_print_transfer(stream, x);
      break;
    case COND_EXEC:
      hexagon_print_condition(stream, XEXP (x, 0), true);
      hexagon_print_rtx(stream, XEXP (x, 1));
      break;
    case PARALLEL:
      for(i = XVECLEN (x, 0) - 1; i >= 0; i--){
        if(XVECEXP (x, 0, i) && GET_CODE (XVECEXP (x, 0, i)) == CLOBBER
           && i > 0 && XVECEXP (x, 0, i - 1)
           && (GET_CODE (XVECEXP (x, 0, i - 1)) == CALL
               || (GET_CODE (XVECEXP (x, 0, i - 1)) == SET
                   && XEXP (XVECEXP (x, 0, i - 1), 0)
                   && REG_P (XEXP (XVECEXP (x, 0, i - 1), 0))
                   && XEXP (XVECEXP (x, 0, i - 1), 1)
                   && GET_CODE (XEXP (XVECEXP (x, 0, i - 1), 1)) == CALL))){
        }
      }
      hexagon_print_vecexp(stream, "{ ", "; ", " }", x);
      break;
    case UNSPEC:
      if(XINT (x, 1) == UNSPEC_NEW_VALUE){
        hexagon_print_rtx(stream, XVECEXP (x, 0, 0));
        fputs(".new", stream);
      }
      else {
        fprintf(stream, "unspec%d", XINT (x, 1));
        hexagon_print_vecexp(stream, "(", ",", ")", x);
      }
      break;
    case UNSPEC_VOLATILE:
      fprintf(stream, "unspec_volatile%d", XINT (x, 1));
      hexagon_print_vecexp(stream, "(", ",", ")", x);
      break;
    case PREFETCH:
      hexagon_print_unary_op(stream, "dcfetch", x);
      break;
    case USE:
      hexagon_print_unary_op(stream, "use", x);
      break;
    case CLOBBER:
      hexagon_print_rtx(stream, XEXP (x, 0));
      fputs(" = clobber()", stream);
      break;
    case CALL:
      fputs("call", stream);
      break;
    case RETURN:
      fputs("jumpr r31", stream);
      break;
    case CONST_INT:
      fputc('#', stream);
      PRINT_OPERAND (stream, x, 0);
      break;
    case CONST_DOUBLE:
      if(reload_completed){
        fputc('#', stream);
        PRINT_OPERAND (stream, x, 0);
      }
      else {
        fputs("#float", stream);
      }
      break;
    case CONST:
      if(XEXP (x, 0) && GET_CODE (XEXP (x, 0)) == PLUS
         && XEXP (XEXP (x, 0), 0)
         && GET_CODE (XEXP (XEXP (x, 0), 0)) == SYMBOL_REF
         && XEXP (XEXP (x, 0), 1)
         && GET_CODE (XEXP (XEXP (x, 0), 1)) == CONST_INT){
        fputs("#symbol", stream);
      }
      else {
        fputc('#', stream);
      }
      break;
    case PC:
      fputs("pc", stream);
      break;
    case REG:
      if(reload_completed){
        PRINT_OPERAND (stream, x, 0);
      }
      else {
        if(C_REG_P (x)){
          fputs(reg_names[REGNO (x)], stream);
        }
        else {
          switch(GET_MODE (x)){
            case DFmode:
              fputs("R:Rf", stream);
              break;
            case DImode:
              fputs("R:R", stream);
              break;
            case SFmode:
              fputs("Rf", stream);
              break;
            case BImode:
              fputc('p', stream);
              break;
            default:
              fputc('R', stream);
          }
        }
      }
      break;
    case SCRATCH:
      hexagon_print_rtx(stream, XEXP (x, 0));
      break;
    case SUBREG:
      if(reload_completed){
        hexagon_print_rtx(stream, XEXP (x, 0));
      }
      else {
        if(GET_MODE (x) == SImode
           && XEXP (x, 0) && REG_P (XEXP (x, 0))
           && GET_MODE (XEXP (x, 0)) == DImode
           && (XINT (x, 1) == 0 || XINT (x, 1) == 4)){
          fputc('R', stream);
        }
        else {
          hexagon_print_rtx(stream, XEXP (x, 0));
/*
          fputc('.', stream);
          int size_in_bytes = 1;
          switch(GET_MODE (x)){
            case DImode:
            case DFmode:
              fputc('d', stream);
              size_in_bytes = 8;
              break;
            case SImode:
            case SFmode:
              fputc('w', stream);
              size_in_bytes = 4;
              break;
            case HImode:
              fputc('h', stream);
              size_in_bytes = 2;
              break;
            case QImode:
              fputc('b', stream);
              size_in_bytes = 1;
              break;
            default:
              fputc('?', stream);
              return;
          }
          fputc('[', stream);
          fprintf(stream, "%d", XINT (x, 1) / size_in_bytes);
          fputc(']', stream);
*/
        }
      }
      break;
    case MEM:
      fputs("mem", stream);
      switch(GET_MODE_SIZE (GET_MODE (x))){
        case 8:
          fputc('d', stream);
          break;
        case 2:
          fputc('h', stream);
          break;
        case 1:
          fputc('b', stream);
          break;
        default:
          fputc('w', stream);
      }
      fputc('(', stream);
      hexagon_print_address(stream, XEXP (x, 0));
      fputc(')', stream);
      break;
    case LABEL_REF:
      fputs(".L", stream);
      break;
    case SYMBOL_REF:
      fputs("#symbol", stream);
      break;
    case IF_THEN_ELSE:
      if(XEXP (x, 0) && GET_CODE (XEXP (x, 0)) == NE
         && XEXP (XEXP (x, 0), 1) == const0_rtx){
        fputs("mux(", stream);
        hexagon_print_rtx(stream, XEXP (XEXP (x, 0), 0));
        fputc(',', stream);
        hexagon_print_rtx(stream, XEXP (x, 1));
        fputc(',', stream);
        hexagon_print_rtx(stream, XEXP (x, 2));
        fputc(')', stream);
      }
      else if(XEXP (x, 0) && GET_CODE (XEXP (x, 0)) == EQ
              && XEXP (XEXP (x, 0), 1) == const0_rtx){
        fputs("mux(", stream);
        hexagon_print_rtx(stream, XEXP (XEXP (x, 0), 0));
        fputc(',', stream);
        hexagon_print_rtx(stream, XEXP (x, 2));
        fputc(',', stream);
        hexagon_print_rtx(stream, XEXP (x, 1));
        fputc(')', stream);
      }
      else {
        hexagon_print_trinary_op(stream, "mux", x);
      }
      break;
    case PLUS:
      hexagon_print_binary_op(stream, "add", x);
      break;
    case MINUS:
      hexagon_print_binary_op(stream, "sub", x);
      break;
    case NEG:
      hexagon_print_unary_op(stream, "neg", x);
      break;
    case MULT:
      hexagon_print_binary_op(stream, "mpyi", x);
      break;
    case AND:
      hexagon_print_binary_op(stream, "and", x);
      break;
    case IOR:
      hexagon_print_binary_op(stream, "or", x);
      break;
    case XOR:
      hexagon_print_binary_op(stream, "xor", x);
      break;
    case NOT:
      hexagon_print_unary_op(stream, "not", x);
      break;
    case ASHIFT:
      hexagon_print_binary_op(stream, "asl", x);
      break;
    case ROTATE:
      if(XEXP (x, 0) && REG_P (XEXP (x, 0)) && GET_MODE (XEXP (x, 0)) == SImode
         && XEXP (x, 1) && GET_CODE (XEXP (x, 1)) == CONST_INT
         && INTVAL (XEXP (x, 1)) == 16){
        fputs("combine(", stream);
        hexagon_print_rtx(stream, XEXP (x, 0));
        fputs(".l,", stream);
        hexagon_print_rtx(stream, XEXP (x, 0));
        fputs(".h)", stream);
      }
      else {
        hexagon_print_binary_op(stream, "rotate_left", x);
      }
      break;
    case ASHIFTRT:
      hexagon_print_binary_op(stream, "asr", x);
      break;
    case LSHIFTRT:
      hexagon_print_binary_op(stream, "lsr", x);
      break;
    case ROTATERT:
      if(XEXP (x, 0) && REG_P (XEXP (x, 0)) && GET_MODE (XEXP (x, 0)) == SImode
         && XEXP (x, 1) && GET_CODE (XEXP (x, 1)) == CONST_INT
         && INTVAL (XEXP (x, 1)) == 16){
        fputs("combine(", stream);
        hexagon_print_rtx(stream, XEXP (x, 0));
        fputs(".l,", stream);
        hexagon_print_rtx(stream, XEXP (x, 0));
        fputs(".h)", stream);
      }
      else {
        hexagon_print_binary_op(stream, "rotate_right", x);
      }
      break;
    case SMIN:
      hexagon_print_binary_op(stream, "min", x);
      break;
    case SMAX:
      hexagon_print_binary_op(stream, "max", x);
      break;
    case UMIN:
      hexagon_print_binary_op(stream, "minu", x);
      break;
    case UMAX:
      hexagon_print_binary_op(stream, "maxu", x);
      break;
    case POST_DEC:
    case POST_INC:
      hexagon_print_rtx(stream, XEXP (x, 0));
      fputs("++#", stream);
      break;
    case POST_MODIFY:
      if(XEXP (x, 0) && REG_P (XEXP (x, 0))
         && XEXP (x, 1) && GET_CODE (XEXP (x, 1)) == PLUS
         && XEXP (XEXP (x, 1), 0) && REG_P (XEXP (XEXP (x, 1), 0))
         && REGNO (XEXP (x, 0)) == REGNO (XEXP (XEXP (x, 1), 0))){
        hexagon_print_rtx(stream, XEXP (x, 0));
        fputs("++", stream);
        hexagon_print_rtx(stream, XEXP (XEXP (x, 1), 1));
      }
      else {
        hexagon_print_rtx(stream, XEXP (x, 0));
        fputs(", ", stream);
        hexagon_print_transfer(stream, x);
      }
      break;
    case NE:
    case EQ:
      if(XEXP (x, 0) && GET_CODE (XEXP (x, 0)) == ZERO_EXTRACT
         && XEXP (XEXP (x, 0), 1) == const1_rtx
         && (XEXP (x, 1) == const0_rtx || XEXP (x, 1) == const1_rtx)){
        if(XEXP (x, 1) == (GET_CODE (x) == NE ? const1_rtx : const0_rtx)){
          fputc('!', stream);
        }
        fputs("tstbit(", stream);
        hexagon_print_rtx(stream, XEXP (XEXP (x, 0), 0));
        fputc(',', stream);
        hexagon_print_rtx(stream, XEXP (XEXP (x, 0), 2));
        fputc(')', stream);
      }
      else {
        hexagon_print_binary_op(stream, GET_CODE (x) == NE ? "cmp.ne" : "cmp.eq",
                              x);
      }
      break;
    case GE:
      hexagon_print_binary_op(stream, "cmp.ge", x);
      break;
    case GT:
      hexagon_print_binary_op(stream, "cmp.gt", x);
      break;
    case LE:
      hexagon_print_swapped_binary_op(stream, "cmp.gt", x);
      break;
    case LT:
      hexagon_print_swapped_binary_op(stream, "cmp.ge", x);
      break;
    case GEU:
      hexagon_print_binary_op(stream, "cmp.geu", x);
      break;
    case GTU:
      hexagon_print_binary_op(stream, "cmp.gtu", x);
      break;
    case LEU:
      hexagon_print_swapped_binary_op(stream, "cmp.gtu", x);
      break;
    case LTU:
      hexagon_print_swapped_binary_op(stream, "cmp.geu", x);
      break;
    case SIGN_EXTEND:
    case ZERO_EXTEND:
      op = GET_CODE (x) == SIGN_EXTEND ? "sxt" : "zxt";
      if(!XEXP (x, 0)){
        hexagon_print_unary_op(stream, op, XEXP (x, 0));
      }
      else {
        if(GET_CODE (XEXP (x, 0)) == MEM){
          op = GET_CODE (x) == SIGN_EXTEND ? "mem" : "memu";
        }
        fputs(op, stream);
        switch(GET_MODE (XEXP (x, 0))){
          case DImode:
            fputc('d', stream);
            break;
          case HImode:
            fputc('h', stream);
            break;
          case QImode:
            fputc('b', stream);
            break;
          default:
            fputc('w', stream);
        }
        if(GET_CODE (XEXP (x, 0)) == MEM){
          fputc('(', stream);
          hexagon_print_address(stream, XEXP (XEXP (x, 0), 0));
          fputc(')', stream);
        }
        else {
          hexagon_print_unary_op(stream, "", x);
        }
      }
      break;
    case TRUNCATE:
      hexagon_print_rtx(stream, XEXP (x, 0));
      fputc('.', stream);
      switch(GET_MODE (x)){
        case DImode:
        case DFmode:
          fputc('d', stream);
          break;
        case SImode:
        case SFmode:
          fputc('w', stream);
          break;
        case HImode:
          fputc('h', stream);
          break;
        case QImode:
          fputc('b', stream);
          break;
        default:
          fputc('?', stream);
          return;
      }
      fputs("[0]", stream);
      break;
    case ABS:
      hexagon_print_unary_op(stream, "abs", x);
      break;
    case CLZ:
      hexagon_print_unary_op(stream, "cl0", x);
      break;
    case CTZ:
      hexagon_print_unary_op(stream, "ct0", x);
      break;
    case POPCOUNT:
      hexagon_print_unary_op(stream, "count_ones", x);
      break;
    case PARITY:
      hexagon_print_unary_op(stream, "parity", x);
      break;
    case SIGN_EXTRACT:
      hexagon_print_trinary_op(stream, "extract", x);
      break;
    case ZERO_EXTRACT:
      hexagon_print_trinary_op(stream, "extractu", x);
      break;
    case HIGH:
      hexagon_print_rtx(stream, XEXP (x, 0));
      fputs(".h", stream);
      break;
    case LO_SUM:
      fputs("add(", stream);
      hexagon_print_rtx(stream, XEXP (x, 0));
      fputc(',', stream);
      hexagon_print_rtx(stream, XEXP (x, 1));
      fputs(".l)", stream);
      break;
    case SS_PLUS:
      hexagon_print_binary_op_with_option(stream, "add", "sat", x);
      break;
    case US_PLUS:
      hexagon_print_binary_op_with_option(stream, "add", "satu", x);
      break;
    case SS_MINUS:
      hexagon_print_binary_op_with_option(stream, "sub", "sat", x);
      break;
    case US_MINUS:
      hexagon_print_binary_op_with_option(stream, "sub", "satu", x);
      break;
    case SS_TRUNCATE:
      switch(GET_MODE (x)){
        case HImode:
          hexagon_print_unary_op(stream, "sath", x);
          break;
        case QImode:
          hexagon_print_unary_op(stream, "satb", x);
          break;
        default:
          hexagon_print_unary_op(stream, "sat", x);
      }
      break;
    case US_TRUNCATE:
      switch(GET_MODE (x)){
        case HImode:
          hexagon_print_unary_op(stream, "satuh", x);
          break;
        case QImode:
          hexagon_print_unary_op(stream, "satub", x);
          break;
        default:
          hexagon_print_unary_op(stream, "satu", x);
      }
      break;
    default:
      fprintf(stream, "[%s]", GET_RTX_NAME (GET_CODE (x)));
  }
}




/* Implements hook TARGET_PRINT_RTL_PSEUDO_ASM */

void
hexagon_print_rtl_pseudo_asm(FILE *stream, const_rtx x)
{
  if(x && INSN_P (x)){
    hexagon_print_rtx(stream, PATTERN (x));
  }
  else {
    hexagon_print_rtx(stream, x);
  }
}




/*-------------------------------------------
Functions called from the machine description
-------------------------------------------*/

/* Compute the DWARF information for the frame of the current function, used for
   exception handling and debugging. */

static void
hexagon_compute_dwarf_frame_information(void)
{
  struct hexagon_frame_info *frame;
  HOST_WIDE_INT offset;
  char *label;
  unsigned int i;

  if(!dwarf2out_do_frame()){
    return;
  }

  label = dwarf2out_cfi_label(false);

  frame = hexagon_frame_info();

  /* Did we use the allocframe instruction? */
  if(frame->use_allocframe){
    /* Yes. */
    dwarf2out_def_cfa(label, HARD_FRAME_POINTER_REGNUM, frame->lrfp_size);
    dwarf2out_reg_save(label, LINK_REGNUM, -UNITS_PER_WORD);
    dwarf2out_reg_save(label, HARD_FRAME_POINTER_REGNUM, -(2 * UNITS_PER_WORD));
  }
  else {
    /* No. */
    dwarf2out_def_cfa(label, STACK_POINTER_REGNUM, frame->total_size);
  }

  /* Saved callee-save registers. */
  offset = -(frame->base_reg == stack_pointer_rtx    ? frame->total_size
                        /* hard_frame_pointer_rtx */ : frame->lrfp_size)
           + frame->offset;
  /* Did we save any callee-save registers as pairs? */
  for(i = 0; i < frame->num_saved_pairs; i++){
    offset -= 2 * UNITS_PER_WORD;
    dwarf2out_reg_save(label, frame->saved_pairs[i], offset);
    dwarf2out_reg_save(label, frame->saved_pairs[i] + 1,
                              offset + UNITS_PER_WORD);
  }
  /* Did we save any other callee-save registers? */
  for(i = 0; i < frame->num_saved_singles; i++){
    offset -= UNITS_PER_WORD;
    dwarf2out_reg_save(label, frame->saved_singles[i], offset);
  }
}




/* Helper function for hexagon_expand_prologue

   Allocate stack space by decrementing SP. */

static void
hexagon_allocate_stack(unsigned HOST_WIDE_INT size, int allocate_stack_insn){
  rtx offset;

  if(size == 0){
    return;
  }

  /* If more than two add instructions would be required, then load the offset
     into r28. */
  if(size > 2 * -MIN_ADD_IMMED){
    offset = gen_rtx_REG (SImode, 28);
    emit_move_insn(offset, gen_int_mode(-size, Pmode));
    size = 0;
  }
  else if(size > -MIN_ADD_IMMED){
    offset = gen_int_mode(MIN_ADD_IMMED, Pmode);
    size -= -MIN_ADD_IMMED;
  }
  else {
    offset = gen_int_mode(-size, Pmode);
    size = 0;
  }

  emit_insn(GEN_FCN (allocate_stack_insn)(offset));

  if(size > 0){
    offset = gen_int_mode(-size, Pmode);
    emit_insn(gen_increment_stack_pointer(offset));
  }
}




/* Emit instructions to set up a stack frame and save any registers that need
   saving for the current function. */

void
hexagon_expand_prologue(void)
{
  struct hexagon_frame_info *frame;
  rtx base_reg;
  HOST_WIDE_INT offset;
  unsigned int i;

  frame = hexagon_frame_info();

  /* Do we need to use the allocframe instruction? */
  if(frame->use_allocframe){
    rtx allocframe_size = gen_int_mode(frame->allocframe_size, SImode);
    emit_insn(GEN_FCN (frame->allocframe_insn)(allocframe_size));
  }

  /* Allocate any remaning stack space. */
  hexagon_allocate_stack(frame->sp_adjustment, frame->allocate_stack_insn);

  /* Save callee-save registers. */
  if(frame->prologue_function != CODE_FOR_nothing){
    emit_insn(GEN_FCN (frame->prologue_function)(NULL_RTX));
  }
  base_reg = frame->base_reg;
  offset = frame->offset;
  /* Account for any pairs that have already been saved. */
  offset -= 2 * UNITS_PER_WORD * frame->num_specially_saved_pairs;
  /* Save any callee-save registers that can be stored as pairs and have not
     already been saved in some other manner. */
  for(i = frame->num_specially_saved_pairs; i < frame->num_saved_pairs; i++){
    offset -= 2 * UNITS_PER_WORD;
    emit_move_insn(gen_rtx_MEM (DImode, plus_constant(base_reg, offset)),
                   gen_rtx_REG (DImode, frame->saved_pairs[i]));
  }
  /* Account for any singles that have already been saved. */
  offset -= UNITS_PER_WORD * frame->num_specially_saved_singles;
  /* Save any remaining callee-save registers. */
  for(i = frame->num_specially_saved_singles; i < frame->num_saved_singles; i++){
    offset -= UNITS_PER_WORD;
    emit_move_insn(gen_rtx_MEM (SImode, plus_constant(base_reg, offset)),
                   gen_rtx_REG (SImode, frame->saved_singles[i]));
  }

  if (flag_pic && crtl->uses_pic_offset_table) {
    hexagon_load_pic_register ();
  }

}




/* Return true if the current function's epilogue consists only of a return
   instruction. */

bool
hexagon_direct_return(void)
{
  struct hexagon_frame_info *frame = hexagon_frame_info();

  return reload_completed && (frame->total_size == 0
                              || (TARGET_V4_FEATURES && frame->use_allocframe
                                                     && frame->reg_size == 0));
}




/* Helper function for hexagon_expand_epilogue

   Deallocate stack space by incrementing SP. */

static void
hexagon_deallocate_stack(unsigned HOST_WIDE_INT size){
  rtx r28;

  /* If more than two add instructions would be required, then reload the offset
     into r28. */
  if(size > 2 * MAX_ADD_IMMED){
    r28 = gen_rtx_REG (SImode, 28);
    emit_move_insn(r28, gen_int_mode(size, Pmode));
    emit_insn(gen_addsi3(stack_pointer_rtx, stack_pointer_rtx, r28));
  }
  else {
    while(size > MAX_ADD_IMMED){
      emit_insn(gen_addsi3(stack_pointer_rtx,
                           stack_pointer_rtx,
                           gen_int_mode(MAX_ADD_IMMED, Pmode)));
      size -= MAX_ADD_IMMED;
    }
    if(size != 0){
      emit_insn(gen_addsi3(stack_pointer_rtx,
                           stack_pointer_rtx,
                           gen_int_mode(size, Pmode)));
    }
  }
}




/* Emit instructions to tear down the stack frame and restore any registers that
   need restoring for the current function.  Also emit a return instruction iff
   EMIT_RETURN is true. */

void
hexagon_expand_epilogue(bool sibcall)
{
  bool emit_return;
  struct hexagon_frame_info *frame;
  rtx base_reg;
  HOST_WIDE_INT offset;
  int i;

  emit_return = !sibcall;

  frame = hexagon_frame_info();

  /* Restore callee-save registers. */
  base_reg = frame->base_reg;
  offset = frame->offset - (2 * frame->num_saved_pairs
                              + frame->num_saved_singles) * UNITS_PER_WORD;
  /* Restore any callee-save registers not stored as part of a pair. */
  for(i = (int) frame->num_saved_singles - 1; i >= 0; i--){
    emit_move_insn(gen_rtx_REG (SImode, frame->saved_singles[i]),
                   gen_rtx_MEM (SImode, plus_constant(base_reg, offset)));
    offset += UNITS_PER_WORD;
  }
  /* Restore any callee-save registers that can be loaded as pairs and will not
     be loaded by a common epilogue function. */
  for(i = (int) frame->num_saved_pairs - 1;
      i >= (int) (sibcall ? frame->num_sibcall_function_restored_pairs
                          : frame->num_function_restored_pairs);
      i--){
    emit_move_insn(gen_rtx_REG (DImode, frame->saved_pairs[i]),
                   gen_rtx_MEM (DImode, plus_constant(base_reg, offset)));
    offset += 2 * UNITS_PER_WORD;
  }

  /* Determine how best to deallocate the stack frame and restore LR and FP if
     necessary. */
  /* If LR and FP do not need to be restored, then simply deallocate the
     stack. */
  if(!frame->use_allocframe){
    hexagon_deallocate_stack(frame->sp_adjustment);
  }
  /* Otherwise, call a function if doing so will save code size. */
  else if(!sibcall && frame->epilogue_function != CODE_FOR_nothing){
    emit_jump_insn(GEN_FCN (frame->epilogue_function)(NULL_RTX));
    emit_return = false;
  }
  else if(sibcall && frame->sibcall_epilogue_function != CODE_FOR_nothing){
    emit_insn(GEN_FCN (frame->sibcall_epilogue_function)(NULL_RTX));
  }
  /* Otherwise, on V4 and up, use the dealloc_return instruction if possible. */
  else if(TARGET_V4_FEATURES && emit_return
          && !crtl->calls_eh_return){
    emit_jump_insn(gen_deallocframe_return());
    emit_return = false;
  }
  /* Otherwise, use separate deallocframe and return instructions. */
  else {
    emit_insn(gen_deallocframe());
  }

  /* If returning to an exception handler, adjust the stack as necessary. */
  if(crtl->calls_eh_return){
    emit_insn(gen_addsi3(stack_pointer_rtx,
                         stack_pointer_rtx, EH_RETURN_STACKADJ_RTX));
  }

  /* Emit a return jump if we still need to. */
  if(emit_return){
    emit_jump_insn(gen_return_jump());
  }
}




#define SET_CODES(CC, JC) compare_code = (CC); jump_code = (JC)
#define SWAP_OPERANDS {rtx swap_rtx = op0; \
                       op0 = op1; \
                       op1 = swap_rtx;}

rtx
hexagon_expand_compare(enum rtx_code code)
{
  rtx op0 = cfun->machine->compare_op0;
  rtx op1 = cfun->machine->compare_op1;
  enum rtx_code compare_code, jump_code;
  rtx p_reg;
  int offset = 0;

  if(GET_MODE (op0) == BImode){
    gcc_assert(REG_P (op0) && (code == NE || code == EQ) && op1 == const0_rtx);
    return gen_rtx_fmt_ee(code, BImode, op0, op1);
  }

  if(REG_P (op1) || GET_CODE (op1) == SUBREG){
    switch(code) {
      /* Equality compares */
      case EQ:
        SET_CODES (EQ, NE); break;
      case NE:
        SET_CODES (EQ, EQ); break;

      /* Signed compares */
      case LT:
        SET_CODES (GT, NE); SWAP_OPERANDS; break;
      case LE:
        SET_CODES (GT, EQ); break;
      case GT:
        SET_CODES (GT, NE); break;
      case GE:
        SET_CODES (GT, EQ); SWAP_OPERANDS; break;

      /* Unsigned compares */
      case LTU:
        SET_CODES (GTU, NE); SWAP_OPERANDS; break;
      case LEU:
        SET_CODES (GTU, EQ); break;
      case GTU:
        SET_CODES (GTU, NE); break;
      case GEU:
        SET_CODES (GTU, EQ); SWAP_OPERANDS; break;

      default:
        gcc_unreachable();
    }
  }
  else {
    gcc_assert(GET_MODE (op0) != DImode && GET_MODE (op1) != DImode);

    switch(code) {
      /* Equality compares */
      case EQ:
        SET_CODES (EQ, NE); break;
      case NE:
        SET_CODES (EQ, EQ); break;

      /* Signed compares */
      case LT:
        SET_CODES (GT, EQ); offset = -1; break;
      case LE:
        SET_CODES (GT, EQ); break;
      case GT:
        SET_CODES (GT, NE); break;
      case GE:
        SET_CODES (GT, NE); offset = -1; break;

      /* Unsigned compares */
      case LTU:
        SET_CODES (GTU, EQ); offset = -1; break;
      case LEU:
        SET_CODES (GTU, EQ); break;
      case GTU:
        SET_CODES (GTU, NE); break;
      case GEU:
        SET_CODES (GTU, NE); offset = -1; break;

      default:
        gcc_unreachable();
    }

    op1 = plus_constant(op1, offset);

    if(GET_CODE (op1) != CONST_INT
       || !IN_RANGE (INTVAL (op1), compare_code == GTU ? 0 : -512, 511)){
      op1 = force_reg(SImode, op1);
    }
  }

  p_reg = gen_reg_rtx (BImode);

  if (!gr_register_operand(op0, GET_MODE(op0)))
  {
    gcc_assert (!reload_completed);
    op0 = copy_to_mode_reg (GET_MODE(op0), op0);
  }
  
  /* emit (set (reg:BI p_reg) (compare_code:BI op0 op1)) */
  emit_insn(gen_rtx_SET (VOIDmode, p_reg,
                         gen_rtx_fmt_ee(compare_code, BImode, op0, op1)));

  /* return (eq/ne:BI (reg:BI p_reg) (const_int 0)) */
  return gen_rtx_fmt_ee(jump_code, BImode, p_reg, const0_rtx);
}

rtx
hexagon_expand_compare2(enum rtx_code code, rtx op0, rtx op1)
{
  enum rtx_code compare_code, jump_code;
  rtx p_reg, const_reg;
  rtx cmp_rtx;
  int offset = 0;

  if(GET_MODE (op0) == BImode){
    gcc_assert(REG_P (op0) && (code == NE || code == EQ) && op1 == const0_rtx);
    return gen_rtx_fmt_ee(code, BImode, op0, op1);
  }

  if(REG_P (op1) || GET_CODE (op1) == SUBREG){
    switch(code) {
      /* Equality compares */
      case EQ:
        SET_CODES (EQ, NE); break;
      case NE:
        SET_CODES (EQ, EQ); break;

      /* Signed compares */
      case LT:
        SET_CODES (GT, NE); SWAP_OPERANDS; break;
      case LE:
        SET_CODES (GT, EQ); break;
      case GT:
        SET_CODES (GT, NE); break;
      case GE:
        SET_CODES (GT, EQ); SWAP_OPERANDS; break;

      /* Unsigned compares */
      case LTU:
        SET_CODES (GTU, NE); SWAP_OPERANDS; break;
      case LEU:
        SET_CODES (GTU, EQ); break;
      case GTU:
        SET_CODES (GTU, NE); break;
      case GEU:
        SET_CODES (GTU, EQ); SWAP_OPERANDS; break;

      default:
        gcc_unreachable();
    }
  }
  else {
    /*gcc_assert(GET_MODE (op0) != DImode && GET_MODE (op1) != DImode);*/

    switch(code) {
      /* Equality compares */
      case EQ:
        SET_CODES (EQ, NE); break;
      case NE:
        SET_CODES (EQ, EQ); break;

      /* Signed compares */
      case LT:
        SET_CODES (GT, EQ); offset = -1; break;
      case LE:
        SET_CODES (GT, EQ); break;
      case GT:
        SET_CODES (GT, NE); break;
      case GE:
        SET_CODES (GT, NE); offset = -1; break;

      /* Unsigned compares */
      case LTU:
        SET_CODES (GTU, EQ); offset = -1; break;
      case LEU:
        SET_CODES (GTU, EQ); break;
      case GTU:
        SET_CODES (GTU, NE); break;
      case GEU:
        SET_CODES (GTU, NE); offset = -1; break;

      default:
        gcc_unreachable();
    }

    op1 = plus_constant(op1, offset);


    if(GET_CODE (op1) == CONST_INT && GET_MODE(op0) == DImode) {
      op1 = force_reg(DImode, op1);
    }
    else if(GET_CODE (op1) != CONST_INT
       || !IN_RANGE (INTVAL (op1), compare_code == GTU ? 0 : -512, 511)){
      op1 = force_reg(SImode, op1);
    }
  }

  p_reg = gen_reg_rtx (BImode);

  if (!gr_register_operand(op0, GET_MODE(op0)))
  {
    gcc_assert (!reload_completed);
    op0 = copy_to_mode_reg (GET_MODE(op0), op0);
  }

  /* emit (set (reg:BI p_reg) (compare_code:BI op0 op1)) */
  emit_insn(gen_rtx_SET (VOIDmode, p_reg,
                         gen_rtx_fmt_ee(compare_code, BImode, op0, op1)));

  /* return (eq/ne:BI (reg:BI p_reg) (const_int 0)) */
  cmp_rtx = gen_rtx_fmt_ee(jump_code, BImode, p_reg, const0_rtx);
  return cmp_rtx;

  /*
  emit_jump_insn (gen_rtx_SET (VOIDmode, pc_rtx,
                               gen_rtx_IF_THEN_ELSE (VOIDmode, cmp_rtx,
                                                     gen_rtx_LABEL_REF (VOIDmode, label),
                                                     pc_rtx)));
  */
}




/* Creates a tree node for a block-move function named NAME. */

static tree
hexagon_special_case_memcpy_fn(const char *name)
{
  tree args, fn;

  fn = get_identifier(name);
  args = build_function_type_list(ptr_type_node, ptr_type_node,
                                  const_ptr_type_node, sizetype,
                                  NULL_TREE);

  fn = build_decl(BUILTINS_LOCATION, FUNCTION_DECL, fn, args);
  DECL_EXTERNAL (fn) = 1;
  TREE_PUBLIC (fn) = 1;
  DECL_ARTIFICIAL (fn) = 1;
  TREE_NOTHROW (fn) = 1;
  DECL_VISIBILITY (fn) = VISIBILITY_DEFAULT;
  DECL_VISIBILITY_SPECIFIED (fn) = 1;
  make_decl_rtl(fn);
  assemble_external(fn);

  return fn;
}




/* Emits a call to block-move function *FN named NAME with parameters DST, SRC,
   and SIZE.  TAILCALL is true only if the call may be implemented as a tail
   call.  If *FN is NULL, then it is initialized to a tree node for a function
   named NAME. */

static void
hexagon_emit_special_case_memcpy_fn(
  tree *fn,
  const char *name,
  rtx dst,
  rtx src,
  rtx size,
  bool tailcall
)
{
  rtx dst_addr, src_addr;
  tree call_expr, src_tree, dst_tree, size_tree;
  enum machine_mode size_mode;

  /* Emit code to copy the addresses of DST and SRC and SIZE into new
     pseudos.  We can then place those new pseudos into a VAR_DECL and
     use them later.  */

  dst_addr = copy_to_mode_reg(Pmode, XEXP (dst, 0));
  src_addr = copy_to_mode_reg(Pmode, XEXP (src, 0));

  dst_addr = convert_memory_address(ptr_mode, dst_addr);
  src_addr = convert_memory_address(ptr_mode, src_addr);

  dst_tree = make_tree(ptr_type_node, dst_addr);
  src_tree = make_tree(ptr_type_node, src_addr);

  size_mode = TYPE_MODE (sizetype);

  size = convert_to_mode(size_mode, size, 1);
  size = copy_to_mode_reg(size_mode, size);

  size_tree = make_tree(sizetype, size);

  if(!*fn){
    *fn = hexagon_special_case_memcpy_fn(name);
  }
  call_expr = build_call_expr (*fn, 3, dst_tree, src_tree, size_tree);
  CALL_EXPR_TAILCALL (call_expr) = tailcall;

  expand_normal (call_expr);
}




/* Emits an inline implementation of a block move.  OPERANDS[0] is a MEM
   containing the destination address.  OPERANDS[1] is a MEM containing the
   source address.  OPERANDS[2] is a CONST_INT containing the number of bytes to
   be copied.  OPERANDS[3] is a CONST_INT containing the guaranteed minimum
   alignment of both the source and destination addresses.  If VOLATILE_P is
   true then the final assembly corresponding to the code being emitted must not
   contain any packets containing more than one memory access. */

static void
hexagon_expand_movmem_inline(rtx operands[], bool volatile_p)
{
  rtx src_0, dst_0, src_reg, dst_reg, src_mem, dst_mem, value_reg, count_reg;
  rtx label, loopcount_rtx, doloop_fixup_code;
  int count, loopcount, align, size, log2size;
  enum machine_mode mode;
  rtx (*gen_memcpy_kernel)(rtx, rtx, rtx, rtx);

  count = INTVAL (operands[2]);
  align = INTVAL (operands[3]);

  gcc_assert(count >= 0);

  src_0 = operands[1];
  dst_0 = operands[0];
  src_reg = copy_to_mode_reg(Pmode, XEXP (src_0, 0));
  dst_reg = copy_to_mode_reg(Pmode, XEXP (dst_0, 0));

  /* Copy as many pieces as possible of size equal to the mutual alignment of
     the source and destination. */
  if((align & 7) == 0){
    mode = DImode;
    size = 8;
    log2size = 3;
    gen_memcpy_kernel = gen_memcpy_kerneldi;
  }
  else if((align & 3) == 0){
    mode = SImode;
    size = 4;
    log2size = 2;
    gen_memcpy_kernel = gen_memcpy_kernelsi;
  }
  else if((align & 1) == 0){
    mode = HImode;
    size = 2;
    log2size = 1;
    gen_memcpy_kernel = gen_memcpy_kernelhi;
  }
  else {
    mode = QImode;
    size = 1;
    log2size = 0;
    gen_memcpy_kernel = gen_memcpy_kernelqi;
  }

  src_mem = change_address(src_0, mode, src_reg);
  dst_mem = change_address(dst_0, mode, dst_reg);

  /* Only form a loop if it would execute for at least two iterations. */
  loopcount = count >> log2size;
  if(loopcount > 2){

    /* If the source or destination might be volatile, then load and store
       serially inside the loop.  Otherwise, software pipeline the loop. */

    value_reg = gen_reg_rtx(mode);
    count_reg = gen_reg_rtx(SImode);
    doloop_fixup_code = GEN_INT (REGNO (count_reg));
    loopcount_rtx = gen_int_mode(volatile_p ? loopcount : loopcount - 1,
                                 SImode);
    label = gen_label_rtx();

    if(!volatile_p){
      emit_move_insn(value_reg, src_mem);
      emit_insn(gen_addsi3(src_reg, src_reg, gen_int_mode(size, Pmode)));
    }

    if(TARGET_HARDWARE_LOOPS){
      emit_insn(gen_doloop_begin0(loopcount_rtx, doloop_fixup_code));
    }
    else {
      emit_move_insn(count_reg, loopcount_rtx);
    }

    emit_label(label);

    if(volatile_p){
      emit_move_insn(value_reg, src_mem);
      emit_move_insn(dst_mem, value_reg);
    }
    else {
      emit_insn(gen_memcpy_kernel(dst_mem, value_reg, value_reg, src_mem));
    }
    emit_insn(gen_addsi3(dst_reg, dst_reg, gen_int_mode(size, Pmode)));
    emit_insn(gen_addsi3(src_reg, src_reg, gen_int_mode(size, Pmode)));

    if(TARGET_HARDWARE_LOOPS){
      emit_jump_insn(gen_endloop0(label, doloop_fixup_code));
      hexagon_hardware_loop();
    }
    else {
      rtx pred = gen_reg_rtx(BImode);
      emit_insn(gen_addsi3(count_reg, count_reg, constm1_rtx));
      emit_insn(gen_cmpsi_eq(pred, count_reg, const0_rtx));
      emit_jump_insn(gen_cond_jump(gen_rtx_EQ (BImode, pred, const0_rtx),
                                   pred, label));
    }

    if(!volatile_p){
      emit_move_insn(dst_mem, value_reg);
      emit_insn(gen_addsi3(dst_reg, dst_reg, gen_int_mode(size, Pmode)));
    }

  }
  else {
    for(; loopcount; loopcount--){

      value_reg = gen_reg_rtx(mode);

      emit_move_insn(value_reg, src_mem);
      emit_insn(gen_addsi3(src_reg, src_reg, gen_int_mode(size, Pmode)));
      emit_move_insn(dst_mem, value_reg);
      emit_insn(gen_addsi3(dst_reg, dst_reg, gen_int_mode(size, Pmode)));

    }
  }

  /* Copy any leftovers. */
  if((align & 7) == 0 && count & 4){

    value_reg = gen_reg_rtx(SImode);
    src_mem = change_address(src_0, SImode, src_reg);
    dst_mem = change_address(dst_0, SImode, dst_reg);

    emit_move_insn(value_reg, src_mem);
    emit_insn(gen_addsi3(src_reg, src_reg, gen_int_mode(4, Pmode)));
    emit_move_insn(dst_mem, value_reg);
    emit_insn(gen_addsi3(dst_reg, dst_reg, gen_int_mode(4, Pmode)));

  }
  if(count & 2){

    value_reg = gen_reg_rtx(HImode);
    src_mem = change_address(src_0, HImode, src_reg);
    dst_mem = change_address(dst_0, HImode, dst_reg);

    emit_move_insn(value_reg, src_mem);
    emit_insn(gen_addsi3(src_reg, src_reg, gen_int_mode(2, Pmode)));
    emit_move_insn(dst_mem, value_reg);
    emit_insn(gen_addsi3(dst_reg, dst_reg, gen_int_mode(2, Pmode)));

  }
  if(count & 1){

    value_reg = gen_reg_rtx(QImode);
    src_mem = change_address(src_0, QImode, src_reg);
    dst_mem = change_address(dst_0, QImode, dst_reg);

    emit_move_insn(value_reg, src_mem);
    emit_move_insn(dst_mem, value_reg);

  }
}




/* Tree nodes for specialized block-move functions */

static GTY(()) tree hexagon_memcpy_volatile;
static GTY(()) tree hexagon_memcpy_likely_aligned8_min32_mult8;

/* Emits RTL to perform a block move or returns false.  OPERANDS[0] is a MEM
   containing the destination address.  OPERANDS[1] is a MEM containing the
   source address.  OPERANDS[2] is a CONST_INT containing the number of bytes to
   be copied.  OPERANDS[3] is a CONST_INT containing the guaranteed minimum
   alignment of both the source and destination addresses.  OPERANDS[6] is a
   CONST_INT with a non-zero value only if the block move may be performed via a
   tail call. */

bool
hexagon_expand_movmem(rtx operands[])
{
  HOST_WIDE_INT length, align;
  int cycles, leftovers;
  bool volatile_p, simple_copy_p;
  const int O3_inline_cycle_threshold = 10;
  const int O2_inline_cycle_threshold = 5;
  const int likely_aligned_cycle_threshold = 100;

  volatile_p = !TARGET_V4_FEATURES
               && (MEM_VOLATILE_P (operands[0]) || MEM_VOLATILE_P (operands[1])
                   || !hexagon_dual_memory_accesses);

  align = MIN (INTVAL (operands[3]), BIGGEST_ALIGNMENT / BITS_PER_UNIT);
  if(GET_CODE (operands[2]) == CONST_INT){
    length = INTVAL (operands[2]);
    length &= 0xFFFFFFFFLL;
    simple_copy_p = (length <= align && exact_log2(length) != -1)
                    || length == 0;
  }
  else {
    length = -1;
    simple_copy_p = false;
  }
  gcc_assert(length >= -1);
  gcc_assert((align & (align - 1)) == 0);

  cycles = length / align + 1;
  for(leftovers = length & (align - 1); leftovers; leftovers >>= 1){
    cycles += leftovers & 1;
  }

  if(optimize
     && (simple_copy_p
         || (!optimize_size
             && (align & 3) == 0
             && length != -1
             && cycles <= (optimize >= 3 ? O3_inline_cycle_threshold
                                         : O2_inline_cycle_threshold)))){
    hexagon_expand_movmem_inline(operands, volatile_p);
    return true;
  }

  if(optimize && !volatile_p
     && (align & 3) == 0 && length >= 32 && length % 8 == 0
     && cycles < likely_aligned_cycle_threshold){
    hexagon_emit_special_case_memcpy_fn(&hexagon_memcpy_likely_aligned8_min32_mult8,
                                      "__qdsp_memcpy_likely_aligned_min32bytes_mult8bytes",
                                      operands[0], operands[1], operands[2],
                                      INTVAL (operands[6]));
    return true;
  }

  if(volatile_p){
    hexagon_emit_special_case_memcpy_fn(&hexagon_memcpy_volatile, "memcpy_v",
                                      operands[0], operands[1], operands[2],
                                      INTVAL (operands[6]));
    return true;
  }

  return false;
}

/* Block set instruction. The destination string is the first operand, given as a 
   mem:BLK whose address is in mode Pmode. The number of bytes to set is the second operand, 
   in mode m. The value to initialize the memory with is the third operand. Targets that only 
   support the clearing of memory should reject any value that is not the constant 0.

   The fourth operand is the known alignment of the destination, in the form of a const_int rtx. 
   Thus, if the compiler knows that the destination is word-aligned, it may provide the value 4 for this operand.

   Optional operands 5 and 6 specify expected alignment and size of block respectively. The expected 
   alignment differs from alignment in operand 4 in a way that the blocks are not required to be aligned 
   according to it in all cases. This expected alignment is also in bytes, just like operand 4. Expected 
   size, when unknown, is set to (const_int -1). 

   Implementation details-
   1. From the alignment, figure out all valid modes which can be used to set memory. For example-
      a. alignment == 4  -> valid modes (QI, HI, SI)
      b. aligment == 128 -> valid modes (QI, HI, SI, DI)

   2. Now loop thru all valid modes starting from the widest to the narrowest-
      a. calculate loop count = bytes-to-copy / mode-size
      b. if loop count == 0 -> not enough bytes to store
      c. if loop count == 1 -> do simple store
      d. if loop count > 1  -> do hardware loop
*/

bool
hexagon_expand_setmem(rtx operands[])
{
#define MEMSET_LIBCALL_THRESHOLD 64
  HOST_WIDE_INT align_intval, nbytes_intval, initval_intval;
  rtx destaddr, nbytes, initval, align;

  destaddr = operands[0];
  nbytes = operands[1];
  initval = operands[2];
  align = operands[3];

  /* Sanity checks */
  gcc_assert(destaddr && nbytes && initval);

  /* nbytes should be constant */
  if (GET_CODE(nbytes) != CONST_INT)
    return false;

  /* align should be constant. We should probably assert but... */
  if (GET_CODE(align) != CONST_INT)
    return false;

  /* initval should be constant. */
  if (GET_CODE(initval) != CONST_INT)
    return false;

  align_intval = INTVAL(align);
  nbytes_intval = INTVAL(nbytes);
  initval_intval = INTVAL(initval);

  /* If nothing to set or large memory (memset might optimize it better), return */
  if (nbytes_intval <= 0 || nbytes_intval > MEMSET_LIBCALL_THRESHOLD)
    return false;

  /* If not clearing memory, return */
  if (initval_intval != 0)
    return false;

  /* Now starting from the narrowest mode, figure out all valid modes */
  enum machine_mode valid_modes[MAX_MODE_INT-MIN_MODE_INT+1] = {VOIDmode};
  enum machine_mode curr_mode;
  int index = 0;

  /* Step 1. See comments above */
  for (curr_mode = GET_CLASS_NARROWEST_MODE(MODE_INT); curr_mode != VOIDmode;
       curr_mode = GET_MODE_WIDER_MODE(curr_mode))
    {
      /* Is mode supported */
      if (!targetm.scalar_mode_supported_p(curr_mode))
        continue;

      /* Make sure alignment does not exceed align */
      if (GET_MODE_SIZE(curr_mode) > align_intval)
        break;

      valid_modes[index++] = curr_mode;
    }

  /* Index must be non-zero */
  gcc_assert(index);

  /* Get the base pointer */
  rtx base_reg = copy_to_mode_reg(SImode, XEXP(destaddr, 0));
  int nbytes_left = nbytes_intval;
  /* Step 2. Starting from the widest mode, generate hardware loop stores */
  for (index = index-1; index >= 0; index--)
    {
      rtx store_reg, label;
      curr_mode = valid_modes[index];
      int loop_count = nbytes_left / GET_MODE_SIZE(curr_mode);
      /* Size is smaller than the alignment */
      if (loop_count == 0)
          continue;

      /* r = #0 */
      rtx zero_reg = gen_reg_rtx(curr_mode);
      emit_move_insn(zero_reg, initval);

      if (loop_count == 1)
        {
          /* Simple store */
          store_reg = gen_rtx_MEM(curr_mode, base_reg);
          MEM_COPY_ATTRIBUTES(store_reg, destaddr);
          emit_move_insn(store_reg, zero_reg);

          /* Increment the base pointer */
          emit_insn(gen_addsi3(base_reg, base_reg, 
                               gen_int_mode(GET_MODE_SIZE(curr_mode), SImode)));
        }
      else
        {
          /* Hardware loop */
          store_reg = gen_rtx_MEM(curr_mode, base_reg);
          MEM_COPY_ATTRIBUTES(store_reg, destaddr);
          label = gen_label_rtx();
          /* Hack for hardware loop */
          rtx count_reg = gen_reg_rtx(SImode);
          rtx doloop_fixup_code = GEN_INT(REGNO(count_reg));
          rtx loopcount_rtx = gen_int_mode(loop_count, SImode);

          emit_insn(gen_doloop_begin0(loopcount_rtx, doloop_fixup_code));
          emit_label(label);
          emit_move_insn(store_reg, zero_reg);
          emit_insn(gen_addsi3(base_reg, base_reg, 
                               gen_int_mode(GET_MODE_SIZE(curr_mode), SImode)));
          emit_jump_insn(gen_endloop0(label, doloop_fixup_code));
          hexagon_hardware_loop();
        }

      /* Count leftover */
      nbytes_left = nbytes_left % GET_MODE_SIZE(curr_mode);
    }
  gcc_assert(nbytes_left == 0);
  return true;
}


/* Determine a static branch hint for INSN.  Return the hint in the form of a
   CONST_INT rtx.  Non-zero means "predict taken" and zero means "predict not
   taken". */

rtx
hexagon_branch_hint(rtx insn)
{
  rtx note = find_reg_note(insn, REG_BR_PROB, 0);
  return GEN_INT (note && INTVAL (XEXP (note, 0)) > REG_BR_PROB_BASE / 2);
}




void
hexagon_hardware_loop(void)
{
  cfun->machine->has_hardware_loops++;
}




/*--------------------------------------------
Functions for forming and manipulating packets
--------------------------------------------*/

void
hexagon_print_insn_info(FILE *file, struct hexagon_insn_info *insn_info)
{
  struct hexagon_reg_access *reg_access;
  struct hexagon_mem_access *mem_access;
  bool first;

  if(insn_info == NULL){
    fputs("!!!! NULL INSN_INFO !!!!\n", file);
    return;
  }

  fputs(";; condition: ", file);
  if(HEXAGON_GPR_CONDITION_P (insn_info)){
    fputs("gpr", file);
  }
  else if(HEXAGON_SENSE (insn_info) == HEXAGON_UNCONDITIONAL){
    fputs("unconditional", file);
  }
  else if(HEXAGON_SENSE (insn_info) == 0){
    fputs("never", file);
  }
  else {
    if(HEXAGON_SENSE (insn_info) == HEXAGON_IF_FALSE){
      fputc('!', file);
    }
    fputs(reg_names[P0_REGNUM + HEXAGON_PREDICATE (insn_info)], file);
    if(HEXAGON_NEW_PREDICATE_P (insn_info)){
      fputs(".new", file);
    }
  }
  fputc('\n', file);

  fputs(";; control: ", file);
  if(HEXAGON_CONTROL_P (insn_info)){
    if(HEXAGON_DIRECT_JUMP_P (insn_info)){
      fputs("jump", file);
    }
    if(HEXAGON_INDIRECT_JUMP_P (insn_info)){
      fputs("indirect jump", file);
    }
    if(HEXAGON_DIRECT_CALL_P (insn_info)){
      fputs("call", file);
    }
    if(HEXAGON_INDIRECT_CALL_P (insn_info)){
      fputs("indirect call", file);
    }
    if(HEXAGON_ENDLOOP_P (insn_info)){
      fputs("endloop", file);
    }
  }
  else {
    fputs("none", file);
  }
  fputc('\n', file);

  fputs(";; flags: (", file);
  first = true;
  if(HEXAGON_EMULATION_CALL_P (insn_info)){
    fputs("emulation_call", file);
    first = false;
  }
  if(HEXAGON_VOLATILE_P (insn_info)){
    if(!first){
      fputs(", ", file);
    }
    fputs("volatile", file);
    first = false;
  }
  if(HEXAGON_MEM_P (insn_info)){
    if(!first){
      fputs(", ", file);
    }
    fputs("mem", file);
    first = false;
  }
  if(HEXAGON_NEW_GPR_P (insn_info)){
    if(!first){
      fputs(", ", file);
    }
    fputs("gpr.new", file);
  }
  fputs(")\n", file);

  fputs(";; register reads:", file);
  first = true;
  reg_access = insn_info->reg_reads;
  while(reg_access){
    if(!first){
      fputc(',', file);
    }
    fputc(' ', file);
    fputs(reg_names[reg_access->regno], file);
    first = false;
    reg_access = reg_access->next;
  }
  if(first){
    fputs(" none", file);
  }
  fputc('\n', file);

  fputs(";; register writes:", file);
  first = true;
  reg_access = insn_info->reg_writes;
  while(reg_access){
    if(!first){
      fputc(',', file);
    }
    fputc(' ', file);
    fputs(reg_names[reg_access->regno], file);
    first = false;
    reg_access = reg_access->next;
  }
  if(first){
    fputs(" none", file);
  }
  fputc('\n', file);

  fputs(";; loads:", file);
  first = true;
  mem_access = insn_info->loads;
  while(mem_access){
    if(first){
      fputc('\n', file);
    }
    print_rtl_single(file, mem_access->mem);
    first = false;
    mem_access = mem_access->next;
  }
  if(first){
    fputs(" none\n", file);
  }

  fputs(";; stores:", file);
  first = true;
  mem_access = insn_info->stores;
  while(mem_access){
    if(first){
      fputc('\n', file);
    }
    print_rtl_single(file, mem_access->mem);
    first = false;
    mem_access = mem_access->next;
  }
  if(first){
    fputs(" none\n", file);
  }

  fputs(";; insn:\n", file);
  print_rtl_single(file, insn_info->insn);
}




void
hexagon_debug_insn_info(struct hexagon_insn_info *insn_info)
{
  hexagon_print_insn_info(stderr, insn_info);
}




void
hexagon_print_packet(FILE *file, struct hexagon_packet_info *packet)
{
  int i;

  if(packet == NULL){
    fputs("!!!! NULL PACKET !!!!\n", file);
    return;
  }

  fputs(";; ==== BEGIN PACKET ====\n", file);
  for(i = 0; i < packet->num_insns && i < HEXAGON_MAX_INSNS_PER_PACKET; i++){
    hexagon_print_insn_info(file, packet->insns[i]);
  }
  fputs(";; ==== END PACKET ====\n", file);
}




void
hexagon_print_packets(FILE *file, struct hexagon_packet_info *packet)
{
  if(packet == NULL){
    hexagon_print_packet(file, packet);
    return;
  }

  do {
    hexagon_print_packet(file, packet);
    packet = packet->next;
  }while(packet);
}




void 
hexagon_debug_packets(void)
{
  basic_block bb;
  FOR_EACH_BB(bb)
  {
    struct hexagon_packet_info *packet;
    packet = BB_HEAD_PACKET(bb);
    hexagon_print_packets(stderr, packet);
  }
}




void
hexagon_debug_packet(struct hexagon_packet_info *packet)
{
  hexagon_print_packet(stderr, packet);
}




void
hexagon_print_bb_packets(FILE *file, basic_block bb)
{
  struct hexagon_packet_info *packet;

  dump_bb_info(bb, true, false, TDF_DETAILS, ";; ", file);
  packet = BB_HEAD_PACKET (bb);
  if(packet){
    fputs("\n;; sentinel packet:\n", file);
    hexagon_print_packet(file, packet->prev);
  }
  fputc('\n', file);
  while(packet && packet != BB_END_PACKET (bb)){
    hexagon_print_packet(file, packet);
    packet = packet->next;
  }
  hexagon_print_packet(file, packet);
  dump_bb_info(bb, false, true, TDF_DETAILS, ";; ", file);
  fputs("\n\n", file);
}




void
hexagon_debug_bb_packets(basic_block bb)
{
  hexagon_print_bb_packets(stderr, bb);
}




void
hexagon_debug_all_bb_packets(void)
{
  basic_block bb;

  FOR_EACH_BB (bb){
   hexagon_debug_bb_packets(bb);
  }
}




static int
hexagon_get_flags(rtx insn)
{
  int flags = 0;
  rtx pattern;
  rtx test;
  rtx target;

  pattern = PATTERN (insn);
  if(GET_CODE (pattern) == PARALLEL){
    pattern = XVECEXP (pattern, 0, 0);
  }

  if(GET_CODE (pattern) == COND_EXEC){
    test = COND_EXEC_TEST (pattern);
  }
  else if(JUMP_P (insn) && GET_CODE (pattern) == SET
          && GET_CODE (SET_SRC (pattern)) == IF_THEN_ELSE){

    test = XEXP (SET_SRC (pattern), 0);

    if(C_REG_P (XEXP (test, 0))){
      flags |= HEXAGON_ENDLOOP;
      test = NULL_RTX;
    }
  }
  else {
    test = NULL_RTX;
  }

  if(test){
    if(P_REG_P (XEXP (test, 0))){
      flags |= REGNO (XEXP (test, 0)) - P0_REGNUM;
      flags |= GET_CODE (test) == NE ? HEXAGON_IF_TRUE : HEXAGON_IF_FALSE;
    }
    else {
      flags |= HEXAGON_GPR_CONDITION | HEXAGON_UNCONDITIONAL;
    }
  }
  else {
    flags |= HEXAGON_UNCONDITIONAL;
  }

  if ( INSN_CODE (insn) == CODE_FOR_compare_and_jump1 ||
       INSN_CODE (insn) == CODE_FOR_compare_and_jump2 )
  {
    flags |= HEXAGON_NEW_PREDICATE;
  }

  if(JUMP_P (insn) && !(flags & HEXAGON_ENDLOOP) ){
    if(GET_CODE (pattern) == RETURN){
      flags |= HEXAGON_INDIRECT_JUMP;
    }
    else {
      gcc_assert(GET_CODE (pattern) == SET);
      target = SET_SRC (pattern);
      if(GET_CODE (target) == IF_THEN_ELSE){
        target = XEXP (target, 1);
      }

      if(GET_CODE (target) == LABEL_REF){
        flags |= HEXAGON_DIRECT_JUMP;
      }
      else {
        flags |= HEXAGON_INDIRECT_JUMP;
      }
    }
  }
  else if(CALL_P (insn)){
    if(GET_CODE (pattern) == SET){
      pattern = SET_SRC (pattern);
    }

    gcc_assert(GET_CODE (pattern) == CALL && MEM_P (XEXP (pattern, 0)));
    if(REG_P (XEXP (XEXP (pattern, 0), 0))){
      flags |= HEXAGON_INDIRECT_CALL;
    }
    else {
      flags |= HEXAGON_DIRECT_CALL;
    }
  }
  /* Ignore instructions that do nothing */
  else if ((GET_CODE (PATTERN (insn)) == CLOBBER) ||
	   (GET_CODE (PATTERN (insn)) == USE) || 
	   (GET_CODE (PATTERN (insn)) == ADDR_VEC) ||
	   (GET_CODE (PATTERN (insn)) == ADDR_DIFF_VEC))
    {
      /* do nothing */
    }
  else if(get_attr_emulation_call(insn) == EMULATION_CALL_YES){
    flags |= HEXAGON_EMULATION_CALL;
  }

  return flags;
}




static struct hexagon_reg_access *
hexagon_add_reg_access(struct hexagon_reg_access *accesses, rtx reg, int flags)
{
  struct hexagon_reg_access *access;
  unsigned int regno;
  unsigned int next_hard_regno;

  /* Ignore duplicates. */
  for(access = accesses; access; access = access->next){
    if(rtx_equal_p(reg, access->reg)){
      return accesses;
    }
  }

  regno = REGNO (reg);
  next_hard_regno = regno + HARD_REGNO_NREGS (regno, GET_MODE (reg));
  for(; regno < next_hard_regno; regno++){
    access = (struct hexagon_reg_access *)ggc_alloc_cleared(sizeof(struct hexagon_reg_access));
    access->reg = reg;
    access->regno = regno;
    access->flags = flags;
    access->next = accesses;
    accesses = access;
  }
  return accesses;
}




static struct hexagon_mem_access *
hexagon_add_mem_access(struct hexagon_mem_access *accesses, rtx mem, int flags)
{
  struct hexagon_mem_access *access;

  /* Ignore duplicates. */
  for(access = accesses; access; access = access->next){
    if(rtx_equal_p(mem, access->mem)){
      return accesses;
    }
  }

  access = (struct hexagon_mem_access *)ggc_alloc_cleared(sizeof(struct hexagon_mem_access));
  access->mem = mem;
  access->flags = flags;
  access->next = accesses;
  return access;
}




static int
hexagon_record_writes(rtx *y, void *info)
{
  rtx x;
  struct hexagon_insn_info *insn_info;

  x = *y;
  insn_info = (struct hexagon_insn_info *) info;

  switch(GET_CODE (x)){
    case MEM:
      insn_info->stores = hexagon_add_mem_access(insn_info->stores,
                                               x,
                                               insn_info->flags);
      insn_info->flags |= HEXAGON_MEM;
      if(MEM_VOLATILE_P (x)){
        insn_info->flags |= HEXAGON_VOLATILE;
      }
      for_each_rtx(&XEXP (x, 0), hexagon_record_reads, insn_info);
      return -1;
    case REG:
      insn_info->reg_writes = hexagon_add_reg_access(insn_info->reg_writes,
                                                   x,
                                                   insn_info->flags);
      return 0;
    default:
      return 0;
  }
}




static int
hexagon_record_reads(rtx *y, void *info)
{
  rtx x;
  struct hexagon_insn_info *insn_info;
  int saved_flags;

  x = *y;
  insn_info = (struct hexagon_insn_info *) info;

  switch(GET_CODE (x)){
    case COND_EXEC:
      saved_flags = insn_info->flags;
      insn_info->flags = HEXAGON_UNCONDITIONAL;
      for_each_rtx(&COND_EXEC_TEST (x), hexagon_record_reads, insn_info);
      insn_info->flags = saved_flags;
      for_each_rtx(&COND_EXEC_CODE (x), hexagon_record_reads, insn_info);
      return -1;
    case SET:
      /* V2/V3/V4 insert instruction is unusual in the way that it reads and
         writes its destination, so we need to record reads here
         as a special case.
         (set (zero_extract (...) (...) (...)) (...)) */
      if(XEXP (x, 0) && GET_CODE (XEXP (x, 0)) == ZERO_EXTRACT){
          for_each_rtx(&XEXP (x, 0), hexagon_record_reads, insn_info);
      }
      /* fall through */
    case POST_MODIFY:
      if(GET_CODE (XEXP (x, 1)) != CALL){
        for_each_rtx(&XEXP (x, 0), hexagon_record_writes, insn_info);
      }
      for_each_rtx(&XEXP (x, 1), hexagon_record_reads, insn_info);
      return -1;
    case CALL:
      gcc_assert(MEM_P (XEXP (x, 0)));
      for_each_rtx(&XEXP (XEXP (x, 0), 0), hexagon_record_reads, insn_info);
      return -1;
    case CLOBBER:
      for_each_rtx(&XEXP (x, 0), hexagon_record_writes, insn_info);
      return -1;
    case POST_DEC:
    case POST_INC:
      for_each_rtx(&XEXP (x, 0), hexagon_record_writes, insn_info);
      return 0;
    case MEM:
      insn_info->loads = hexagon_add_mem_access(insn_info->loads,
                                              x,
                                              insn_info->flags);
      insn_info->flags |= HEXAGON_MEM;
      if(MEM_VOLATILE_P (x)){
        insn_info->flags |= HEXAGON_VOLATILE;
      }
      return 0;
    case REG:
      insn_info->reg_reads = hexagon_add_reg_access(insn_info->reg_reads,
                                                  x,
                                                  insn_info->flags);
      return 0;
    case RETURN:
      if(!HEXAGON_CALL_P (insn_info)){
        insn_info->reg_reads = hexagon_add_reg_access(insn_info->reg_reads,
                                                    gen_rtx_REG (word_mode,
                                                                 LINK_REGNUM),
                                                    insn_info->flags);
      }
      return 0;
    default:
      return 0;
  }
}




static struct hexagon_insn_info *
hexagon_get_insn_info(rtx insn)
{
  struct hexagon_insn_info *insn_info;

  insn_info = (struct hexagon_insn_info *)ggc_alloc_cleared(sizeof(struct hexagon_insn_info));

  insn_info->insn = insn;
  insn_info->flags = hexagon_get_flags(insn);

  /* Record accesses. */
  for_each_rtx(&PATTERN (insn), hexagon_record_reads, insn_info);

  /* Transfers of immediate values that cannot be encoded in a transfer
     immediate instruction are implemented as GP-relative loads. */
  if ((GET_CODE (PATTERN (insn)) == CLOBBER) ||
      (GET_CODE (PATTERN (insn)) == USE) || 
      (GET_CODE (PATTERN (insn)) == ADDR_VEC) ||
      (GET_CODE (PATTERN (insn)) == ADDR_DIFF_VEC))
    {
      /* do nothing */
    }
  else if (get_attr_type(insn) == TYPE_LOAD)
    {
      insn_info->flags |= HEXAGON_MEM;
    }
  
  return insn_info;
}


/* Given register reg, return its corresponding pair register */
static inline unsigned int 
get_pair_reg(unsigned int regno)
{
  return (regno & 0x1) ? regno - 1 : regno + 1;
}


/* 
   Given a vector tranfer_source that maps register numbers to insn pointers:
   Iterate through the vector.
   If an element of the vector is a register copy with orig_reg as a source, 
   replace that element with replacement 
*/
static void
hexagon_replace_transfer_map(VEC(rtx, gc)* transfer_source, unsigned orig_reg, 
			   rtx replacement)
{
  unsigned int iter;

  gcc_assert((replacement == NULL_RTX) || INSN_P(replacement));

  for (iter = 0; iter <  FIRST_PSEUDO_REGISTER; ++iter) 
    {
      rtx element = VEC_index(rtx, transfer_source, iter);
      if (element != NULL_RTX) 
	{
	  rtx element_source = SET_SRC (single_set (element));
	  if (REG_P (element_source) && 
	      (REGNO (element_source) == orig_reg))
	    {
	      VEC_replace(rtx, transfer_source, iter, replacement);
	    }
	}
    }
}


/* Predicate that returns true if insn is a register-to-register or
   a register-to-immediate copy */
static inline bool 
hexagon_register_copy_word_p (rtx insn)
{
  rtx reg_copy;
  bool dest_reg, src_reg_imm;
  if (!insn || (!(reg_copy = single_set(insn))))
    {
      return false;
    }
  
  dest_reg = gr_register_operand(SET_DEST (reg_copy), SImode);
  src_reg_imm = gr_register_operand(SET_SRC (reg_copy), SImode) || 
    const_int_operand(SET_SRC (reg_copy), SImode);

  return (dest_reg && src_reg_imm);
}

/* Predicate that checks if REG is a lower component of a pair register */
#define HEXAGON_LOWER_PAIR(REG)         (!(REG & 0x1))


/* 
   Pass that scans through all basic blocks and changes register-register
   and register-immediate transfers into combine instructions where possible.
   For instance, it combines:
   r0 = r3
   ...
   r1 = r4
   into r1:0 = combine(r4,r3)

   High-level overview of the pass:
   --------------------------------
   Iterate over all instructions I in the basic block. 
   Maintain a map M from register number to insn pointer of the last write 
   of that register
   For all register reads, R, clear map(R)
   Consider all transfer instructions of the form rx = y, where rx is a 
   register and y is a register or an immediate
   Consult the map to verify if the corresponding pair register for rx
   was written to by a transfer. If so, replace the transfers with a combine
   instruction
   For all non-transfer instructions, iterate over the register writes
   and invalidate the corresponding entry in the map
*/
static void
hexagon_local_combine_pass(void) 
{
  rtx insn;
  basic_block bb;
  rtx head_insn;
  rtx end_insn;

  /* transfer_source: vector that holds the sources used by a transfer 
     instruction. The index is the physical register defined by the transfer. 
     The vector element is the rtx of the source used by the transfer 
     instruction. 
     This vector depends on NULL_RTX being defined to 0
  */
  VEC(rtx, gc) *transfer_source = NULL;
  VEC_safe_grow_cleared(rtx, gc, transfer_source, FIRST_PSEUDO_REGISTER);  
  
  FOR_EACH_BB(bb)
    {
      rtx combine_insn;
      head_insn = BB_HEAD (bb);
      end_insn = BB_END (bb);
      insn = head_insn;

      /* Reset the vector */
      VEC_truncate(rtx, transfer_source, 0);
      VEC_safe_grow_cleared(rtx, gc, transfer_source, FIRST_PSEUDO_REGISTER);
      
      FOR_BB_INSNS (bb, insn)
	{
	  struct hexagon_insn_info *insn_info;
	  struct hexagon_reg_access *read;
	  struct hexagon_reg_access *write;

	  /* Only process instructions */
	  if (!INSN_P(insn)) 
	    {
	      continue;
	    }
	  insn_info = hexagon_get_insn_info(insn);

	  /* Process all instructions -- transfers and non-transfers. If the 
	     instruction is reading the register. Remove from map. This condition
	     must be checked before processing register copies. Else, the code will
	     incorrectly handle this situation:
	     r1 = r25
	     r0 = r1   ;; We must invalidate r1 before processing this instruction
                       ;; We cannot insert a r1:0=combine(r25,r1) here
	  */
	  for(read = insn_info->reg_reads; read; read = read->next)
	    {
	      VEC_replace(rtx, transfer_source, read->regno, NULL_RTX);
	    }
	  

	  if (hexagon_register_copy_word_p (insn))
	    {
	      rtx source;
	      unsigned int dest_pair_regno;
	      rtx dest_pair_insn, source_pair;
	      unsigned int dest_regno = REGNO (SET_DEST(single_set (insn)));
	      gcc_assert(dest_regno < FIRST_PSEUDO_REGISTER);

	      /* Get the source for this transfer instruction */
	      source = SET_SRC (single_set (insn));
	      VEC_replace(rtx, transfer_source, dest_regno, insn);

	      /* A register has been defined. If that register is an element of
		 transfer_source, we can no longer consider that transfer to be valid.
		 Invalidate that element */
	      hexagon_replace_transfer_map (transfer_source, dest_regno, NULL_RTX);
	      
	      /* Get the pair register for dest_regno */
	      dest_pair_regno = get_pair_reg(dest_regno);
	      if ((dest_pair_insn = VEC_index(rtx, transfer_source, dest_pair_regno)))
		{
		  enum machine_mode dummy_mode = VOIDmode;
		  source_pair = SET_SRC (single_set (dest_pair_insn));

		  /* Check if the sources for transfer instructions defining the pair are either:
		     1. Both registers, in which case we can use combine(reg, reg), or
		     2. Both immediates, in which case we can use combine(imm, imm)
		  */
		  /*
		        To consider: Can I make the int operand belongs to s8 code more generic?
		  */
		  if ((REG_P (source_pair) && REG_P (source)) || 
		      (CONST_INT_P (source_pair) && CONST_INT_P (source) && 
		       s8_const_int_operand(source, dummy_mode) && 
		       s8_const_int_operand(source_pair, dummy_mode)))
		    {
		      rtx dest_reg_rtx  = gen_rtx_REG(SImode, dest_regno);
		      rtx dest_pair_rtx = gen_rtx_REG(SImode, dest_pair_regno);
		      
		      /* Check if the current instruction defines the lower or the higher pair
			 and create the appropriate combine instruction */
		      if (HEXAGON_LOWER_PAIR (dest_regno))
			{
			  combine_insn = 
			    emit_insn_after( gen_combinesi (dest_pair_rtx, 
							    source_pair, 
							    dest_reg_rtx,
							    source), 
					     insn);
			}
		      else 
			{
			  combine_insn = 
			    emit_insn_after( gen_combinesi (dest_reg_rtx, 
							    source, 
							    dest_pair_rtx,
							    source_pair), 
					     insn);
			}

		      delete_insn(insn);
		      /* If this pass hasn't already deleted dest_pair_insn, then 
			 delete it
			 This can happen if dest_pair_insn has been replaced with a combine,
			 and then the defined register is used in another replacement */
		      if (!INSN_DELETED_P (dest_pair_insn)) 
			{
			  delete_insn(dest_pair_insn);
			}
		      insn = combine_insn;
		    }
		}
	    } /* hexagon_is_register_copy */
	  else 
	    {
	      /* For Call instructions we need to invalidate all caller-saved registers */
	      if (CALL_P(insn)) {
		unsigned int i;
		for (i = 0; i < VEC_length(rtx, transfer_source); ++i) 
		  {
		    if (call_used_regs[i])
		      {
			VEC_replace(rtx, transfer_source, i, NULL_RTX); 
			/* If any element of the vector contains a caller-save register
			   invalidate that entry */
			hexagon_replace_transfer_map (transfer_source, i, NULL_RTX);
		      }
		  }
	      }

	      /* An non-transfer instruction is writing to a register. Remove from map */
	      for(write = insn_info->reg_writes; write; write = write->next)
		{
		  unsigned int defined_reg = write->regno;
		  
		  VEC_replace(rtx, transfer_source, defined_reg, NULL_RTX);
		  /* Register defined_reg is redefined. Iterate through vector and remove all 
		     occurrences of register defined_reg as a source 
		     
		     This can be made more efficient by maintaining a map of regno to 
		     a list of indices in transfer_source that contain regno as an 
		     element */
		  hexagon_replace_transfer_map(transfer_source, defined_reg, NULL_RTX); 
		}
	    }
	}
    }
}


static struct hexagon_packet_info *
hexagon_start_new_packet(void)
{
  struct hexagon_packet_info *new_packet;

  new_packet = (struct hexagon_packet_info *)ggc_alloc_cleared(sizeof(struct hexagon_packet_info));

  if(hexagon_head_packet == NULL){
    hexagon_head_packet = new_packet;
  }
  else {
    gcc_assert(hexagon_tail_packet);
    hexagon_tail_packet->next = new_packet;
    new_packet->prev = hexagon_tail_packet;
  }
  hexagon_tail_packet = new_packet;

  return new_packet;
}




/* Add INSN_INFO to PACKET.  If ADD_TO_BEGINNING is true, the add INSN_INFO to
   the beginning of PACKET.  If ADD_TO_BEGINNING is false and INSN_INFO is not a
   control insn, then add INSN_INFO above any jump insns already in PACKET.  If
   ADD_TO_BEGINNING is false and INSN_INFO is a control insn, then add INSN_INFO
   above any unconditional jumps in PACKET, but below any conditional jumps in
   PACKET. */

static void
hexagon_add_insn_to_packet(
  struct hexagon_packet_info *packet,
  struct hexagon_insn_info *insn_info,
  bool add_to_beginning
)
{
  int i;

  gcc_assert(packet->num_insns < HEXAGON_MAX_INSNS_PER_PACKET);

  if(!packet->location){
    packet->location = insn_info->insn;
  }

  for(i = packet->num_insns;
      i > 0
      && ((HEXAGON_JUMP_P (packet->insns[i - 1])
           && (!HEXAGON_CONDITIONAL_P (packet->insns[i - 1])
               || !HEXAGON_CONTROL_P (insn_info)))
          || add_to_beginning);
      i--){
    packet->insns[i] = packet->insns[i - 1];
  }
  packet->insns[i] = insn_info;
  packet->num_insns++;
}




static void
hexagon_remove_insn_from_packet(
  struct hexagon_packet_info *packet,
  struct hexagon_insn_info *insn_info
)
{
  int i;

  /* Find the insn. */
  for(i = 0; i < packet->num_insns; i++){
    if(packet->insns[i] == insn_info){
      break;
    }
  }

  /* That insn wasn't in this packet. */
  gcc_assert(i < packet->num_insns);

  /* Remove the insn. */
  for(; i < packet->num_insns - 1; i++){
    packet->insns[i] = packet->insns[i + 1];
  }
  packet->insns[i] = NULL;
  packet->num_insns--;
}




static bool
hexagon_can_speculate_p(struct hexagon_insn_info *insn_info, basic_block bb)
{
  struct hexagon_reg_access *write;

  /* Don't speculate any control insns, stores, or insns that might trap. */
  if(HEXAGON_CONTROL_P (insn_info)
     || insn_info->stores
     || may_trap_or_fault_p(PATTERN (insn_info->insn))){
    return false;
  }

  for(write = insn_info->reg_writes; write; write = write->next){
    if(TEST_HARD_REG_BIT (BB_LIVE_OUT (bb), write->regno)){
      return false;
    }
  }

  return true;
}




static void
hexagon_add_live_out(struct hexagon_insn_info *insn_info, basic_block bb)
{
  struct hexagon_reg_access *write;

  for(write = insn_info->reg_writes; write; write = write->next){
    SET_HARD_REG_BIT (BB_LIVE_OUT (bb), write->regno);
  }
}




static bool
hexagon_predicable_p(struct hexagon_insn_info *insn_info)
{
  rtx cond_exec;

  /* Form a COND_EXEC wrapper around the pattern of the insn to test for
     predicability. */
  cond_exec = gen_rtx_COND_EXEC (VOIDmode,
                                 gen_rtx_NE (BImode,
                                             gen_rtx_REG (BImode, P0_REGNUM),
                                             const0_rtx),
                                 PATTERN (insn_info->insn));
  start_sequence();
  if(JUMP_P (insn_info->insn)){
    emit_jump_insn(cond_exec);
  }
  else if(CALL_P (insn_info->insn)){
    emit_call_insn(cond_exec);
  }
  else {
    emit_insn(cond_exec);
  }
  cond_exec = get_insns();
  end_sequence();

  /* If the predicated version is valid, then the original insn is
     predicable. */
  return !insn_invalid_p(cond_exec);
}




static struct hexagon_insn_info *
hexagon_predicate_insn(
  struct hexagon_insn_info *insn_info,
  struct hexagon_insn_info *jump_insn_info,
  bool invert_condition
)
{
  struct hexagon_insn_info *new_insn_info;
  rtx insn;
  rtx pattern;
  rtx test;
  enum rtx_code test_code;

  pattern = PATTERN (jump_insn_info->insn);
  if(GET_CODE (pattern) == PARALLEL){
    pattern = XVECEXP (pattern, 0, 0);
  }
  test = XEXP (SET_SRC (pattern), 0);
  test_code = GET_CODE (test);
  gcc_assert(test_code == EQ || test_code == NE);
  if(invert_condition){
    test_code = test_code == EQ ? NE : EQ;
  }

  pattern = copy_rtx(PATTERN (insn_info->insn));
  pattern = gen_rtx_COND_EXEC (VOIDmode,
                               gen_rtx_fmt_ee(test_code,
                                              GET_MODE (test),
                                              XEXP (test, 0),
                                              XEXP (test, 1)),
                               pattern);

  start_sequence();
  if(JUMP_P (insn_info->insn)){
    emit_jump_insn(pattern);
  }
  else if(CALL_P (insn_info->insn)){
    emit_call_insn(pattern);
  }
  else {
    emit_insn(pattern);
  }
  insn = get_insns();
  end_sequence();

  new_insn_info = hexagon_get_insn_info(insn);
  new_insn_info->stack = insn_info;

  if(HEXAGON_NEW_PREDICATE_P (insn_info)){
    new_insn_info->flags |= HEXAGON_NEW_PREDICATE;
  }
  if(HEXAGON_NEW_GPR_P (insn_info)){
    new_insn_info->flags |= HEXAGON_NEW_GPR;
  }
  if(HEXAGON_MOVED_P (insn_info)){
    new_insn_info->flags |= HEXAGON_MOVED;
  }
  set_block_for_insn(new_insn_info->insn, BLOCK_FOR_INSN (insn_info->insn));

  return new_insn_info;
}


static bool 
hexagon_can_be_new_value_p(
  struct hexagon_insn_info *producer, 
  struct hexagon_insn_info *consumer,
  struct hexagon_dependence *dependence
)
{
  rtx pattern;
  rtx set;

  /* If the producer is conditional, then consumer must have the same
     condition. */
  if(HEXAGON_CONDITIONAL_P (producer)
     && (HEXAGON_CONDITION (consumer) != HEXAGON_CONDITION (producer)
         || (HEXAGON_NEW_PREDICATE_P (consumer)
             && !HEXAGON_NEW_PREDICATE_P (producer))))
  {
    return false;
  }

  /* The new value must not come from or be a register pair. */
  if(GET_MODE_SIZE (GET_MODE (dependence->set)) > UNITS_PER_WORD
     || GET_MODE_SIZE (GET_MODE (dependence->use)) > UNITS_PER_WORD){
    return false;
  }

  /* The producer may be conditional. */
  pattern = PATTERN (producer->insn);
  if(GET_CODE (pattern) == COND_EXEC){
    pattern = COND_EXEC_CODE (pattern);
  }

  /* The new value must not come from a post-update address. */
  if(GET_CODE (pattern) != SET){
    return false;
  }
  set = SET_DEST (pattern);
  if(GET_CODE (set) == ZERO_EXTRACT){
    set = XEXP (set, 0);
  }
  if(set != dependence->set){
    return false;
  }

  return true;
}


static bool 
hexagon_can_be_new_value_store_p(
  struct hexagon_insn_info *producer, 
  struct hexagon_insn_info *consumer,
  struct hexagon_dependence *dependence
)
{
  if(!TARGET_NEW_VALUE_STORES)
  {
    return false;
  }

  if (!hexagon_can_be_new_value_p(producer, consumer, dependence))
  {
    return false;
  }

  return true;
}

static bool 
hexagon_can_be_new_value_jump_p(
  struct hexagon_insn_info *consumer,
  struct hexagon_dependence *dependence
)
{

  if(!(TARGET_V4_FEATURES && TARGET_NEW_VALUE_JUMP))
  {
    return false;
  }

  if (HEXAGON_DIRECT_JUMP_P(consumer) &&
      (INSN_CODE(consumer->insn) == CODE_FOR_new_value_jump1 ||
       INSN_CODE(consumer->insn) == CODE_FOR_new_value_jump2 ||
       INSN_CODE(consumer->insn) == CODE_FOR_new_value_jump_tstbit) &&
      hexagon_nvj_new_gpr_p(consumer, dependence))
  {
    return true;
  }

  return false;
}


static bool
hexagon_gpr_dot_newable_p(
  struct hexagon_insn_info *producer,
  struct hexagon_insn_info *consumer,
  struct hexagon_dependence *dependence
)
{
  rtx insn;
  rtx pattern;

  if (hexagon_can_be_new_value_jump_p( consumer, dependence))
  {
    return true;
  }

  if (!hexagon_can_be_new_value_store_p( producer, consumer, dependence))
  {
     return false;
  }
      
  /* Try wrapping all uses of the register in the consumer in a NEW_VALUE
     unspec. */
  pattern = copy_rtx(PATTERN (consumer->insn));
  pattern = replace_rtx(pattern,
                        dependence->use,
                        gen_rtx_UNSPEC (GET_MODE (dependence->use),
                                        gen_rtvec(1, dependence->use),
                                        UNSPEC_NEW_VALUE));

  start_sequence();
  if(JUMP_P (consumer->insn)){
    emit_jump_insn(pattern);
  }
  else if(CALL_P (consumer->insn)){
    emit_call_insn(pattern);
  }
  else {
    emit_insn(pattern);
  }
  insn = get_insns();
  end_sequence();

  /* If the resulting insn is valid, then the original insn is .new-able. */
  return !insn_invalid_p(insn);
}

  /* get compare portion of the nvj*/
  /* get compare - cmp.XX(Ns.new, YY) */
static rtx 
hexagon_nvj_get_compare(rtx nvj_insn, int elem_num)
{
  rtx pattern; 
  rtx condition;
  rtx compare;

  pattern = PATTERN(nvj_insn);

  /* get condition code - if(cmp.XX(Ns.new,YY)) */
  gcc_assert(PARALLEL==GET_CODE(pattern));
  condition = XVECEXP(pattern, 0, elem_num);

  if (GET_CODE(XEXP(condition,1)) == IF_THEN_ELSE) 
  {
    /* get compare - cmp.XX(Ns.new, YY) */
    compare  = XEXP(XEXP(condition, 1),0);
  }
  else 
  {
    compare  = XEXP(condition, 1);
  }

  return compare;
}

static rtx 
hexagon_nvj_get_operand( rtx insn, int op_count)
{
  return XEXP(insn, op_count-1);
}


/* first get the first element and see it's
   EQ, if yes, swap it and get the second element
   insn, and swap that as well */
static rtx
hexagon_nvj_swap_operands( rtx insn )
{
  rtx compare;
  rtx operand1;
  rtx operand2;

  /*first element insn of nvj insn set*/
  compare = hexagon_nvj_get_compare(insn,0);

  if (!(GET_CODE(compare) == EQ || 
        GET_CODE(compare) == NE ))
    return NULL;

  operand1 = hexagon_nvj_get_operand(compare, 1);
  operand2 = hexagon_nvj_get_operand(compare, 2);

  if ( GET_CODE(operand2) == UNSPEC &&  
       XINT(operand2,1) == UNSPEC_NEW_VALUE )
  {
    /*now swap the operands correctly*/
    XEXP(compare, 0)=operand2;
    XEXP(compare, 1)=operand1;
    /*first element of the nvj instruction is swapped*/

    /*now get the second pair, and swap them 
      as well. .new property of the first 
      and the second instruction will always 
      be the same*/
    compare = hexagon_nvj_get_compare(insn,1);
    operand1 = hexagon_nvj_get_operand(compare, 1);
    operand2 = hexagon_nvj_get_operand(compare, 2);

    XEXP(compare, 0)=operand2;
    XEXP(compare, 1)=operand1;
    /*second element of the nvj instruction is swapped*/
  }
  return insn;
}


static struct hexagon_insn_info *
hexagon_dot_newify_gpr(
  struct hexagon_insn_info *insn_info,
  struct hexagon_dependence *dependence
)
{
  struct hexagon_insn_info *new_insn_info;
  rtx insn;
  rtx pattern;

  pattern = copy_rtx(PATTERN (insn_info->insn));
  pattern = replace_rtx(pattern,
                        dependence->use,
                        gen_rtx_UNSPEC (GET_MODE (dependence->use),
                                        gen_rtvec(1, dependence->use),
                                        UNSPEC_NEW_VALUE));

  start_sequence();
  if(JUMP_P (insn_info->insn)){
    emit_jump_insn(pattern);
  }
  else if(CALL_P (insn_info->insn)){
    emit_call_insn(pattern);
  }
  else {
    emit_insn(pattern);
  }
  insn = get_insns();
  end_sequence();

  /* Make assembler happy and swap the operands */
  if (TARGET_NEW_VALUE_JUMP && 
      (INSN_CODE(insn_info->insn) == CODE_FOR_new_value_jump1   ||
       INSN_CODE(insn_info->insn) == CODE_FOR_new_value_jump2   ||
       INSN_CODE(insn_info->insn) == CODE_FOR_compare_and_jump1 || 
       INSN_CODE(insn_info->insn) == CODE_FOR_new_value_jump2)
     ) 
  {
    rtx original_insn = insn;
    if ((insn = hexagon_nvj_swap_operands(original_insn))==NULL);
      insn = original_insn;
  }

  new_insn_info = hexagon_get_insn_info(insn);
  new_insn_info->stack = insn_info;
  new_insn_info->flags |= HEXAGON_NEW_GPR;


  if (TARGET_NEW_VALUE_JUMP && 
      (INSN_CODE(insn_info->insn) == CODE_FOR_new_value_jump1   ||
       INSN_CODE(insn_info->insn) == CODE_FOR_new_value_jump2   ||
       INSN_CODE(insn_info->insn) == CODE_FOR_compare_and_jump1 || 
       INSN_CODE(insn_info->insn) == CODE_FOR_new_value_jump2   ||
       INSN_CODE(insn_info->insn) == CODE_FOR_new_value_jump_tstbit   ||
       INSN_CODE(insn_info->insn) == CODE_FOR_compare_and_jump_tstbit )) 
  {
    JUMP_LABEL(insn) = JUMP_LABEL(insn_info->insn);
  }

  if(HEXAGON_NEW_PREDICATE_P (insn_info)){
    new_insn_info->flags |= HEXAGON_NEW_PREDICATE;
  }
  if(HEXAGON_MOVED_P (insn_info)){
    new_insn_info->flags |= HEXAGON_MOVED;
  }
  set_block_for_insn(new_insn_info->insn, BLOCK_FOR_INSN (insn_info->insn));

  return new_insn_info;
}




static int
hexagon_find_new_value(rtx *x, void *y)
{
  rtx *new_value = (rtx *) y;
  if(GET_CODE (*x) == UNSPEC && XINT (*x, 1) == UNSPEC_NEW_VALUE){
    *new_value = *x;
    return -1;
  }
  return 0;
}




static void
hexagon_dot_oldify_gpr(struct hexagon_insn_info *insn_info)
{
  rtx insn;
  rtx pattern;
  rtx new_value;

  if (TARGET_NEW_VALUE_JUMP && 
      (INSN_CODE(insn_info->insn) == CODE_FOR_new_value_jump1 ||
       INSN_CODE(insn_info->insn) == CODE_FOR_new_value_jump2 ||
       INSN_CODE(insn_info->insn) == CODE_FOR_new_value_jump_tstbit )) {
    pattern = copy_rtx(PATTERN(insn_info->insn));

    /* new value jump patterns have two instructions */
    /* eg. if (cmp.XX(r0.new,#-1)) jump; p0 = cmp.XX(r0.new, #-1) */
    /* one is the actual new value jump - get the .new new operand from the first one*/
    for_each_rtx(&XVECEXP(pattern,0,0), hexagon_find_new_value, &new_value);
    XVECEXP(pattern,0,0) = replace_rtx(XVECEXP(pattern,0,0), new_value, XVECEXP (new_value, 0, 0));

    /* the other one is actually restricting the use of the predicate, in case we have to fall 
       out to the original jump (non new value jump) - get the .new new operand from the second one*/
    for_each_rtx(&XVECEXP(pattern,0,1), hexagon_find_new_value, &new_value);
    XVECEXP(pattern,0,1) = replace_rtx(XVECEXP(pattern,0,1), new_value, XVECEXP (new_value, 0, 0));

  } else 
  {
    pattern = copy_rtx(PATTERN (insn_info->insn));
    for_each_rtx(&pattern, hexagon_find_new_value, &new_value);
    pattern = replace_rtx(pattern, new_value, XVECEXP (new_value, 0, 0));
  }


  if(JUMP_P (insn_info->insn)){
    insn = emit_jump_insn_after(pattern, insn_info->insn);
    if (INSN_CODE(insn_info->insn) == CODE_FOR_new_value_jump1 ||
        INSN_CODE(insn_info->insn) == CODE_FOR_new_value_jump2 ||
        INSN_CODE(insn_info->insn) == CODE_FOR_new_value_jump_tstbit )
    {
      JUMP_LABEL(insn) = JUMP_LABEL(insn_info->insn);
    }
  }
  else if(CALL_P (insn_info->insn)){
    insn = emit_call_insn_after(pattern, insn_info->insn);
  }
  else {
    insn = emit_insn_after(pattern, insn_info->insn);
  }
  set_block_for_insn(insn, BLOCK_FOR_INSN (insn_info->insn));
  delete_insn(insn_info->insn);
}




static bool
hexagon_predicate_dot_newable_p(struct hexagon_insn_info *insn_info)
{
  rtx pattern;
  rtx address;

  if(!TARGET_NEW_PREDICATES){
    return false;
  }

  /* Insns must already be conditional on a predicate condition to be
     new-predicable. */
  if(!HEXAGON_CONDITIONAL_P (insn_info) || HEXAGON_GPR_CONDITION_P (insn_info)){
    return false;
  }

  /* Before V4, the only control insns that could be .new predicated were direct
     jumps. In V4, all control instructions can be .new predicated except calls
     and register-condition jumps. */
  if(HEXAGON_CONTROL_P (insn_info)
     && (HEXAGON_CALL_P (insn_info)
         || (!TARGET_V4_FEATURES && !HEXAGON_DIRECT_JUMP_P (insn_info)))){
    return false;
  }

  /* In V4, all non-control predicable instructions are .new predicable. */
  if(TARGET_V4_FEATURES){
    return true;
  }

  pattern = PATTERN (insn_info->insn);
  if(GET_CODE (pattern) == COND_EXEC){
    pattern = COND_EXEC_CODE (pattern);
    if(GET_CODE (pattern) == SET){
      /* Stores are not .newable. */
      if(MEM_P (SET_DEST (pattern))){
        return false;
      }
      /* loads */
      if(MEM_P (SET_SRC (pattern))){
        address = XEXP (SET_SRC (pattern), 0);
        /* Only base + offset loads are .newable. */
        if(G_REG_P (address) || GET_CODE (address) == PLUS){
          return true;
        }
        return false;
      }
    }
  }

  return true;
}




static struct hexagon_insn_info *
hexagon_dot_newify_predicate(struct hexagon_insn_info *insn_info)
{
  struct hexagon_insn_info *new_insn_info;
  new_insn_info = (struct hexagon_insn_info *)ggc_alloc(sizeof(struct hexagon_insn_info));
  memcpy(new_insn_info, insn_info, sizeof(struct hexagon_insn_info));
  new_insn_info->stack = insn_info;
  new_insn_info->flags |= HEXAGON_NEW_PREDICATE;
  return new_insn_info;
}




/* Return true if INSN_INFO appears to be part of the prologue. */

static bool
hexagon_prologue_insn_p(struct hexagon_insn_info *insn_info)
{
  struct hexagon_reg_access *write;
  struct hexagon_reg_access *read;
  struct hexagon_mem_access *store;
  rtx address;
  rtx reg;

  /* Assume any instruction that adjusts the frame pointer or stack pointer is
     part of the prologue. */
  for(write = insn_info->reg_writes; write; write = write->next){
    if(write->regno == HARD_FRAME_POINTER_REGNUM
       || write->regno == STACK_POINTER_REGNUM){
      return true;
    }
  }

  /* Assume any instruction that reads a callee-save register and stores to
     memory using FP or SP as a base is part of the prologue. */
  for(read = insn_info->reg_reads; read; read = read->next){
    if(!(call_used_regs[read->regno] || read->regno == LINK_REGNUM)){
      for(store = insn_info->stores; store; store = store->next){
        address = XEXP (store->mem, 0);
        reg = GET_CODE (address) == PLUS ? XEXP (address, 0) : address;
        if(REG_P (reg) && (REGNO (reg) == HARD_FRAME_POINTER_REGNUM
                           || REGNO (reg) == STACK_POINTER_REGNUM)){
          return true;
        }
      }
      break;
    }
  }

  return false;
}




static struct hexagon_dependence *
hexagon_add_dependence(
  struct hexagon_dependence *dependencies,
  enum hexagon_dependence_type type,
  rtx set,
  rtx use
)
{
  struct hexagon_dependence *new_dependence;
  new_dependence = (struct hexagon_dependence *)ggc_alloc(sizeof(struct hexagon_dependence));
  new_dependence->type = type;
  new_dependence->set = set;
  new_dependence->use = use;
  new_dependence->next = dependencies;
  return new_dependence;
}




static struct hexagon_dependence *
hexagon_remove_dependence(
  struct hexagon_dependence *dependencies,
  struct hexagon_dependence *dependence
)
{
  struct hexagon_dependence *dep;

  gcc_assert(dependence);

  if(dependencies == dependence){
    return dependencies->next;
  }

  for(dep = dependencies; dep->next != dependence; dep = dep->next){
    /* The dependence to be removed must be in the list. */
    gcc_assert(dep->next);
  }
  dep->next = dep->next->next;

  return dependencies;
}




static struct hexagon_dependence *
hexagon_concat_dependencies(
  struct hexagon_dependence *a,
  struct hexagon_dependence *b
)
{
  struct hexagon_dependence *c;
  if(!a){
    return b;
  }
  for(c = a; c->next; c = c->next);
  c->next = b;
  return a;
}




static struct hexagon_dependence *
hexagon_control_dependencies(
  struct hexagon_insn_info *first,
  struct hexagon_insn_info *second
)
{
  struct hexagon_dependence *dependencies = NULL;

  if(HEXAGON_CONTROL_P (first)){
    /* Allow dual jumps by not adding a control dependence between two jumps
       that are allowed to be in the same packet. */
    if(!((TARGET_V3_FEATURES
          /* The first jump must be conditional. */
          && HEXAGON_CONDITIONAL_P (first)
          /* Indirect jumps are not allowed to be dual jumps. */
          && HEXAGON_DIRECT_JUMP_P (first) && HEXAGON_DIRECT_JUMP_P (second)
          /* In V3, dot-new jumps are not allowed to be dual jumps. */
          && !HEXAGON_NEW_PREDICATE_P (second) && !HEXAGON_NEW_PREDICATE_P (first)
          /* Register-condition jumps are not allowed to be dual jumps. */
          && !HEXAGON_GPR_CONDITION_P (second) && !HEXAGON_GPR_CONDITION_P (first))
         || (TARGET_V4_FEATURES
             /* The first jump must be conditional. */
             && HEXAGON_CONDITIONAL_P (first)
             /* Indirect jumps are not allowed to be dual jumps. */
             && (HEXAGON_DIRECT_JUMP_P (first) || HEXAGON_DIRECT_CALL_P (first))
             && (HEXAGON_DIRECT_JUMP_P (second) || HEXAGON_DIRECT_CALL_P (second))
             /* Register-condition jumps are not allowed to be dual jumps. */
             && !HEXAGON_GPR_CONDITION_P (first)
             && !HEXAGON_GPR_CONDITION_P (second)))){
      dependencies = hexagon_add_dependence(dependencies,
                                          HEXAGON_DEP_CONTROL,
                                          first->insn,
                                          second->insn);
    }
  }

  /* Both insns are actually calls. */
  if(HEXAGON_EMULATION_CALL_P (first) && HEXAGON_EMULATION_CALL_P (second)){
    dependencies = hexagon_add_dependence(dependencies,
                                        HEXAGON_DEP_CONTROL,
                                        first->insn,
                                        second->insn);
  }

  /* When generating exception handling information, do not put a call in the
     same packet as a prologue insn. */
  if(flag_exceptions && HEXAGON_CALL_P (second) && hexagon_prologue_insn_p(first)){
    dependencies = hexagon_add_dependence(dependencies,
                                        HEXAGON_DEP_CONTROL,
                                        first->insn,
                                        second->insn);
  }

  return dependencies;
}




static struct hexagon_dependence *
hexagon_true_dependencies(
  struct hexagon_insn_info *writer,
  struct hexagon_insn_info *reader
)
{
  struct hexagon_dependence *dependencies;
  struct hexagon_mem_access *store;
  struct hexagon_mem_access *load;
  struct hexagon_reg_access *write;
  struct hexagon_reg_access *read;

  dependencies = NULL;

  if(HEXAGON_EMULATION_CALL_P (writer)){
    /* For an emulation call followed by another insn, consider anti
       dependencies to be true dependencies since emulation calls do not read
       their inputs until after all results in the current packet have been
       written. */
    dependencies = hexagon_concat_dependencies(dependencies,
                                             hexagon_anti_dependencies(writer,
                                                                     reader));
  }
  else if(HEXAGON_EMULATION_CALL_P (reader)){
    /* For an emulation call following another insn, ignore true dependencies
       since emulation calls do not read their inputs until after all results in
       the current packet have been written. */
    return dependencies;
  }

  if (!TARGET_V4_FEATURES || !TARGET_PACKETIZE_VOLATILES){
    /* If a memory access is volatile, then it should be the only memory access in
       a packet.  (not really a dependency, but oh well) */
    if((HEXAGON_VOLATILE_P (writer) || HEXAGON_VOLATILE_P (reader))
       && (HEXAGON_MEM_P (writer) && HEXAGON_MEM_P (reader))){
      dependencies = hexagon_add_dependence(dependencies,
                                          HEXAGON_DEP_VOLATILE,
                                          writer->insn,
                                          reader->insn);
    }
  }

  /* Check for possible true memory dependencies. */
  for(store = writer->stores; store; store = store->next){
    for(load = reader->loads; load; load = load->next){
      if((HEXAGON_CONFLICT_P (store, load)
          || (HEXAGON_NEW_PREDICATE_P (reader)
              && !HEXAGON_NEW_PREDICATE_P (writer)))
         && true_dependence(store->mem, VOIDmode, load->mem, rtx_varies_p)){
        dependencies = hexagon_add_dependence(dependencies,
                                            HEXAGON_DEP_MEMORY,
                                            store->mem,
                                            load->mem);
      }
    }
  }

  /* Check for true register dependencies. */
  for(write = writer->reg_writes; write; write = write->next){
    for(read = reader->reg_reads; read; read = read->next){
      if((HEXAGON_CONFLICT_P (write, read)
          || (HEXAGON_NEW_PREDICATE_P (reader)
              && !HEXAGON_NEW_PREDICATE_P (writer)))
         && write->regno == read->regno){
        dependencies = hexagon_add_dependence(dependencies,
                                            HEXAGON_DEP_REGISTER,
                                            write->reg,
                                            read->reg);
      }
    }
  }

  return dependencies;
}




static struct hexagon_dependence *
hexagon_output_dependencies(
  struct hexagon_insn_info *insn0,
  struct hexagon_insn_info *insn1
)
{
  struct hexagon_dependence *dependencies = NULL;
  struct hexagon_reg_access *write0;
  struct hexagon_reg_access *write1;

  if(HEXAGON_EMULATION_CALL_P (insn1)){
    /* For an emulation call following another insn, ignore output dependencies
       since emulation calls do not write their outputs until after all results
       in the current packet have been written.  The exception is LR, since it
       is written by the call insn itself. */
    for(write0 = insn0->reg_writes; write0; write0 = write0->next){
      if(write0->regno == LINK_REGNUM){
        write1 = insn1->reg_writes;
        while(write1 && write1->regno != LINK_REGNUM){
          write1 = write1->next;
        }
        gcc_assert(write1);
        dependencies = hexagon_add_dependence(dependencies,
                                            HEXAGON_DEP_REGISTER,
                                            write0->reg,
                                            write1->reg);
      }
    }
    return dependencies;
  }

  /* Check for register output dependencies. */
  for(write0 = insn0->reg_writes; write0; write0 = write0->next){
    for(write1 = insn1->reg_writes; write1; write1 = write1->next){
      if((HEXAGON_CONFLICT_P (write0, write1)
          || (HEXAGON_NEW_PREDICATE_P (insn1)
              && !HEXAGON_NEW_PREDICATE_P (insn0)))
         && write0->regno == write1->regno){
        dependencies = hexagon_add_dependence(dependencies,
                                            HEXAGON_DEP_REGISTER,
                                            write0->reg,
                                            write1->reg);
      }
    }
  }

  return dependencies;
}




static struct hexagon_dependence *
hexagon_anti_dependencies(
  struct hexagon_insn_info *earlier,
  struct hexagon_insn_info *later
)
{
  struct hexagon_dependence *dependencies = NULL;
  struct hexagon_mem_access *mem;
  struct hexagon_mem_access *store;
  struct hexagon_reg_access *read;
  struct hexagon_reg_access *write;

  /* Don't allow insns to move across control insns and vice versa. */
  if(HEXAGON_CONTROL_P (earlier) ^ HEXAGON_CONTROL_P (later)){
    dependencies = hexagon_add_dependence(dependencies,
                                        HEXAGON_DEP_CONTROL,
                                        earlier->insn,
                                        later->insn);
  }

  /* Check for possible memory anti dependencies. */
  for(store = later->stores; store; store = store->next){
    /* load followed by a store */
    for(mem = earlier->loads; mem; mem = mem->next){
      if(HEXAGON_CONFLICT_P (mem, store)
         && anti_dependence(mem->mem, store->mem)){
        dependencies = hexagon_add_dependence(dependencies,
                                            HEXAGON_DEP_MEMORY,
                                            mem->mem,
                                            store->mem);
      }
    }
    /* store followed by a store */
    for(mem = earlier->stores; mem; mem = mem->next){
      if(HEXAGON_CONFLICT_P (mem, store)
         && output_dependence(mem->mem, store->mem)){
        dependencies = hexagon_add_dependence(dependencies,
                                            HEXAGON_DEP_MEMORY,
                                            mem->mem,
                                            store->mem);
      }
    }
  }

  /* Check for register anti dependencies. */
  for(read = earlier->reg_reads; read; read = read->next){
    for(write = later->reg_writes; write; write = write->next){
      if(HEXAGON_CONFLICT_P (read, write) && read->regno == write->regno){
        dependencies = hexagon_add_dependence(dependencies,
                                            HEXAGON_DEP_REGISTER,
                                            read->reg,
                                            write->reg);
      }
    }
  }

  return dependencies;
}




static bool
hexagon_packet_insn_dependence_p(
  struct hexagon_packet_info *packet,
  struct hexagon_insn_info **insn_info,
  bool ignore_jumps
)
{
  struct hexagon_insn_info *original_insn_info = *insn_info;
  struct hexagon_dependence *dependencies;
  struct hexagon_dependence *dep;
  int i;

  /* Check each insn in the packet in reverse order for dependencies. */
  for(i = packet->num_insns - 1; i >= 0; i--){

    /* We don't have any way to eliminate output dependencies. */
    if(hexagon_output_dependencies(packet->insns[i], *insn_info)){
      *insn_info = original_insn_info;
      return true;
    }

    /* Disallow anti-dependencies with jumps since INSN_INFO would be inserted
       before any jumps if it were added to the packet. */
    if(HEXAGON_JUMP_P (packet->insns[i])){
      dependencies = hexagon_anti_dependencies(packet->insns[i], *insn_info);
      /* If IGNORE_JUMPS is true, ignore control dependencies from jumps. */
      if(ignore_jumps){
        for(dep = dependencies; dep; dep = dep->next){
          if(dep->type == HEXAGON_DEP_CONTROL){
            dependencies = hexagon_remove_dependence(dependencies, dep);
          }
        }
      }
      if(dependencies){
        return true;
      }
    }

    dependencies = hexagon_true_dependencies(packet->insns[i], *insn_info);

    /* If IGNORE_JUMPS is true, ignore control dependencies from jumps. */
    if(! (ignore_jumps && HEXAGON_JUMP_P (packet->insns[i]))){
    dependencies = 
      hexagon_concat_dependencies(dependencies,
                                hexagon_control_dependencies(packet->insns[i],
                                                           *insn_info));
    }

    for(dep = dependencies; dep; dep = dep->next){

      if(dep->type == HEXAGON_DEP_REGISTER
         && P_REG_P (dep->use)
         && hexagon_predicate_dot_newable_p(*insn_info)){

        if(!HEXAGON_NEW_PREDICATE_P (*insn_info)){
          *insn_info = hexagon_dot_newify_predicate(*insn_info);
          (*insn_info)->transformed_at_packet = packet;
        }
        dependencies = hexagon_remove_dependence(dependencies, dep);
      }

      /* See if the consumer insn can use the newly generated value in the same
         packet. */
      if(dep->type == HEXAGON_DEP_REGISTER
         && G_REG_P (dep->use)
         && hexagon_gpr_dot_newable_p(packet->insns[i], *insn_info, dep)){

        if(!HEXAGON_NEW_GPR_P (*insn_info)){
          *insn_info = hexagon_dot_newify_gpr(*insn_info, dep);
          (*insn_info)->transformed_at_packet = packet;
        }
        dependencies = hexagon_remove_dependence(dependencies, dep);
      }

    }

    /* We have encountered a dependence that we are unable to eliminate. */
    if(dependencies){
      *insn_info = original_insn_info;
      return true;
    }
  }

  /* Transforming the insn might have introduced a control dependence. */
  if(*insn_info != original_insn_info && !ignore_jumps){
    for(i = packet->num_insns - 1; i >= 0; i--){
      if(hexagon_control_dependencies(packet->insns[i], *insn_info)){
        *insn_info = original_insn_info;
        return true;
      }
    }
  }

  return false;
}




static bool
hexagon_packet_insn_internal_dependence_p(
  struct hexagon_packet_info *packet,
  struct hexagon_insn_info *insn_info
)
{
  struct hexagon_dependence *anti_dependencies;
  struct hexagon_dependence *true_dependencies, *control_dependencies;
  struct hexagon_dependence *dependencies;
  int num_insns;
  int i;

  /* If INSN_INFO is in PACKET, then only check for dependencies on insns before
     it. */
  for(num_insns = 0; num_insns < packet->num_insns; num_insns++){
    if(insn_info == packet->insns[num_insns]){
      break;
    }
  }

  for(i = num_insns - 1; i >= 0; i--){

    anti_dependencies = hexagon_anti_dependencies(packet->insns[i], insn_info);

    /* We can have truly dependent insns in the same packet becasue of .new. */
    true_dependencies = hexagon_true_dependencies(packet->insns[i], insn_info);
    control_dependencies = hexagon_control_dependencies(packet->insns[i],
                                                           insn_info);

    dependencies = hexagon_concat_dependencies(anti_dependencies,
                                             true_dependencies);

    /* Ignore control dependencies from jumps. */
    if(! HEXAGON_JUMP_P (packet->insns[i])){
      dependencies = hexagon_concat_dependencies(dependencies,
                                               control_dependencies);
    }

    if(dependencies){
      return true;
    }
  }

  return false;
}




static bool
hexagon_insn_fits_in_packet_p(
  struct hexagon_insn_info *insn,
  struct hexagon_packet_info *packet
)
{
  state_t pipeline_state;
  int i;

  pipeline_state = alloca(state_size());
  state_reset(pipeline_state);
  for(i = 0; i < packet->num_insns; i++){
    gcc_assert(state_transition(pipeline_state, packet->insns[i]->insn) < 0);
  }

  return state_transition(pipeline_state, insn->insn) < 0;
}




static bool
hexagon_can_add_insn_to_packet_p(
  struct hexagon_insn_info **insn,
  struct hexagon_packet_info *packet
)
{
  struct hexagon_insn_info *original_insn = *insn;

  
  if(hexagon_packet_insn_dependence_p(packet, insn, false)){
    gcc_assert(*insn == original_insn);
    return false;
  }
  if(!hexagon_insn_fits_in_packet_p(*insn, packet)){
    *insn = original_insn;
    return false;
  }
  return true;
}




static rtx
hexagon_bb_real_head_insn(basic_block bb)
{
  rtx insn;
  for(insn = BB_HEAD (bb);
      insn && (!INSN_P (insn)
               || GET_CODE (PATTERN (insn)) == USE
               || GET_CODE (PATTERN (insn)) == CLOBBER
               || GET_CODE (PATTERN (insn)) == ADDR_VEC
               || GET_CODE (PATTERN (insn)) == ADDR_DIFF_VEC);
      insn = NEXT_INSN (insn));
  if(!insn || BLOCK_FOR_INSN (insn) != bb){
    return NULL_RTX;
  }
  return insn;
}




static rtx
hexagon_bb_real_end_insn(basic_block bb)
{
  rtx insn;
  for(insn = BB_END (bb);
      insn && (!INSN_P (insn)
               || GET_CODE (PATTERN (insn)) == USE
               || GET_CODE (PATTERN (insn)) == CLOBBER
               || GET_CODE (PATTERN (insn)) == ADDR_VEC
               || GET_CODE (PATTERN (insn)) == ADDR_DIFF_VEC);
      insn = PREV_INSN (insn));
  if(!insn || BLOCK_FOR_INSN (insn) != bb){
    return NULL_RTX;
  }
  return insn;
}

static void
hexagon_create_bb_sentinel_packet(struct hexagon_packet_info *packet)
{
  struct hexagon_packet_info *sentinel_packet;
  struct hexagon_insn_info *sentinel_insn;

  sentinel_packet = (struct hexagon_packet_info *)
    ggc_alloc_cleared(sizeof(struct hexagon_packet_info));
  sentinel_insn = (struct hexagon_insn_info *)
    ggc_alloc_cleared(sizeof(struct hexagon_insn_info));

  sentinel_insn->insn = PREV_INSN (packet->insns[0]->insn);
  sentinel_packet->insns[0] = sentinel_insn;
  sentinel_packet->num_insns = 1;
  sentinel_packet->prev = packet->prev;
  sentinel_packet->next = packet;

  if(packet->prev){
    packet->prev->next = sentinel_packet;
  }
  else {
    hexagon_head_packet = sentinel_packet;
  }
  packet->prev = sentinel_packet;
}



static void
hexagon_finalize_transformations(
  struct hexagon_packet_info *first,
  struct hexagon_packet_info *last
)
{
  struct hexagon_packet_info *packet;
  struct hexagon_insn_info *new_insn_info;
  struct hexagon_insn_info *old_insn_info;
  rtx prev_insn;
  rtx insn;
  int i;

  for(packet = first; packet && packet->prev != last; packet = packet->next){
    prev_insn = packet->location;
    for(i = 0; i < packet->num_insns; i++){
      new_insn_info = packet->insns[i];

      while(new_insn_info->stack
            && new_insn_info->insn == new_insn_info->stack->insn){
        new_insn_info->stack = new_insn_info->stack->stack;
      }

      if(HEXAGON_MOVED_P (new_insn_info) || new_insn_info->stack){
        old_insn_info = new_insn_info;

        while(old_insn_info->stack){
          old_insn_info = old_insn_info->stack;
        }

        insn = new_insn_info->insn;
        if(JUMP_P (insn)){
          insn = emit_jump_insn_after(insn, prev_insn);
        }
        else if(CALL_P (insn)){
          insn = emit_call_insn_after(insn, prev_insn);
        }
        else {
          insn = emit_insn_after(insn, prev_insn);
        }
        new_insn_info->insn = insn;

        delete_insn(old_insn_info->insn);
      }

      new_insn_info->stack = NULL;
      new_insn_info->transformed_at_packet = NULL;

      prev_insn = new_insn_info->insn;
    }
  }
}




static void
hexagon_pack_insns(bool need_bb_info)
{
  basic_block bb = NULL;
  struct hexagon_packet_info *packet = NULL;
  struct hexagon_insn_info *insn_info;
  rtx insn;
  rtx bb_head_insn = NULL_RTX;
  rtx bb_end_insn  = NULL_RTX;
  bool start_packet = true;
  bool start_bb = false;
  bool end_bb = false;

  if(need_bb_info){
    bb = ENTRY_BLOCK_PTR->next_bb;
    do{
      if(bb){
        bb_head_insn = hexagon_bb_real_head_insn(bb);
        bb_end_insn = hexagon_bb_real_end_insn(bb);
        if(!(bb_head_insn && bb_end_insn)){
          bb = bb->next_bb;
        }
      }
    }while(bb && !(bb_head_insn && bb_end_insn));
    gcc_assert(bb_head_insn && bb_end_insn);
  }

  for(insn = get_insns(); insn; insn = NEXT_INSN (insn)){

    /* Ignore notes. */
    if(NOTE_P (insn)){
      continue;
    }

    /* Don't bundle insns across other non-insns, like labels. */
    if(!INSN_P (insn)){
      start_packet = true;
      continue;
    }

    /* Ignore insns that don't do anything. */
    switch(GET_CODE (PATTERN (insn))){
      case USE:
      case CLOBBER:
      case ADDR_VEC:
      case ADDR_DIFF_VEC:
        continue;
      default:
        break;
    }

    if(need_bb_info){
      if(bb_head_insn == insn){
        start_bb = true;
        start_packet = true;
      }
      if(bb_end_insn == insn){
        end_bb = true;
      }
    }

    insn_info = hexagon_get_insn_info(insn);

    if(start_packet || !hexagon_can_add_insn_to_packet_p(&insn_info, packet)){
      packet = hexagon_start_new_packet();
    }

    hexagon_add_insn_to_packet(packet, insn_info, false);

    start_packet = false;

    if(need_bb_info){
      if(start_bb){
        BB_HEAD_PACKET (bb) = packet;
        hexagon_create_bb_sentinel_packet(packet);
      }
      if(end_bb){
        BB_END_PACKET (bb) = packet;
        do {
          bb = bb->next_bb;
          if(!bb){
            bb_head_insn = NULL_RTX;
            bb_end_insn = NULL_RTX;
            break;
          }
          bb_head_insn = hexagon_bb_real_head_insn(bb);
          bb_end_insn = hexagon_bb_real_end_insn(bb);
        }while(!(bb_head_insn && bb_end_insn));
      }
      start_bb = false;
      end_bb = false;
    }

  }

  hexagon_finalize_transformations(hexagon_head_packet, hexagon_tail_packet);
}




static int
check_call_reorder_feasibility(struct hexagon_insn_info *insn_info){

  struct hexagon_reg_access *write;
  struct hexagon_reg_access *read;
  char call_used_regs[] = CALL_USED_REGISTERS;

  gcc_assert(insn_info);
  /* If this is a call, I should assume it to alias with any memory access,
              but I might try to reason about calee-save registers */
  if(HEXAGON_MEM_P (insn_info)) return true;
    for(write = insn_info->reg_writes; write; write = write->next){
      if(call_used_regs[write->regno] || (write->regno == LINK_REGNUM))
        return true;
    }
    for(read = insn_info->reg_reads; read; read = read->next){
      if(call_used_regs[read->regno] || (read->regno == LINK_REGNUM))
        return true;
    }
  return false;
}




/* This function is  used by tail merging
   Looks at the relationship of two instructions
   and tries to establish their independenc.
   Conservative.
   Shaped after hexagon_true_dependencies(from,to); */

int
hexagon_instructions_dependent (rtx from,rtx to){
 struct hexagon_insn_info *insn_info_from = NULL;
 struct hexagon_insn_info *insn_info_to   = NULL;
 struct hexagon_mem_access *store;
 struct hexagon_mem_access *load;
 struct hexagon_reg_access *write;
 struct hexagon_reg_access *read;


  /* I know it is INSN_P for both cases, and it should not be a jump,
          since we are not at the "bottom" of BB, but I will double check
          for generality */
  if(!INSN_P(from) ||
    (GET_CODE (PATTERN (from)) == USE) ||
    (GET_CODE (PATTERN (from)) == CLOBBER))
      return true;
  if(!INSN_P(to) ||
    (GET_CODE (PATTERN (to)) == USE) ||
    (GET_CODE (PATTERN (to)) == CLOBBER))
      return true;

  insn_info_from = hexagon_get_insn_info(from);
  insn_info_to   = hexagon_get_insn_info(to);

  if(HEXAGON_JUMP_P(insn_info_from) || HEXAGON_JUMP_P(insn_info_to))
    /* I really should not have jumps here... */
    return true;

  if(HEXAGON_EMULATION_CALL_P (insn_info_from) ||
     HEXAGON_EMULATION_CALL_P (insn_info_to))
    /* not handling these yet */
    return true;

  /* If this is a call, I should assume it to alias with any memory access,
               but I might try to reason about calee-save registers */
  if(HEXAGON_CALL_P (insn_info_from))
    return check_call_reorder_feasibility(insn_info_to);

  /* If this is a call, I should assume it to alias with any memory access,
               but I might try to reason about calee-save registers */
  if(HEXAGON_CALL_P(insn_info_to))
    return check_call_reorder_feasibility(insn_info_from);

  /* this will cover the case of memory output dependency   */
  if((HEXAGON_VOLATILE_P (insn_info_from) || HEXAGON_VOLATILE_P (insn_info_to))
  && (HEXAGON_MEM_P (insn_info_from) && HEXAGON_MEM_P (insn_info_to)))
    return true;

  /* Check for possible true memory dependencies. */
  for(store = insn_info_from->stores; (store && store->mem); store = store->next){
    for(load = insn_info_to->loads; (load && load->mem); load = load->next){
      if(true_dependence(store->mem, VOIDmode, load->mem, rtx_varies_p))
        return true;
    }
  }

  /* Check for possible anti memory dependencies. */
  for(store = insn_info_to->stores; (store && store->mem); store = store->next){
    for(load = insn_info_from->loads; (load && load->mem); load = load->next){
      if(true_dependence(store->mem, VOIDmode, load->mem, rtx_varies_p))
        return true;
    }
  }

  /* Check for true register dependencies. */
  for(write = insn_info_from->reg_writes; write; write = write->next){
    for(read = insn_info_to->reg_reads; read; read = read->next){
      if(write->regno == read->regno)
        return true;
    }
  }
  /* Check for anti register dependencies. */
  for(write = insn_info_to->reg_writes; write; write = write->next){
    for(read = insn_info_from->reg_reads; read; read = read->next){
      if(write->regno == read->regno)
        return true;
    }
  }
  /* We do not need to check for output dependency since this is a check inside BB, and DCE has been recently
     performed */

  return false;
}




static void
hexagon_move_insn(
  struct hexagon_insn_info *old_insn,
  struct hexagon_packet_info *from_packet,
  struct hexagon_insn_info *new_insn,
  struct hexagon_packet_info *to_packet,
  bool move_to_beginning
)
{
  basic_block bb;
  rtx adjacent_insn;

  gcc_assert(to_packet != from_packet);

  hexagon_remove_insn_from_packet(from_packet, old_insn);
  hexagon_add_insn_to_packet(to_packet, new_insn, move_to_beginning);

  if(old_insn->insn == new_insn->insn){
    if(PREV_INSN (old_insn->insn)){
      NEXT_INSN (PREV_INSN (old_insn->insn)) = NEXT_INSN (old_insn->insn);
    }
    if(NEXT_INSN (old_insn->insn)){
      PREV_INSN (NEXT_INSN (old_insn->insn)) = PREV_INSN (old_insn->insn);
    }
    bb = BLOCK_FOR_INSN (old_insn->insn);
    if(bb && BB_END (bb) == old_insn->insn){
      BB_END (bb) = PREV_INSN (old_insn->insn);
    }
  }
  else {
    delete_insn(old_insn->insn);
  }


  if(to_packet->num_insns > 1){
    if (move_to_beginning){
      adjacent_insn = to_packet->insns[1]->insn;
      if(PREV_INSN (adjacent_insn) != new_insn->insn){
        PREV_INSN(new_insn->insn) = PREV_INSN (adjacent_insn);
        NEXT_INSN (PREV_INSN (adjacent_insn)) = new_insn->insn;
        NEXT_INSN(new_insn->insn) = adjacent_insn;
        PREV_INSN (adjacent_insn) = new_insn->insn;
      }        
    }
    else if(to_packet->insns[to_packet->num_insns - 1] == new_insn){
      adjacent_insn = to_packet->insns[to_packet->num_insns - 2]->insn;
      if(NEXT_INSN (adjacent_insn) != new_insn->insn){
        PREV_INSN (new_insn->insn) = adjacent_insn;
        NEXT_INSN (new_insn->insn) = NEXT_INSN (adjacent_insn);
        NEXT_INSN (adjacent_insn) = new_insn->insn;
        PREV_INSN (NEXT_INSN (new_insn->insn)) = new_insn->insn;
        bb = BLOCK_FOR_INSN(adjacent_insn);
        if(bb && BB_END (bb) == adjacent_insn){
          BB_END (bb) = new_insn->insn;
        }
      }
    }
    else {
      gcc_assert(to_packet->insns[to_packet->num_insns - 2] == new_insn);
      adjacent_insn = to_packet->insns[to_packet->num_insns - 1]->insn;
      NEXT_INSN (new_insn->insn) = adjacent_insn;
      PREV_INSN (new_insn->insn) = PREV_INSN (adjacent_insn);
      PREV_INSN (adjacent_insn) = new_insn->insn;
      NEXT_INSN (PREV_INSN (new_insn->insn)) = new_insn->insn;
    }
  }
  else {
    gcc_assert(to_packet->num_insns == 1);
    do {
      to_packet = to_packet->prev;
    }while(to_packet->num_insns == 0);
    adjacent_insn = to_packet->insns[to_packet->num_insns - 1]->insn;
    if(NEXT_INSN (adjacent_insn) != new_insn->insn){
      PREV_INSN (new_insn->insn) = adjacent_insn;
      NEXT_INSN (new_insn->insn) = NEXT_INSN (adjacent_insn);
      NEXT_INSN (adjacent_insn) = new_insn->insn;
      PREV_INSN (NEXT_INSN (new_insn->insn)) = new_insn->insn;
      bb = BLOCK_FOR_INSN(adjacent_insn);
      if(bb && BB_END (bb) == adjacent_insn){
        BB_END (bb) = new_insn->insn;
      }
    }
  }

 /*
  df_insn_rescan_all();
  set_block_for_insn(new_insn->insn, BLOCK_FOR_INSN (adjacent_insn));
*/ 
  df_insn_change_bb (new_insn->insn, BLOCK_FOR_INSN (adjacent_insn)); /* Support for data flow analysis */
}




static void
hexagon_sanity_check_cfg_packet_info(void)
{
  basic_block bb;
  struct hexagon_packet_info *packet;
  struct hexagon_insn_info *insn;
  int i;

  FOR_EACH_BB (bb){
    packet = BB_HEAD_PACKET (bb);
    while(packet && packet->prev != BB_END_PACKET (bb)){
      for(i = 0; i < packet->num_insns; i++){
        insn = packet->insns[i];
        gcc_assert(insn && insn->insn && BLOCK_FOR_INSN (insn->insn) == bb);
      }
      if(!packet->next){
        gcc_assert(packet == BB_END_PACKET (bb));
      }
      packet = packet->next;
    }
  }

  for(packet = hexagon_head_packet; packet; packet = packet->next){
    gcc_assert(packet->num_insns > 0
               && packet->insns[0]
               && packet->insns[0]->insn);
    bb = BLOCK_FOR_INSN (packet->insns[0]->insn);
    gcc_assert(BB_HEAD_PACKET (bb) && BB_END_PACKET (bb));
    for(i = 0; i < packet->num_insns; i++){
      gcc_assert(packet->insns[i]
                 && packet->insns[i]->insn
                 && BLOCK_FOR_INSN (packet->insns[i]->insn) == bb);
    }
    if(!packet->insns[0]->flags){
      if(packet->prev){
        gcc_assert(packet->prev->num_insns
                   && packet->prev->insns[0]
                   && packet->prev->insns[0]->insn
                   && BLOCK_FOR_INSN (packet->prev->insns[0]->insn)
                   && packet->prev == BB_END_PACKET (BLOCK_FOR_INSN (packet->prev->insns[0]->insn)));
      }
      gcc_assert(packet->next && packet->next == BB_HEAD_PACKET (bb));
    }
    if(packet == BB_HEAD_PACKET (bb)){
      gcc_assert(packet->prev
                 && packet->prev->num_insns == 1
                 && !packet->prev->insns[0]->reg_reads
                 && !packet->prev->insns[0]->reg_writes
                 && !packet->prev->insns[0]->loads
                 && !packet->prev->insns[0]->stores
                 && !packet->prev->insns[0]->flags);
    }
    if(packet== BB_END_PACKET (bb)){
      if(packet->next){
        gcc_assert(packet->next->num_insns == 1
                   && !packet->next->insns[0]->reg_reads
                   && !packet->next->insns[0]->reg_writes
                   && !packet->next->insns[0]->loads
                   && !packet->next->insns[0]->stores
                   && !packet->next->insns[0]->flags);
      }
    }
    if(!packet->next){
      gcc_assert(packet == BB_END_PACKET (bb) && packet == hexagon_tail_packet);
    }
  }
}




#define SORTED_EDGE_LIST_SIZE 1024

static void
hexagon_pull_up_insns(void)
{
  basic_block bb;
  basic_block successor_bb;
  edge e;
  edge_iterator ei;
  HARD_REG_SET prev_live_out;
  struct hexagon_packet_info *top_packet;
  struct hexagon_packet_info *forward_edge_packet;
  struct hexagon_packet_info *back_edge_packet;
  struct hexagon_packet_info *last_packet;
  struct hexagon_packet_info *packet;
  struct hexagon_packet_info *target_packet;
  struct hexagon_insn_info *insn;
  struct hexagon_insn_info *original_insn;
  struct hexagon_insn_info *edge_insn;
  bool start_at_the_next_packet;
  int i;
  int j;
  int num_edges = 0;
  /* This fixed way of book keeping will need to be updated */
  edge sorted_edge_list[SORTED_EDGE_LIST_SIZE];

  hexagon_sanity_check_cfg_packet_info();

#if 0
  verify_flow_info();
#endif /* 0 */

  FOR_EACH_BB (bb){
    if(!(BB_HEAD_PACKET (bb) && BB_END_PACKET (bb))
       || !JUMP_P (BB_END (bb))){
      continue;
    }
    /* Construct a sorted list of edges. */
    num_edges = 0;
    FOR_EACH_EDGE (e, ei, bb->succs){
      edge last_edge = e;
      /* Insert in sorted order. */
      for(i = 0; i < num_edges; i++){
        if(e->probability > sorted_edge_list[i]->probability){
          last_edge = sorted_edge_list[num_edges - 1];
          for(j = num_edges - 1; j > i; j--){
            sorted_edge_list[j] = sorted_edge_list[j - 1];
          }
          sorted_edge_list[i] = e;
          break;
        }
      }
      if(num_edges < SORTED_EDGE_LIST_SIZE){
        sorted_edge_list[num_edges] = last_edge;
        num_edges++;
      }
    }
    for(j = 0; j < num_edges; j++){
      e = sorted_edge_list[j];
      successor_bb = e->dest;
      if(e->flags & EDGE_COMPLEX
         || successor_bb->index == EXIT_BLOCK
         || !(BB_HEAD_PACKET (successor_bb) && BB_END_PACKET (successor_bb))
         || !single_pred_p(successor_bb)){
      /* || e->probability < 0.1 ) ??? Can set a threshold  to prevent low
         probability code from speculation, but need more investigation.
      */
        continue;
      }
      gcc_assert(single_pred(successor_bb) == bb);
      gcc_assert(BB_HEAD_PACKET (bb));
      gcc_assert(BB_END_PACKET (bb));
      gcc_assert(BB_HEAD_PACKET (successor_bb));
      gcc_assert(BB_END_PACKET (successor_bb));
      top_packet = BB_HEAD_PACKET (bb);
      forward_edge_packet = BB_END_PACKET (bb);
      back_edge_packet = BB_HEAD_PACKET (successor_bb);
      last_packet = BB_END_PACKET (successor_bb);
      gcc_assert(top_packet->num_insns > 0);
      gcc_assert(forward_edge_packet->num_insns > 0);
      gcc_assert(back_edge_packet->num_insns > 0);
      gcc_assert(last_packet->num_insns > 0);
      packet = back_edge_packet;
      while(packet && packet->prev != last_packet){
        for(i = 0; i < packet->num_insns; i++){
          COPY_HARD_REG_SET(prev_live_out, BB_LIVE_OUT (bb));
          original_insn = packet->insns[i];
          insn = original_insn;

          /* Don't try to reorder the final control flow insn if present. */
          if(control_flow_insn_p (insn->insn)){
            if(packet->num_insns > 1 || packet == back_edge_packet){
              break;
            }
            target_packet = packet->prev;
            while (target_packet->num_insns == 0 && target_packet != back_edge_packet){
              target_packet = target_packet->prev;
            }
            if(!hexagon_can_add_insn_to_packet_p(&insn, target_packet)){
              target_packet = target_packet->next;
              if(target_packet == packet){
                break;
              }
            }		  
            hexagon_remove_insn_from_packet(packet, original_insn);
            hexagon_add_insn_to_packet(target_packet, insn, false);
            break;
          }

          /* We can't pull up insns dependent on an insn in the same packet. */
          if(hexagon_packet_insn_internal_dependence_p(packet, insn)){
            continue;
          }

          /* pull up */
          target_packet = packet;
          start_at_the_next_packet = false;
          while(target_packet != top_packet){
            if(target_packet == back_edge_packet){
              target_packet = forward_edge_packet;
              edge_insn = target_packet->insns[target_packet->num_insns - 1];
              gcc_assert(HEXAGON_JUMP_P (edge_insn));
              if(hexagon_can_speculate_p(insn, bb)){
                /* speculate */
              }
              else if(HEXAGON_CONDITIONAL_P (edge_insn)
                      && !HEXAGON_GPR_CONDITION_P (edge_insn)
                      && (e->flags & EDGE_FALLTHRU
                          || HEXAGON_DIRECT_JUMP_P (edge_insn))
                      && hexagon_predicable_p(insn)){
                /* predicate */
                insn = hexagon_predicate_insn(insn, edge_insn,
                                            e->flags & EDGE_FALLTHRU);
                insn->transformed_at_packet = target_packet;
              }
              else if(!HEXAGON_CONDITIONAL_P (edge_insn)
                      && HEXAGON_DIRECT_JUMP_P (edge_insn)){
                /* We can always move an insn across an uncodtional direct
                   jump. */
              }
              else {
                target_packet = back_edge_packet;
                break;
              }
              hexagon_add_live_out(insn, bb);
            }
            else {
              target_packet = target_packet->prev;
            }
            /* dependent? */
            if(hexagon_packet_insn_dependence_p(target_packet, &insn, true)){
              start_at_the_next_packet = true;
              break;
            }
            /* anti-dependent? */
            if(hexagon_packet_insn_internal_dependence_p(target_packet, insn)){
              break;
            }
          }

          /* trickle down */
          if(start_at_the_next_packet){
            goto try_the_next_packet;
          }
          while(target_packet != packet){
            if(hexagon_insn_fits_in_packet_p(insn, target_packet)){
              break;
            }

            try_the_next_packet:

            while(insn->transformed_at_packet == target_packet){
              insn = insn->stack;
            }
            if(target_packet == forward_edge_packet){
              target_packet = back_edge_packet;
              COPY_HARD_REG_SET( BB_LIVE_OUT(bb), prev_live_out);
            }
            else {
              target_packet = target_packet->next;
            }
          }

          if(target_packet != packet){
            hexagon_move_insn(original_insn, packet, insn, target_packet, false);
            i--;
          }
          insn->stack = NULL;
          insn->transformed_at_packet = NULL;
        }
        packet = packet->next;
      }

      /* remove empty packets */
      packet = back_edge_packet;
      while(packet != last_packet){
        while(packet->next && packet->next->num_insns == 0){
          if(packet->next == BB_END_PACKET (successor_bb)){
            BB_END_PACKET (successor_bb) = packet;
          }
          if(packet->next->next){
            packet->next->next->prev = packet;
          }
          packet->next = packet->next->next;
        }
        if(packet == BB_END_PACKET (successor_bb)){
          break;
        }
        packet = packet->next;
      }
    }
  }


  if(dump_file){
    fputs("\n\n\n\nall basic blocks:\n\n", dump_file);
    FOR_EACH_BB (bb){
      hexagon_print_bb_packets(dump_file, bb);
    }
    fputs("\n\n\n\n", dump_file);
    FOR_EACH_BB (bb){
      fputs("BB_HEAD:\n", dump_file);
      print_rtl_single(dump_file, BB_HEAD (bb));
      fputs("BB_END:\n", dump_file);
      print_rtl_single(dump_file, BB_END (bb));
    }
    fputs("\n\n\n\n", dump_file);
    print_rtl(dump_file, get_insns());
  }
#if 0
  verify_flow_info();
#endif /* 0 */
  /* CLEANUP_CROSSJUMP will not work any more here,
     but it is OK to try to clean up potential empty BBs
     if any were created by the PULL-UP phase
  */
  cleanup_cfg(CLEANUP_EXPENSIVE);

}




static void
hexagon_init_packing_info(bool need_bb_info)
{
  basic_block bb;
  struct hexagon_bb_aux_info *new_bb_aux;

  dfa_start();

  hexagon_head_packet = NULL;
  hexagon_tail_packet = NULL;

  if(need_bb_info){
    df_set_flags(DF_LR_RUN_DCE);
    df_note_add_problem();
    df_analyze();
    df_set_flags(DF_DEFER_INSN_RESCAN);

    hexagon_head_bb_aux = NULL;
    new_bb_aux = NULL;
    FOR_EACH_BB (bb){
      if(hexagon_head_bb_aux == NULL){
        hexagon_head_bb_aux = (struct hexagon_bb_aux_info *)
            ggc_alloc_cleared(sizeof(struct hexagon_bb_aux_info));
        new_bb_aux = hexagon_head_bb_aux;
      }
      else {
        new_bb_aux->next = (struct hexagon_bb_aux_info *)
            ggc_alloc_cleared(sizeof(struct hexagon_bb_aux_info));
        new_bb_aux = new_bb_aux->next;
      }
      REG_SET_TO_HARD_REG_SET (new_bb_aux->live_out, df_get_live_out(bb));
      bb->aux = new_bb_aux;
    }
  }
}




static void
hexagon_remove_new_values(void)
{
  struct hexagon_packet_info *packet;
  int i;

  for(packet = hexagon_head_packet; packet; packet = packet->next){
    for(i = 0; i < packet->num_insns; i++){
      if(HEXAGON_NEW_GPR_P (packet->insns[i])){
        hexagon_dot_oldify_gpr(packet->insns[i]);
      }
    }
  }
}




static void
hexagon_free_packing_info(bool free_bb_info)
{
  basic_block bb;

  if(free_bb_info){
    hexagon_remove_new_values();

    FOR_EACH_BB (bb){
      bb->aux = NULL;
    }
    hexagon_head_bb_aux = NULL;

    df_finish_pass(false);
  }

  hexagon_head_packet = NULL;
  hexagon_tail_packet = NULL;

  dfa_finish();
}


/****************************************/
/*** Functions for New Value Jump *******/
/****************************************/


static bool
hexagon_nvj_new_gpr_p(
  struct hexagon_insn_info *consumer,
  struct hexagon_dependence *dependence
)
{

  rtx compare;
  rtx operand1, operand2;

  /* get compare portion of the nvj, 
    from the first 1st elemenet of insn*/
  /* get compare - cmp.XX(Ns.new, YY) */
  compare = hexagon_nvj_get_compare(consumer->insn, 0);

  /*get the operands, Ns.new and YY*/
  operand1 = hexagon_nvj_get_operand(compare, 1);
  operand2 = hexagon_nvj_get_operand(compare, 2);
  
  if ( GET_CODE(operand1) == UNSPEC &&  
      XINT(operand1,1) == UNSPEC_NEW_VALUE && 
      XVECEXP(operand1,0,0) == dependence->use ) 
  {
    return true;
  }

  if ( GET_CODE(operand2) == UNSPEC &&  
       XINT(operand2,1) == UNSPEC_NEW_VALUE && 
       XVECEXP(operand2,0,0) == dependence->use ) 
  {
    return true;
  }
  return false;
}




/*Given: an instruction, 
 *       any two packets (from and two in downward flow)
 *Returns true if insn can be moved from from_packet to the to_packet
 */      
static bool
hexagon_move_insn_across_packet_down(
  struct hexagon_packet_info *from,
  struct hexagon_packet_info *to, 
  struct hexagon_insn_info  *insn) 
{
  while( from != to)
  {
    if (!hexagon_move_insn_down_p(insn, from, from->next)) 
      return (false); 
    from = from->next;
  }
  return (true);
}

static bool 
hexagon_move_all_insn_across_packet_down(
  struct hexagon_packet_info *from,
  struct hexagon_packet_info *to)
{
  int i; 

  if (from->num_insns == 1)
  {
    /*there is only only one instruction in the packet and it will be moved to the 
    candidate packet and this packet will be removed */
    return true;
  }

  /* make sure you can move all the packets*/
  for(i = 0; i < from->num_insns; i++)
  {
    if (!hexagon_move_insn_across_packet_down(from, to, from->insns[i]))
    {
      return false;
    }
  }
  return true;
}

static bool 
hexagon_nvj_move_possible(
  struct hexagon_packet_info *candidate_packet,
  struct hexagon_packet_info *prev_packet,
  struct hexagon_insn_info *jump_insn_info, 
  struct hexagon_insn_info *comp_insn_info, 
  rtx *oper, 
  rtx *pred,
  rtx *op1, 
  rtx *op2,
  rtx *b_lab,
  struct hexagon_packet_info **src_packet,
  struct hexagon_insn_info **src_insn,
  int *op_cnt
)
{
  rtx feeder_reg, feeder_reg1; 
  rtx nvj_instruction, nvj_insn_rtx;
  enum rtx_code compare_code, jump_code;
  bool resource_avail = false;
  bool move_possible = false;
  *src_insn = NULL;
  *src_packet = NULL;
  struct hexagon_reg_access *read;


  for (read=comp_insn_info->reg_reads; read; read=read->next)
  {
    feeder_reg1 = XEXP(SET_SRC(PATTERN(comp_insn_info->insn)),*op_cnt);
    /*for tstbit */
    if (GET_CODE(feeder_reg1) == ZERO_EXTRACT ) 
    {
      feeder_reg = XEXP(feeder_reg1,*op_cnt);
    }
    else 
      feeder_reg = feeder_reg1;


    *src_packet = hexagon_get_source_packet(prev_packet, feeder_reg, comp_insn_info, src_insn);
    if (!*src_packet || GET_MODE(XEXP(PATTERN((*src_insn)->insn),*op_cnt))!=SImode) 
    {
      /*reject everything that not SI - pattern won't support it */
      /*src packet is not in the same bb or source is from a combine */
      /*move on to the next operand if its reg or bail out*/ 
      continue;
    }

    compare_code = GET_CODE(SET_SRC(PATTERN(comp_insn_info->insn)));
    jump_code    = GET_CODE(XEXP(SET_SRC(PATTERN(jump_insn_info->insn)),0));

    /* swap the compare code depeding on the condition of jump and compare*/
    /* tstbit comparison */
    if (GET_CODE(feeder_reg1) == ZERO_EXTRACT ) 
    {
      /* xor jump and compare code */
      if ( jump_code ^ compare_code)
        compare_code = NE;
      else 
        compare_code = EQ;
    }
    else
      /*non tstbit comparison */
    {
      if (jump_code ==  EQ )
      {
        switch(compare_code) 
        {
          case EQ:  compare_code = NE; break;
          case NE:  compare_code = EQ; break;
          case GT:  compare_code = LE; break;
          case LE:  compare_code = GT; break;
          case GTU: compare_code = LEU; break;
          case LEU: compare_code = GTU; break;
          default: break;
        }
      }
    }


    *oper  = gen_rtx_fmt_ee(compare_code, SImode, NULL_RTX, NULL_RTX);
    *pred  = SET_DEST(PATTERN(comp_insn_info->insn));
    *op1   = XEXP(SET_SRC(PATTERN(comp_insn_info->insn)),0);
    *op2   = XEXP(SET_SRC(PATTERN(comp_insn_info->insn)),1);
    *b_lab = XEXP(SET_SRC(PATTERN(jump_insn_info->insn)),1);


    start_sequence();

    if (GET_CODE(feeder_reg1) == ZERO_EXTRACT ) 
    {
      rtx tstbit_operands = *op1;
      *op1 = XEXP(tstbit_operands, 0);
      *op2 = XEXP(tstbit_operands, 2);
      nvj_instruction =  gen_new_value_jump_tstbit( *oper, *op1, *op2, *b_lab, *pred ); 
    }
    else 
    {
      if (*op_cnt==0)
        nvj_instruction =  gen_new_value_jump1( *oper, *op1, *op2, *b_lab, *pred ); 
      else
        nvj_instruction =  gen_new_value_jump2( *oper, *op1, *op2, *b_lab, *pred ); 
    }

    nvj_insn_rtx = emit_jump_insn ( nvj_instruction );
    resource_avail =  hexagon_nvj_check_resources ( *src_insn, candidate_packet, comp_insn_info, jump_insn_info, nvj_insn_rtx);
    end_sequence();

    if (resource_avail) 
    {
      hexagon_remove_insn_from_packet(candidate_packet, comp_insn_info);
      move_possible = hexagon_move_insn_across_packet_down(*src_packet, candidate_packet, *src_insn);
      /*Make a decision whether nvj should be created or not*/
      /*Don't create nvj, if the packet can not be removed*/
      if (move_possible && !optimize_size)
        move_possible &= hexagon_move_all_insn_across_packet_down(*src_packet, candidate_packet);
      hexagon_add_insn_to_packet(candidate_packet, comp_insn_info, false);
      if (move_possible) 
      {
        return true;
      }
    }

    /* operand1 could not be .newifed, try operand2 - only for cmp.gt and cmp.gtu */
    if ((GET_CODE(feeder_reg1) == ZERO_EXTRACT) ||
         compare_code == NE || compare_code == EQ ) 
      /* dont' try for tstbit, and cmp.eq */
      break; 
    else 
      (*op_cnt)++;
  }

  return false;
}

static int 
hexagon_get_writes_count(struct hexagon_insn_info *insn_info) 
{
  int cnt=0;
  struct hexagon_reg_access *write;
  for (write=insn_info->reg_writes; write; write = write->next) cnt++;
  return (cnt);
}

static int 
hexagon_get_reads_count(struct hexagon_insn_info *insn_info) 
{
  int cnt=0;
  struct hexagon_reg_access *read;
  for (read=insn_info->reg_reads; read; read = read->next) cnt++;
  return (cnt);
}



/* Now that we have identified the feeder register, 
*  iterate over the prev packets, and find it's defination
*  (src_insn) and return the packet which contains the def.
*/ 
static struct hexagon_packet_info * 
hexagon_get_source_packet( 
              struct hexagon_packet_info *prev_packet,
              rtx feeder_reg, 
              struct hexagon_insn_info *d_insn, 
              struct hexagon_insn_info **s_insn) 
{
 int i;
 basic_block bb = BLOCK_FOR_INSN(d_insn->insn);
 *s_insn = NULL;
 
 while( prev_packet && 
     prev_packet->num_insns &&
     BLOCK_FOR_INSN(prev_packet->insns[0]->insn) == bb )
 {
  for( i = 0; i < prev_packet->num_insns; i++ ) 
  {
    if (!NOTE_P(prev_packet->insns[i]->insn) &&
        /* 
        1. don't assume pattern to have xexp
        2. check and reject the following conditions like
            a. post_update
            b. register pair
        */
				XEXP(PATTERN(prev_packet->insns[i]->insn),0) == feeder_reg) 
    {
      *s_insn = prev_packet->insns[i];
      return prev_packet;
    }
  }
  prev_packet=prev_packet->prev;
 }
 return (NULL);
}


static bool
hexagon_nvj_compare_p(rtx insn) 
{ 
  enum rtx_code code;
  enum machine_mode mode;
  rtx pattern;
  rtx const_int_operand  = NULL;
  rtx operand1;
  rtx operand2;

  if (GET_CODE(PATTERN(insn)) != SET)
  {
    return (false);
  }

  pattern = PATTERN(insn);

  code = GET_CODE(XEXP(pattern,1));
  mode = GET_MODE(XEXP(pattern,1));

  operand1 = XEXP(SET_SRC(pattern),0);
  operand2 = XEXP(SET_SRC(pattern),1);

  if (mode != BImode)
  {
    return (false);
  }

  /* new value jump supports only the following comparisons */
  if(!(code == NE  || code == EQ  ||
       code == LE  || code == GT  || 
       code == LEU || code == GTU))
  {
    return (false);
  }

  /* for tstbit, only #0 comparison is permitted*/
  if (GET_CODE(operand1) == ZERO_EXTRACT &&
      INTVAL(XEXP(operand1,2)) != 0 )
  {
    return (false);
  }

       
  /* Make sure compare uses either two registers or
     one register and an CONST_INT */
  if ( (GET_CODE(operand1) == REG) && 
       (!(GET_CODE(operand2) == CONST_INT || GET_CODE(operand2) == REG))) 
  {
    return (false);
  }
  if ( (GET_CODE(operand2) == REG) && 
       (!(GET_CODE(operand1) == CONST_INT || GET_CODE(operand1) == REG))) 
  {
    return (false);
  }

  /* reject if cmp.XX(r1,r1) case:peren_c++/Sec23/2_1/P23784.C*/
  if ((GET_CODE(operand1) == REG) && 
      (GET_CODE(operand2) == REG) && 
      (REGNO(operand1) == REGNO(operand2)))
  {
    return (false);
  }

  if (GET_CODE(operand1) == REG && GET_CODE(operand2) == CONST_INT)
    const_int_operand = operand2;
  if (GET_CODE(operand2) == REG && GET_CODE(operand1) == CONST_INT)
    const_int_operand = operand1;

  /* if one of operands of the compare is immediate, 
   * only allowed values are -1 to U5 ie 32*/
  if (const_int_operand)
  {
    switch(code) {
      case EQ:  
      case NE:
      case LE:
      case GT:
        if (INTVAL(const_int_operand) < -1 || INTVAL(const_int_operand) > 31)
          return (false);
        break;
      case GTU:
      case LEU:
        if ((INTVAL(const_int_operand) < 0)  || (INTVAL(const_int_operand) > 31))
          return (false);
        break;
      default:
        break;
    }
  }

  return (true);

}

/* 
* Validate that predicate is used only for jump and nothing else
*/
static struct hexagon_insn_info *
hexagon_nvj_query_compare(struct hexagon_packet_info *packet, struct hexagon_insn_info *jump_p_insn_info)
{
  struct hexagon_insn_info *compare_insn = NULL;
  int i, auto_anding_chk = 0;
  //unsigned int pred_no = (*jump_p_insn_info)->reg_reads->regno;
  unsigned int pred_no = jump_p_insn_info->reg_reads->regno;
  for( i = 0; i < packet->num_insns; i++ ) 
  {
    struct hexagon_insn_info *pred_insn = packet->insns[i];
    /*while we are at it, get the compare instruction*/

    /*this avoids cases like { r3 = r2; r2 = r1 } generated by combinesi_v4*/
    /*assumption: there will NOT be parallel RTX's one of which will be use of a predicate*/
    if (GET_CODE(PATTERN(pred_insn->insn)) == PARALLEL)
      continue;

    if ( HEXAGON_NEW_PREDICATE_P(pred_insn) &&
        !HEXAGON_DIRECT_JUMP_P (pred_insn)  && 
        ( hexagon_predicate_use_DImode(pred_insn)      || 
          hexagon_register_defined(pred_insn, pred_no) ||
          hexagon_register_used(pred_insn, pred_no))) 
    {
      /*there is another use/def of the predicate in this packet */
      return NULL;
    }
    
    if ( hexagon_nvj_compare_p(pred_insn->insn) )
    {
      if ( hexagon_register_defined(pred_insn, pred_no) )
      {
        compare_insn = pred_insn;
        /*auto anding also multiple register definitions*/
        if (++auto_anding_chk > 1)
        {
          return NULL;
        }
      }
    }

  }
  return compare_insn;
}

/*
* Determine if the new value jump can be created (along with other instructions)
* in the packet. 
*/
static bool
hexagon_nvj_check_resources ( 
     struct hexagon_insn_info *q_insn, 
     struct hexagon_packet_info *nvj_packet, 
     struct hexagon_insn_info *comp_insn,
     struct hexagon_insn_info *jump_insn, 
     rtx nvj_insn_rtx )
      

{
  struct hexagon_packet_info *d_packet;
  struct hexagon_insn_info *src_insn;
  int i=0;

  d_packet = (struct hexagon_packet_info *) ggc_alloc_cleared(sizeof(struct hexagon_packet_info));

  /*first copy all the non-jump/non-compare instructions*/
  for (i=0; i < nvj_packet->num_insns; i++ )
  {
    if ( (nvj_packet->insns[i] != comp_insn) &&
         (nvj_packet->insns[i] != jump_insn))
    {
      hexagon_add_insn_to_packet(d_packet, nvj_packet->insns[i], false); 
    }
  }

  /* see if nvj can be put in the packet */
  src_insn = hexagon_get_insn_info(nvj_insn_rtx);
  if (!hexagon_insn_fits_in_packet_p(src_insn, d_packet)) 
  {
    return false;
  }

  /*if nvj can be put, check to see if its source (.new) 
    can be put in the same packet, 
    and at the start of the packet - */
  hexagon_add_insn_to_packet(d_packet, src_insn, false); 
  return (hexagon_insn_fits_in_packet_p(q_insn, d_packet)); 
}


/* Given an instruction, return
*    true if compare uses combine registers
*/
static bool
hexagon_predicate_use_DImode( struct hexagon_insn_info *insn_info)
{
  rtx pattern = PATTERN(insn_info->insn);
  rtx uses = XEXP(pattern,1);
  if ((GET_CODE (XEXP(uses,1)) == REG && 
       GET_MODE (XEXP(uses,1)) == DImode) ||
      (GET_CODE (XEXP(uses,0)) == REG && 
       GET_MODE (XEXP(uses,0)) == DImode)
     )
  {
    return (true);
  }
  return (false);
}

/* reject if the operands of the compare instruction is def' in the packet */
static bool
hexagon_used_operands( struct hexagon_packet_info *packet, 
                     struct hexagon_insn_info *jump_insn_info,
                     struct hexagon_insn_info *comp_insn_info)
{
  int i, j, reads_cnt = hexagon_get_reads_count(comp_insn_info);
  for( i = 0; i < packet->num_insns; i++ ) 
  {
    if ( packet->insns[i] != jump_insn_info &&
         packet->insns[i] != comp_insn_info )
    {
      for (j=0; j<hexagon_get_writes_count(packet->insns[i]); j++)
      {
        unsigned int reg_no = comp_insn_info->reg_reads->regno;
        if (hexagon_register_defined(packet->insns[i], reg_no))
        {
          return (true);
        }

        if (reads_cnt > 1)
        {
          reg_no = (comp_insn_info)->reg_reads->next->regno;
          if (hexagon_register_defined(packet->insns[i], reg_no))
          {
            return (true);
          }
        } 
      }
    }
  }
  return (false);
}

/*
* Given an instruction insn_info, return true
*    if it defines/loads the register reg_no  
*/
static bool
hexagon_register_defined(struct hexagon_insn_info *insn_info, unsigned int reg_no) 
{
  struct hexagon_reg_access *write = insn_info->reg_writes;
  while(write) 
  {
    if (write->regno == reg_no) 
    {
      return (true);
    }
    write = write->next;
  }
  return (false);
}

/*
* Given an instruction insn_info, return true
*     if it uses the register reg_no
*/
static bool
hexagon_register_used(struct hexagon_insn_info *insn_info, unsigned int reg_no) 
{
  struct hexagon_reg_access *read = insn_info->reg_reads;
  while(read) 
  {
    if (read->regno == reg_no) 
    {
      return (true);
    }
    read = read->next;
  }
  return (false);
}


static bool
hexagon_in_bb_live_out( basic_block bb, struct hexagon_insn_info *q_insn)
{
  struct hexagon_reg_access *write;

  for(write = q_insn->reg_reads; write; write = write->next)
  {
    if(TEST_HARD_REG_BIT (BB_LIVE_OUT (bb), write->regno))
    {
      return (true);
    }
  }
  return (false);
}

/* Given a packet and array of two rtx
 * returns 
 *    false if 
 *       a. there are no jumps in the packet 
 *     b. two dumps (dual jumps not allowed)
 *    true  if there is a single jump in the packet
 *    does not modify the array of rtx if there are(is) no jump
 *    modifies the first  element of rtx with the jmp if it's a jump (single jump packet)
 *    modifies the second element of rtx with the jmp if it's the second jump and can be
            converted into the compound new value jump (dual jump & copacket)
 */
static struct hexagon_insn_info *
hexagon_nvj_query_jump( 
  struct hexagon_packet_info *packet, 
  bool   *dot_new_predicate,
  basic_block bb) 

{
  int i, nvj_count = 0;
  struct hexagon_insn_info *jump_insn;
  for( i = 0; i < packet->num_insns; i++ ) 
  {
    struct hexagon_insn_info *insn_info = packet->insns[i];
    if ( HEXAGON_DIRECT_JUMP_P(insn_info) && 
         HEXAGON_CONDITIONAL_P(insn_info) && 
         !hexagon_in_bb_live_out(bb, insn_info)
       ) 
    {
    
    nvj_count++;
    jump_insn=insn_info;

    /*if dot new predicate*/
    if (HEXAGON_NEW_PREDICATE_P(insn_info))
      *dot_new_predicate = true;
    else 
      *dot_new_predicate = false; /*this is just for the breakpoint - don't need it */
    }
  }


  if (nvj_count == 1 ) return (jump_insn);

  /*just making sure, in case of dual jumps - it might have been set to true */
  *dot_new_predicate = false;
  return NULL;
}
 

static void 
hexagon_new_value_jump(void)
{
 /* 
 * 1. Scan the packets from the bottom of the basic looking for predicated 
 *    jump, - it's either .new or otherwise.
 *
 * 2. a. If pX.new is found, we have a two packet scenario.
 *    a. i.   scan the predecessor of this packet,
 *       ii.  if the predecessor has the producer that feeds the compare (check
 *            both the operands of the compare), you've found the guy, 
 *            collapse compare and jump instructions into one
 *            compound new value jump and move the producer/feeder to the compare 
 *            instruction to the same packet.
 *       iii. if the predecessor does not have the producer that feeds the 
 *            compare, repeat 2.a.ii until top of the basic block is reached.
 *
 * 2. b. If pX is found, we have a three packet scenario. This is little more complicated
 *       and less beneficial -
 *    a. i.  scan the predecessor and the precedessor of the predessor of this packet, 
 *       ii. if the predecessor has compare I that feeds the jump, temporalily move 
 *           the compare to the packet which contains jump insn ( see if the packet, 
 *           which contained the compare could be removed) and continue traversing
 *           up - towards the top of the basic block, until you find the feeder to 
 *           the compare. If the feeder is found, try moving the feeder to the 
 *           packet which contains the jump. If can be moved, see if the packet which 
 *           contained the feeder can be removed. If at least, one of the packets 
 *           can be removed, continue otherwise give up. 
 * 
 * Note: In three packet scenario, I did not any scenario, where I could remove at least 
 * one of the packets.
 */

  basic_block bb;

  FOR_EACH_BB(bb)
  {
    struct hexagon_packet_info  *packet, *nvj_packet;
    struct hexagon_insn_info    *compare_insn_info = NULL;
    struct hexagon_insn_info    *jump_p_insn_info = NULL;
    bool                      dot_new_predicate = false;
    rtx                       nvj_insn;
    rtx                       nvj_instruction;

    packet = BB_END_PACKET(bb);

    if (packet && packet->prev && 
           packet->prev->num_insns &&
           BLOCK_FOR_INSN(packet->prev->insns[0]->insn) == bb) 
    {
      if ( !(jump_p_insn_info=hexagon_nvj_query_jump(packet, &dot_new_predicate, bb)))
      {
        continue;
      }
      else /* single jumps */
      {
        struct hexagon_insn_info *src_insn;
        struct hexagon_packet_info *src_packet;
        rtx comp_operator, p_reg, operand1, operand2, branch_label; 
        int op_cnt = 0;
        struct hexagon_insn_info *new_insn; 

        nvj_packet = packet;
        if (dot_new_predicate)  /* predicate is generated in the same packet, two packets */
        {
          if (!(compare_insn_info = hexagon_nvj_query_compare(nvj_packet, jump_p_insn_info)))
          {
          /*predicate is used, other than for jump insn*/
             continue;
          }

          if (hexagon_used_operands(nvj_packet, jump_p_insn_info, compare_insn_info))
          {
            /*one of operands of the compare is defined in the same packet*/
            continue;
          }


          /* get the feeder to the compare and search in the prev packets 
           * of the bb 
          op_cnt = hexagon_get_reads_count(compare_insn_info);
           */
          if (!hexagon_nvj_move_possible(nvj_packet, packet->prev, jump_p_insn_info, 
                                       compare_insn_info, &comp_operator, &p_reg, 
                                       &operand1, &operand2, &branch_label, &src_packet, 
                                       &src_insn,  &op_cnt)) 
          {
            continue;
          }

          hexagon_move_insn(src_insn, src_packet, src_insn, nvj_packet, true);

          /*now call the hexagon genroutine to get the actual instruction */
          /*if the compare is a tstbit, only first operand can be .new  */
          if (GET_CODE(XEXP(SET_SRC(PATTERN(compare_insn_info->insn)),0)) == ZERO_EXTRACT)
          {
            nvj_instruction = gen_new_value_jump_tstbit(comp_operator, operand1, operand2, branch_label, p_reg);
          }
          else 
          {
            if (op_cnt==0)
              nvj_instruction = gen_new_value_jump1(comp_operator, operand1, operand2, branch_label, p_reg);
            else
              nvj_instruction = gen_new_value_jump2(comp_operator, operand1, operand2, branch_label, p_reg);

          }
          /*generate a nvj instruction after the jump; later - remove old jump insn */
          nvj_insn = emit_jump_insn_after(nvj_instruction, jump_p_insn_info->insn);

          /*add a jump label*/
          JUMP_LABEL(nvj_insn) = XEXP(branch_label,0);

           /*ensuring that code label can be accessed through label ref */
          XEXP(XEXP(XVECEXP(PATTERN(nvj_insn),0,0),1),1) = branch_label;

          if (!(find_reg_note(nvj_insn, REG_LABEL_OPERAND, branch_label)))
          {
            add_reg_note(nvj_insn, REG_LABEL_OPERAND, branch_label);
          }

          /* assign the block number for the instruction*/
          set_block_for_insn(nvj_insn, BLOCK_FOR_INSN(jump_p_insn_info->insn));

          hexagon_remove_insn_from_packet(nvj_packet, jump_p_insn_info);
          delete_insn(jump_p_insn_info->insn);

          hexagon_remove_insn_from_packet(nvj_packet, compare_insn_info);
          delete_insn(compare_insn_info->insn);

          new_insn = hexagon_get_insn_info(nvj_insn);
          new_insn->flags |= HEXAGON_NEW_GPR;
          hexagon_add_insn_to_packet(nvj_packet, new_insn, false);

          if (src_packet->num_insns == 0 ) 
          {
            /* remove empty packet */
            hexagon_remove_empty_packet(bb, src_packet);
          }
        } 
        else  /* three packets */
        {
          /* In qbench, I did not fidn any three packet cases, where I would reduce
             the number of packets, so I am not implementing them. 
             SPEC2000 or SPEC2006 may have opportunities - in spec analysis, if I find 
             opportunities, I will implement them
          */
        }
      } /* jump found*/
    }   /* packet is not a candidate */ 
  }     /* iterated over all the basic blocks in proc*/

}       /* end of hexagon_new_value_jump */


static void
hexagon_remove_empty_packet( 
              basic_block bb,
              struct hexagon_packet_info *packet)
{
  /* There is always a sentinal packet */
  if (BB_HEAD_PACKET(bb) == packet) 
  {
    BB_HEAD_PACKET(bb) = packet->next;
  }

  /* There is always a sentinal packet */
  if (packet->prev != NULL) 
  {
    packet->prev->next = packet->next;
  }
  if (packet->next != NULL) 
  {
    packet->next->prev = packet->prev;
  }
  else 
  {
    packet->prev = NULL;
  }
}



static void
hexagon_packet_optimizations(void)
{
  if(!TARGET_PACKETS){
    return;
  }

  shorten_branches(get_insns());

  hexagon_init_packing_info(true);
  hexagon_pack_insns(true);

  if (TARGET_V4_FEATURES && TARGET_NEW_VALUE_JUMP)
    hexagon_new_value_jump();

  if (TARGET_PULLUP)
    hexagon_pull_up_insns();

  hexagon_free_packing_info(true);
}

static void
hexagon_final_pack_insns(void)
{
  if(!TARGET_PACKETS){
    return;
  }

  hexagon_init_packing_info(false);
  hexagon_pack_insns(false);

  if(TARGET_V4_FEATURES && TARGET_DUPLEX_SCHEDULING) 
    {
      hexagon_pack_duplex_insns();
    }

  shorten_branches(get_insns());
}


/*------------------------------
Functions for duplex scheduling
-------------------------------*/

/* The list of sub-instructions for duplex scheduling was obtained from 
   the V4 Architecture Specification version 0.94 */

enum duplex_move_direction {
  UP,
  DOWN,
  BOTH
};

/* hexagon_duplex_register_p()
   Predicate that checks if the given register can be used in a duplex 
   instruction. This will identify instructions that are not 
   sub-instructions as sub-instructions. However, refining this function
   to be more accurate does not result in codesize reductions in AMSS */
static bool
hexagon_duplex_register_p(int regno)
{
  return (regno == DUPLEX_PRED_REG || 
          regno == SP_REGNUM ||
          regno == FP_REGNUM ||
          regno == LINK_REGNUM ||
          (regno >= DUPLEX_REG_LOW_START &&
          regno <= DUPLEX_REG_LOW_END) ||
          (regno >= DUPLEX_REG_HIGH_START &&
           regno <= DUPLEX_REG_HIGH_END));
}

/*
  hexagon_duplex_insn_p()
  Given: an instruction insn
  Returns true if the instruction is a duplex instruction
*/
static bool
hexagon_duplex_insn_p(struct hexagon_insn_info* insn)
{
  struct hexagon_reg_access *read;
  struct hexagon_reg_access *write;

  if (get_attr_duplex(insn->insn) != DUPLEX_YES)
    {
      return (false);
    }

  for(read = insn->reg_reads; read; read = read->next) 
    {
      if (!hexagon_duplex_register_p (read->regno))
        {
          return (false);
        }
    }

  for(write = insn->reg_writes; write; write = write->next)
    {
      if (!hexagon_duplex_register_p (write->regno))
        {
          return (false);
        }
    }
  return (true);
}


/*
  hexagon_move_insn_up_p()
  Given: an instruction insn
         a packet containing insn: succ_packet
         the previous packet: pred_packet
  Returns true if insn can be moved from succ_packet to pred_packet
*/
static bool
hexagon_move_insn_up_p(struct hexagon_insn_info* insn, 
                     struct hexagon_packet_info* pred_packet, 
                     struct hexagon_packet_info* succ_packet)
{
  int i;
  struct hexagon_dependence *dependencies = NULL, *dep = NULL;

  /* The following types of dependences prevent an instruction I from succ_packet
     from being moved into pred_packet: 
     1. If I is a control flow instruction
     2. A control dependence between an instruction in pred_packet and I
     3. A true dependence between an instruction in pred_packet and I
     4. An output dependence between an instruction in pred_packet and I
     5. If I produces a value used by a dot-new consumer in succ_packet
     6. If I consumes a dot-new value produced by an instruction in succ_packet
     7. An "true-dependence" between I and an instruction in succ_packet
        This is really an anti-dependence between an instruction in succ_packet
        and I but the depencency checker ignores the parallel semantics of a 
        packet. Hence we check if there is a "true-dependence" between an 
        instruction in succ_packet and I
  */

  /* Case 1 */
  if (HEXAGON_CONTROL_P (insn))
    {
      return false;
    }


  /* First, iterate over pred_packet and check for cases 2, 3, and 4 */
  for (i = 0; i < pred_packet->num_insns; ++i)
    {
      struct hexagon_insn_info *pred_insn = pred_packet->insns[i];
      
      /* Check for control instructions in pred_packet */
      dependencies = hexagon_control_dependencies(pred_insn, insn);
      if (dependencies != NULL) 
        {
          return false;
        }
      
      dependencies = hexagon_true_dependencies(pred_insn, insn);
      if (dependencies != NULL) 
        {
          return false;
        }
      
      dependencies = hexagon_output_dependencies(pred_insn, insn);
      if (dependencies != NULL) 
        {
          return false;
        }
    }


  /* Then, iterate over succ_packet and check for cases 5, 6, and 7 */
  for (i = 0; i < succ_packet->num_insns; ++i)
    {
      struct hexagon_insn_info *succ_insn = succ_packet->insns[i];
      
      /* Don't compute dependences of insn with itself */
      if (insn == succ_insn)
        {
          continue;
        }

      /* Case 5 */
      dependencies = hexagon_true_dependencies(succ_insn, insn);
      for(dep = dependencies; dep; dep = dep->next)
        {
         if (dep->type == HEXAGON_DEP_REGISTER) 
           {
             /* Check for dependence due to p.new */
             if (HEXAGON_NEW_PREDICATE_P (insn) && P_REGNO_P (REGNO (dep->use)))
               {
                 return false;
               }
           }
        }
      
      /* Cases 6 and 7 */
      dependencies = hexagon_true_dependencies(insn, succ_insn);
      if (dependencies != NULL)
        {
          return false;
        }
    }

  return true;
}


/*
  hexagon_move_insn_down_p():
  Given: an instruction insn
         a packet containing insn: pred_packet
         the next packet: succ_packet
  Returns true if insn can be moved from pred_packet to succ_packet
*/
static bool
hexagon_move_insn_down_p(struct hexagon_insn_info* insn, 
                       struct hexagon_packet_info* pred_packet, 
                       struct hexagon_packet_info* succ_packet)
{
  int i;
  struct hexagon_dependence *dependencies = NULL, *dep = NULL;

  /* The following types of dependences prevent an instruction I from pred_packet
     from being moved into succ_packet:
     1. If I is a control flow instruction and succ_packet is non-empty
     2. An anti-dependence between I and an instruction in pred_packet
     3. A control instruction in pred_packet
     4. If I produces a value used by a dot-new consumer in pred_packet
     5. If I consumes a dot-new value produced by an instruction in pred_packet 
     (TODO: This can be relaxed by dot-oldifying I)
     6. A true dependence between I and an instruction in succ_packet
     7. An output dependence between I and an instruction in succ_packet
  */

   /* Case 1 */
  if (HEXAGON_CONTROL_P (insn) && (succ_packet->num_insns > 0))
    {
      return false;
    }
 
  /* First, iterate over pred_packet and check for cases 2, 3, and 4 */
  for (i = 0; i < pred_packet->num_insns; ++i)
    {
      struct hexagon_insn_info *pred_insn = pred_packet->insns[i];
      
      /* Don't compute dependences of insn with itself */
      if (pred_insn == insn) 
        {
          continue;
        }
      
      /* Check for control instructions in pred_packet */
      if (HEXAGON_JUMP_P (pred_insn) || HEXAGON_CALL_P (pred_insn) || 
          HEXAGON_EMULATION_CALL_P (pred_insn))
        {
          return false;
        }

      /* Check for an anti-dependence in pred_packet */
      dependencies = hexagon_anti_dependencies(insn, pred_insn);
      if (dependencies != NULL)
        {
          return false;
        }

      /* Check for dot-new consumers in pred_packet
         There are two types of dot-new producer-consumer situations:
         1. I produces a predicate that is consumed by a p.new consumer
         2. I produces a gpr that is consumed by a new-value store 
      */
      dependencies = hexagon_true_dependencies(insn, pred_insn);
      for(dep = dependencies; dep; dep = dep->next)
        {
          if (dep->type == HEXAGON_DEP_REGISTER) {
            /* Check for dependence due to p.new */
            if (HEXAGON_NEW_PREDICATE_P (pred_insn) && P_REGNO_P(REGNO(dep->use)))
              {
                return false;
              }
            /* Check for dependence due to r.new */
            if (HEXAGON_NEW_GPR_P (pred_insn))
              {
                rtx pattern, new_value;
                pattern = copy_rtx(PATTERN (pred_insn->insn));
                for_each_rtx(&pattern, hexagon_find_new_value, &new_value);
                /* new_value is wrapped in an unspec; hence look 
                   at XVECEXP(new_value, 0, 0) */
                if (XVECEXP(new_value, 0, 0) == dep->use)
                  {
                    return false;
                  }
              }
          }
        }
    }

  /* Case 5 */
  if (HEXAGON_NEW_PREDICATE_P (insn))
    {
      return false;
    }

  /* Then, iterate over succ_packet and check for cases 6 and 7 */
  for (i = 0; i < succ_packet->num_insns; ++i)
    {
      struct hexagon_insn_info *succ_insn = succ_packet->insns[i];

      dependencies = hexagon_true_dependencies(insn, succ_insn);
      if (dependencies != NULL) 
        {
          return false;
        }
      dependencies = hexagon_output_dependencies(insn, succ_insn);
      if (dependencies != NULL) 
        {
          return false;
        }
    }

  return true;
}

/*
  Given a predecessor packet and a successor packet and a direction
  to move instructions, check if we can create a duplex by moving
  from one of these packets to another */
static bool
hexagon_pair_duplex_insn(struct hexagon_packet_info* pred_packet, 
                       struct hexagon_packet_info* succ_packet,
                       enum duplex_move_direction dir)
{
  int i;

  if (dir == DOWN || dir == BOTH)
    {
      /* 
         First, check if we can move a duplex instruction from
         pred_packet to succ_packet:
         If pred_packet contains a duplex instruction that fits in 
         the next packet and the dependences allow us to move the instruction 
         into the next packet, conduct the move.
      */ 
      for(i = 0; i < pred_packet->num_insns; ++i)
        {
          struct hexagon_insn_info *insn = pred_packet->insns[i];
          if (hexagon_duplex_insn_p(insn) && 
              hexagon_insn_fits_in_packet_p(insn, succ_packet) &&
              hexagon_move_insn_down_p(insn, pred_packet, succ_packet))
            {
              hexagon_move_insn(insn, pred_packet, insn, succ_packet, true);
              return (true);
            }
        }
    }

  if (dir == UP || dir == BOTH)
    {
      /* 
         Then, check if we can move a duplex instruction from
         succ_packet to pred_packet:
         If succ_packet contains a duplex instruction that fits in 
         the previous packet and the dependences allow us to move the instruction 
         into the previous packet, conduct the move.
      */
      for(i = 0; i < succ_packet->num_insns; ++i)
        {
          struct hexagon_insn_info *insn = succ_packet->insns[i];
          if (hexagon_duplex_insn_p (insn) &&
              hexagon_insn_fits_in_packet_p(insn, pred_packet) &&
              hexagon_move_insn_up_p(insn, pred_packet, succ_packet))
            {
              hexagon_move_insn(insn, succ_packet, insn, pred_packet, false);
              return (true);
            }
        }
    }

  /* 
     If none of these succeed, we should attempt a swap between
     a duplex instruction in pred_packet and a non-duplex in
     succ_packet or vice versa (duplex in succ_packet and
     non-duplex in pred_packet)
     It may make sense to memoize all instructions that can
     be moved from one packet to the other before we get 
     started
  */
  return (false);
}

static int
hexagon_count_duplex_insns(struct hexagon_packet_info *packet)
{
  int i, count = 0;
  for(i = 0; i < packet->num_insns; i++)
    {
      struct hexagon_insn_info *insn = packet->insns[i];
      if (NOTE_P(insn->insn)) 
        {
          continue;
        }
      count += (hexagon_duplex_insn_p (insn));
    }
  return(count);
}

static void 
compute_pipeline_state (struct hexagon_packet_info *packet, bool count_duplexes, 
                             state_t* pipeline_state)
{
  int i;
  for(i = 0; i < packet->num_insns; i++)
    {
      struct hexagon_insn_info *insn = packet->insns[i];
      if (NOTE_P(insn->insn)) 
        {
          continue;
        }

      if (!count_duplexes && hexagon_duplex_insn_p(insn)) {
        continue;
      }
      
      gcc_assert(state_transition(*pipeline_state, insn->insn) < 0);
    }
}

/*
  slot0and1_occupied_p(): Given a packet, predicate that returns true if 
  slot 0 and 1 are both occupied by instructions in that packet 
*/
static bool 
slot0and1_occupied_p(struct hexagon_packet_info *packet, bool count_duplexes)
{
  state_t pipeline_state;
  rtx slot0or1_insn;
  pipeline_state = alloca(state_size());
  state_reset(pipeline_state);

  slot0or1_insn = make_insn_raw(gen_deallocframe());
  INSN_UID(slot0or1_insn) = get_max_uid() + 1;

  compute_pipeline_state (packet, count_duplexes, &pipeline_state);
  return (state_transition(pipeline_state, slot0or1_insn) >= 0);
}


/*
  slot0or1_occupied_p(): Given a packet, predicate that returns true if
  either slot 0 or slot 1 is occupied by instructions in that packet 
*/
static bool 
slot0or1_occupied_p(struct hexagon_packet_info *packet, bool count_duplexes)
{
  state_t pipeline_state;
  rtx slot0or1_insn;
  pipeline_state = alloca(state_size());
  state_reset(pipeline_state);

  slot0or1_insn = make_insn_raw(gen_deallocframe());
  INSN_UID(slot0or1_insn) = get_max_uid() + 1;

  compute_pipeline_state (packet, count_duplexes, &pipeline_state);
  return ((state_transition(pipeline_state, slot0or1_insn) >= 0) ||
          (state_transition(pipeline_state, slot0or1_insn) >= 0));
}


/* 
   hexagon_pack_duplex_insns(): Operates after instructions have been packetized.
   Look for duplex opportunities across packets. Move instructions across 
   packets to create more duplexes. Currently moves instructions between 
   adjacent packets.
*/
static void hexagon_pack_duplex_insns(void)
{
  struct hexagon_packet_info *packet;
  int i;

  packet = hexagon_head_packet; 
  while(packet && packet->next)
        {
          struct hexagon_packet_info *this_packet = packet;
          struct hexagon_packet_info *next_packet = packet->next;
          int duplex_this_packet = hexagon_count_duplex_insns(packet);
          int duplex_next_packet = hexagon_count_duplex_insns(packet->next);
          
          /* Check if neither packet has any duplex instructions */
          if ((this_packet->num_insns == 0) || (next_packet->num_insns == 0))
            {
              packet = packet->next;
              continue;
            }

          /* Only consider moving instructions within the same basic block */
          basic_block this_bb = BLOCK_FOR_INSN(this_packet->insns[0]->insn);
          basic_block next_bb = BLOCK_FOR_INSN(next_packet->insns[0]->insn);
          if (this_bb != next_bb)
            {
              packet = packet->next;
              continue;
            }

          /* 
             Try splitting the packet if:
             The packet contains 4 pairable instructions or
             The packet contains more than 1 pairable instruction and resource
             restrictions prevent the pairing of those duplexes 
          */
          bool split_packet = (duplex_this_packet == 4) || 
            ((duplex_this_packet >= 2) && 
             slot0or1_occupied_p(packet, false /* Don't count duplexes */));

          /* First, try to split the packet */
          if (split_packet) 
            {
              /* Create a new packet and choose instructions to move to that
                 packet */
              struct hexagon_packet_info *new_packet = 
                (struct hexagon_packet_info *)ggc_alloc_cleared(sizeof(struct hexagon_packet_info));
              struct hexagon_insn_info *movable_insns[2];
              int num_movable_insns = 0;

              for (i = 0; (i < this_packet->num_insns) && 
                     (num_movable_insns < 2); ++i)
                {
                  if (hexagon_duplex_insn_p (packet->insns[i]) && 
                      hexagon_move_insn_down_p(packet->insns[i], this_packet, 
                                             new_packet))
                    {
                      movable_insns[num_movable_insns++] = packet->insns[i];
                    }
                }

              /* Can we move at least two instructions to a new packet */
              if (num_movable_insns >= 2)
                {
                  struct hexagon_insn_info *third_insn = movable_insns[0],
                    *fourth_insn = movable_insns[1];
                  
                  /* Splice new packet in between this_packet and next_packet */
                  this_packet->next = new_packet;
                  new_packet->next = next_packet;
                  new_packet->prev = this_packet;
                  next_packet->prev = new_packet;
                  
                  hexagon_move_insn(third_insn, this_packet, third_insn, new_packet, false);
                  hexagon_move_insn(fourth_insn, this_packet, fourth_insn, new_packet, false);
                  packet = new_packet;
                  continue;
                }
            }


          /* Then, try to move instructions between packets. Check for 
             resource restrictions */
          bool open_slot_this_packet = !slot0and1_occupied_p (this_packet, 
                                                              true);
          bool open_slot_next_packet = !slot0and1_occupied_p (next_packet, 
                                                              true);

          /* We try moving instructions from one packet to the next 
             if an issue slot is vacant in at least one of the packets */
          if (open_slot_this_packet || open_slot_next_packet)
            {

              /* Look for unpaired instructions in this and the next packet */
              bool unpaired_this_packet = (duplex_this_packet == 1) || 
                (duplex_this_packet > 2);
              bool unpaired_next_packet = (duplex_next_packet == 1) || 
                (duplex_next_packet > 2);

              /* Then check if there are unpaired duplex instructions in this 
                 packet and the next packet */
              if (unpaired_this_packet && unpaired_next_packet)
                {
                  /* 
                     If there are unpaired instructions in both packets, 
                     try to move a duplex instruction between this_packet and 
                     next_packet (in both directions) to pair the instructions.
                     If there are extra duplexes in one packet, try to move 
                     from that packet to the other 
                  */
                  enum duplex_move_direction dir = UP;
                  bool can_move = false;
                  if ((duplex_this_packet == 1) && (duplex_next_packet == 1))
                    {
                      if (open_slot_this_packet && open_slot_next_packet)
                        {
                          dir = BOTH;
                        }
                      else if (open_slot_this_packet)
                        {
                          dir = UP;
                        }
                      else if (open_slot_next_packet)
                        {
                          dir = DOWN;
                        }
                      can_move = true;
                    }
                  else if ((duplex_this_packet > 2) && 
                           (duplex_next_packet == 1) &&
                           open_slot_next_packet)
                    {
                      dir = DOWN;
                      can_move = true;
                    }
                  else if ((duplex_next_packet > 2) && 
                           (duplex_this_packet == 1) && 
                           open_slot_this_packet) 
                    {
                      dir = UP;
                      can_move = true;
                    }
                  else if ((duplex_next_packet > 2) && 
                           (duplex_this_packet > 2))
                    {
                      /* Not implemented. We must create a new packet in between
                         this_packet and next_packet and attempt to move instructions
                         to the new packet */
                      can_move = false;
                    }

                  if (can_move)
                    {
                      hexagon_pair_duplex_insn(this_packet, next_packet, dir);
                    }
                }
            }
          
          if(!packet->next)
            {
              gcc_assert(packet == BB_END_PACKET (this_bb));
            }
          packet = packet->next;
        }
  
}



/*------------------------------
Functions for fast math
-------------------------------*/
void hexagon_fast_math_libfunc(rtx operand)
{
  if (GET_CODE (XEXP (operand, 0)) == SYMBOL_REF) {
    const char *name = XSTR (XEXP (operand, 0), 0); 
    if (!strncmp (name, "sqrt", strlen(name))){
      rtx sqrt_func = gen_rtx_SYMBOL_REF (Pmode, "fast_sqrt");
      XEXP (operand, 0) = sqrt_func;
    }
    /* gcc's builtin fabs is faster than fast_fabs on floats. So, we do not
       emit fast_fabs */
  }
}


/* Should be at the end of the file */
#include "gt-hexagon.h"
