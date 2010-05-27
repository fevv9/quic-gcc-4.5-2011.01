/*****************************************************************
# Copyright (c) $Date$ Qualcomm Innovation Center, Inc..
# All Rights Reserved.
# Modified by Qualcomm Innovation Center, Inc. on $Date$
*****************************************************************/

 /* QDSP6 specific functions
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
#if !GCC_3_4_6
#include "tree-pass.h"
#endif /* !GCC_3_4_6 */
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





enum qdsp6_architecture qdsp6_arch = QDSP6_ARCH_UNSPECIFIED;
#if GCC_3_4_6
const char * qdsp6_arch_string = QDSP6_ARCH_DEFAULT_STRING;
#endif /* GCC_3_4_6 */
enum qdsp6_abi qdsp6_abi = QDSP6_ABI_UNSPECIFIED;
#if GCC_3_4_6
const char * qdsp6_abi_string = NULL;
const char * qdsp6_oslib_string;
#endif /* GCC_3_4_6 */
int qdsp6_features;
enum qdsp6_falign qdsp6_falign = QDSP6_FALIGN_UNSPECIFIED;
bool qdsp6_dual_memory_accesses = true;




#if !GCC_3_4_6
static bool qdsp6_handle_option(size_t code, const char *arg, int value);
#endif /* !GCC_3_4_6 */

static struct machine_function *qdsp6_init_machine_status(void);

static int qdsp6_array_alignment(tree type, int align);
static bool qdsp6_align_anon_bitfield(void);

#if !GCC_3_4_6
static bool qdsp6_default_short_enums(void);
#endif /* !GCC_3_4_6 */

#if !GCC_3_4_6
static enum reg_class qdsp6_secondary_reload(
                        bool in_p,
                        rtx x,
                        enum reg_class reload_class,
                        enum machine_mode reload_mode,
                        secondary_reload_info *sri);
#endif /* !GCC_3_4_6 */

static bool qdsp6_save_register_p(unsigned int regno);
static void qdsp6_make_prologue_epilogue_decisions(
              struct qdsp6_frame_info *info);
static struct qdsp6_frame_info *qdsp6_frame_info(void);

#if !GCC_3_4_6
static bool qdsp6_must_pass_in_stack(enum machine_mode mode, const_tree type);
#endif /* !GCC_3_4_6 */

#if !GCC_3_4_6
static bool qdsp6_vector_mode_supported_p(enum machine_mode mode);
#endif /* !GCC_3_4_6 */

#if !GCC_3_4_6
static rtx qdsp6_function_value(
             const_tree ret_type,
             const_tree fn_decl_or_type,
             bool outgoing);
#endif /* !GCC_3_4_6 */

static bool qdsp6_return_in_memory(const_tree type, const_tree fntype);
#if GCC_3_4_6
static rtx qdsp6_struct_value_rtx(tree fndecl, int incoming);
#endif /* GCC_3_4_6 */

static void qdsp6_asm_function_prologue(FILE *file, HOST_WIDE_INT size);

static bool qdsp6_function_ok_for_sibcall(tree decl, tree exp);

#if QDSP6_DINKUMWARE
static void qdsp6_init_libfuncs(void);
#endif /* QDSP6_DINKUMWARE */

static bool qdsp6_legit_addr_const_p(
              HOST_WIDE_INT value,
              enum machine_mode mode,
              int num_bits);
#if !GCC_3_4_6
static bool qdsp6_reg_ok_for_base_p(rtx x, bool reg_ok_strict_p);
#endif /* !GCC_3_4_6 */
static bool qdsp6_reg_ok_for_index_p(rtx x, bool reg_ok_strict_p);
#if !GCC_3_4_6
static tree qdsp6_vectorize_builtin_mask_for_load(void);
#endif /* !GCC_3_4_6 */

static bool qdsp6_free_immediate(rtx x, int outer_code, int value);
static bool qdsp6_rtx_costs(
              rtx x,
              int code,
              int outer_code,
              int *total,
              bool speed);
static bool qdsp6_rtx_costs_debug(
              rtx x,
              int code,
              int outer_code,
              int *total,
              bool speed);
static int qdsp6_address_cost(rtx address, bool speed);
static int qdsp6_address_cost_debug(rtx address, bool speed);

static int qdsp6_sched_issue_rate(void);
static void qdsp6_sched_dependencies_eval (rtx, rtx);
#if GCC_3_4_6
static int qdsp6_sched_use_dfa_pipeline_interface(void);
#endif /* GCC_3_4_6 */
static int qdsp6_sched_first_cycle_multipass_dfa_lookahead(void);

#if GCC_3_4_6
static void qdsp6_asm_select_rtx_section(
              enum machine_mode mode,
              rtx x,
              unsigned HOST_WIDE_INT align);
#else /* !GCC_3_4_6 */
static section *qdsp6_asm_select_rtx_section(
                  enum machine_mode mode,
                  rtx x,
                  unsigned HOST_WIDE_INT align);
#endif /* !GCC_3_4_6 */
static section * qdsp6_select_section (tree decl, int reloc, unsigned HOST_WIDE_INT align ATTRIBUTE_UNUSED); 
static bool qdsp6_in_small_data_p(const_tree exp);
static void qdsp6_unique_section (tree decl, int reloc); 
static void qdsp6_elf_asm_named_section (const char *name, unsigned int flags,tree decl ATTRIBUTE_UNUSED); 

static void qdsp6_output_operand(FILE *f, rtx x, int code);

static void qdsp6_fixup_cfg(void);
static void qdsp6_fixup_doloops(void);
static void qdsp6_machine_dependent_reorg(void);
static void qdsp6_local_combine_pass(void);

static void qdsp6_init_builtins(void);
static rtx expand_one_builtin(
             enum insn_code icode,
             rtx target,
             tree exp,
             int nargs);
static rtx qdsp6_expand_builtin(
             tree exp,
             rtx target,
             rtx subtarget,
             enum machine_mode mode,
             int ignore);
static const char *qdsp6_invalid_within_doloop(const_rtx insn);
static void qdsp6_print_jump(FILE *file, rtx x);
static void qdsp6_print_transfer(FILE *file, rtx x);
static void qdsp6_print_condition(FILE *file, rtx x, bool non_inverted);
static void qdsp6_print_address(FILE *file, rtx x);
static void qdsp6_print_unary_op(FILE *file, const char *op, rtx x);
static void qdsp6_print_binary_op(FILE *file, const char *op, rtx x);
static void qdsp6_print_swapped_binary_op(FILE *file, const char *op, rtx x);
static void qdsp6_print_binary_op_with_option(FILE *file, const char *op, const char *option, rtx x);
static void qdsp6_print_trinary_op(FILE *file, const char *op, rtx x);
static void qdsp6_print_vecexp(FILE *file, const char *open, const char *separator, const char *close, rtx x);
static void qdsp6_print_rtx(FILE *file, rtx x);
static void qdsp6_print_rtl_pseudo_asm(FILE *stream, rtx x);

static void qdsp6_compute_dwarf_frame_information(void);
static void qdsp6_allocate_stack(
              unsigned HOST_WIDE_INT size,
              int allocate_stack_insn);
static void qdsp6_deallocate_stack(unsigned HOST_WIDE_INT size);
static tree qdsp6_special_case_memcpy_fn(const char *name);
static void qdsp6_emit_special_case_memcpy_fn(
              tree *fn,
              const char *name,
              rtx dst,
              rtx src,
              rtx size,
              bool tailcall);
static void qdsp6_expand_movmem_inline(rtx operands[], bool volatile_p);

static void qdsp6_packet_optimizations(void);
static void qdsp6_final_pack_insns(void);

static unsigned HOST_WIDE_INT  sdata_symbolic_operand_smallest_accessable_size(rtx);


/* Initialize the GCC target structure. */

/*---------------------------
Run-time Target Specification
---------------------------*/

#if !GCC_3_4_6
#undef TARGET_DEFAULT_TARGET_FLAGS
#define TARGET_DEFAULT_TARGET_FLAGS \
  (MASK_LITERAL_POOL | MASK_LITERAL_POOL_ADDRESSES | MASK_HARDWARE_LOOPS \
   | MASK_DOT_NEW | MASK_BASE_PLUS_INDEX | MASK_MEMOPS | MASK_SECTION_SORTING \
   | MASK_SECTION_SORTING_CODE_SUPPORT)
#endif /* !GCC_3_4_6 */

#if !GCC_3_4_6
#undef TARGET_HANDLE_OPTION
#define TARGET_HANDLE_OPTION qdsp6_handle_option
#endif /* !GCC_3_4_6 */


/*------------
Storage Layout
------------*/

/* Integer arguments and return values should be sign- or zero-extended to a
   full register or register pair before being passed/returned. */
#undef  TARGET_PROMOTE_FUNCTION_MODE
#define TARGET_PROMOTE_FUNCTION_MODE default_promote_function_mode_always_promote

#undef TARGET_ALIGN_ANON_BITFIELD
#define TARGET_ALIGN_ANON_BITFIELD qdsp6_align_anon_bitfield

/*bool TARGET_VECTOR_OPAQUE_P (tree type)*/ /* ??? Should this be true? */


/*----------------------------------
Layout of Source Language Data Types
----------------------------------*/

#if !GCC_3_4_6
#undef TARGET_DEFAULT_SHORT_ENUMS
#define TARGET_DEFAULT_SHORT_ENUMS qdsp6_default_short_enums
#endif /* !GCC_3_4_6 */


/*--------------
Register Classes
--------------*/

#if !GCC_3_4_6
#undef TARGET_SECONDARY_RELOAD
#define TARGET_SECONDARY_RELOAD qdsp6_secondary_reload
#endif /* !GCC_3_4_6 */


/*----------------------------
Passing Arguments in Registers
----------------------------*/

#if !GCC_3_4_6
#undef TARGET_MUST_PASS_IN_STACK
#define TARGET_MUST_PASS_IN_STACK qdsp6_must_pass_in_stack
#endif /* !GCC_3_4_6 */

#if !GCC_3_4_6
#undef TARGET_VECTOR_MODE_SUPPORTED_P
#define TARGET_VECTOR_MODE_SUPPORTED_P qdsp6_vector_mode_supported_p
#endif /* !GCC_3_4_6 */


/*-------------------------------------
How Scalar Function Values Are Returned
-------------------------------------*/

#if !GCC_3_4_6
#undef TARGET_FUNCTION_VALUE
#define TARGET_FUNCTION_VALUE qdsp6_function_value
#endif /* !GCC_3_4_6 */


/*---------------------------
How Large Values Are Returned
---------------------------*/

#undef TARGET_RETURN_IN_MEMORY
#define TARGET_RETURN_IN_MEMORY qdsp6_return_in_memory

#if GCC_3_4_6
#undef TARGET_STRUCT_VALUE_RTX
#define TARGET_STRUCT_VALUE_RTX qdsp6_struct_value_rtx
#endif /* GCC_3_4_6 */


/*---------------------
Function Entry and Exit
---------------------*/

#undef TARGET_ASM_FUNCTION_PROLOGUE
#define TARGET_ASM_FUNCTION_PROLOGUE qdsp6_asm_function_prologue


/*-------------------
Permitting tail calls
-------------------*/

#undef  TARGET_FUNCTION_OK_FOR_SIBCALL
#define TARGET_FUNCTION_OK_FOR_SIBCALL qdsp6_function_ok_for_sibcall


/*-----------------------------
Implementing the Varargs Macros
-----------------------------*/

#undef TARGET_STRICT_ARGUMENT_NAMING
#define TARGET_STRICT_ARGUMENT_NAMING hook_bool_CUMULATIVE_ARGS_true


/*--------------------------------
Implicit Calls to Library Routines
--------------------------------*/

#if QDSP6_DINKUMWARE
#undef TARGET_INIT_LIBFUNCS
#define TARGET_INIT_LIBFUNCS qdsp6_init_libfuncs
#endif /* QDSP6_DINKUMWARE */


/*--------------
Addressing Modes
--------------*/

#if !GCC_3_4_6
#undef TARGET_VECTORIZE_BUILTIN_MASK_FOR_LOAD
#define TARGET_VECTORIZE_BUILTIN_MASK_FOR_LOAD \
  qdsp6_vectorize_builtin_mask_for_load
#endif /* !GCC_3_4_6 */


/*-------------------------------------
Describing Relative Costs of Operations
-------------------------------------*/

#undef TARGET_RTX_COSTS
#define TARGET_RTX_COSTS qdsp6_rtx_costs

#undef TARGET_ADDRESS_COST
#define TARGET_ADDRESS_COST qdsp6_address_cost


/*---------------------------------
Adjusting the Instruction Scheduler
---------------------------------*/

#undef TARGET_SCHED_ISSUE_RATE
#define TARGET_SCHED_ISSUE_RATE qdsp6_sched_issue_rate

#if GCC_3_4_6
#undef TARGET_SCHED_USE_DFA_PIPELINE_INTERFACE
#define TARGET_SCHED_USE_DFA_PIPELINE_INTERFACE \
  qdsp6_sched_use_dfa_pipeline_interface
#endif /* GCC_3_4_6 */

#undef TARGET_SCHED_FIRST_CYCLE_MULTIPASS_DFA_LOOKAHEAD
#define TARGET_SCHED_FIRST_CYCLE_MULTIPASS_DFA_LOOKAHEAD \
  qdsp6_sched_first_cycle_multipass_dfa_lookahead

/*--------------------------------------------------
Dividing the Output into Sections (Texts, Data, ...)
--------------------------------------------------*/

#undef TARGET_ASM_SELECT_RTX_SECTION
#define TARGET_ASM_SELECT_RTX_SECTION qdsp6_asm_select_rtx_section

#undef TARGET_IN_SMALL_DATA_P
#define TARGET_IN_SMALL_DATA_P qdsp6_in_small_data_p

#undef TARGET_ASM_UNIQUE_SECTION
#define TARGET_ASM_UNIQUE_SECTION qdsp6_unique_section // _LSY_ 

#undef TARGET_ASM_SELECT_SECTION
#define TARGET_ASM_SELECT_SECTION qdsp6_select_section // _LSY_ 

#undef TARGET_ASM_NAMED_SECTION
#define TARGET_ASM_NAMED_SECTION  qdsp6_elf_asm_named_section // _LSY_ 

//#undef TARGET_IRA_COVER_CLASSES
//#define TARGET_IRA_COVER_CLASSES qdsp6_ira_cover_classes


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
#define TARGET_MACHINE_DEPENDENT_REORG qdsp6_machine_dependent_reorg

#undef TARGET_INIT_BUILTINS
#define TARGET_INIT_BUILTINS  qdsp6_init_builtins

#undef TARGET_EXPAND_BUILTIN
#define TARGET_EXPAND_BUILTIN qdsp6_expand_builtin

/*tree TARGET_RESOLVE_OVERLOADED_BUILTIN (tree fndecl, tree arglist)*/
/*tree TARGET_FOLD_BUILTIN (tree fndecl, tree arglist, bool ignore)*/

#undef TARGET_INVALID_WITHIN_DOLOOP
#define TARGET_INVALID_WITHIN_DOLOOP qdsp6_invalid_within_doloop

/* ??? Should this be GENERAL_REGS? */
/*int TARGET_BRANCH_TARGET_REGISTER_CLASS (void)*/

#undef TARGET_PRINT_RTL_PSEUDO_ASM
#define TARGET_PRINT_RTL_PSEUDO_ASM qdsp6_print_rtl_pseudo_asm


struct gcc_target targetm = TARGET_INITIALIZER;

static enum section_category	qdsp6_categorize_decl_for_section (const_tree decl, int reloc); 
void default_unique_section_2 (tree decl, int reloc); 
unsigned HOST_WIDE_INT  smallest_accessable_entity_in_declaration(tree decl); 
bool has_this_tree_been_visited(tree node); 
void remember_this_tree(tree node); 
unsigned int descent_smallest(const char *prefix, tree node, unsigned int smallest); 
int qdsp6_named_section_sbss (tree decl, const char *name, int reloc); 
extern section * get_named_section (tree decl, const char *name, int reloc); 
/*---------------------------
Run-time Target Specification
---------------------------*/

static const struct qdsp6_arch_table_entry qdsp6_arch_table[NUM_QDSP6_ARCH] =
  QDSP6_ARCH_TABLE_INITIALIZER;

static const struct qdsp6_abi_table_entry qdsp6_abi_table[NUM_QDSP6_ABI] =
  QDSP6_ABI_TABLE_INITIALIZER;

#if !GCC_3_4_6
/* Implements hook TARGET_HANDLE_OPTION

   Process command-line options such as -march. */

static bool
qdsp6_handle_option(size_t code, const char *arg, int value ATTRIBUTE_UNUSED)
{
  int i;

  switch(code){
    case OPT_march_:
    case OPT_mcpu_:
      for(i = 0; i < NUM_QDSP6_ARCH; i++){
        if(strcmp(arg, qdsp6_arch_table[i].name) == 0){
          qdsp6_arch = qdsp6_arch_table[i].arch;
          qdsp6_features = qdsp6_arch_table[i].features;
          return true;
        }
      }
      error("bad value (%s) for -m%s= option",
            arg, code == OPT_march_ ? "arch" : "cpu");
      return false;
    case OPT_mabi_:
      for(i = 0; i < NUM_QDSP6_ABI; i++){
        if(strcmp(arg, qdsp6_abi_table[i].name) == 0){
          qdsp6_abi = qdsp6_abi_table[i].abi;
          return true;
        }
      }
      error("bad value (%s) for -mabi= option", arg);
      return false;
    case OPT_mno_falign:
      qdsp6_falign = QDSP6_NO_FALIGN;
      return true;
    case OPT_mfalign_loops:
      qdsp6_falign = QDSP6_FALIGN_LOOPS;
      return true;
    case OPT_mfalign_labels:
      qdsp6_falign = QDSP6_FALIGN_LABELS;
      return true;
  }
  return true;
}
#endif /* !GCC_3_4_6 */




/* Implements macro OVERRIDE_OPTIONS

   Make any necessary final decisions about command-line options. */

void
qdsp6_override_options(void)
{
  int arch_index;
  int abi_index;

#if GCC_3_4_6
  for(arch_index = 0; arch_index < NUM_QDSP6_ARCH; arch_index++){
    if(strcmp(qdsp6_arch_string, qdsp6_arch_table[arch_index].name) == 0){
      qdsp6_arch = qdsp6_arch_table[arch_index].arch;
      qdsp6_features = qdsp6_arch_table[arch_index].features;
      break;
    }
  }
  if(arch_index == NUM_QDSP6_ARCH){
    error("bad value (%s) for -march= option", qdsp6_arch_string);
  }
#else /* !GCC_3_4_6 */
  if(qdsp6_arch == QDSP6_ARCH_UNSPECIFIED){
    arch_index = QDSP6_ARCH_TABLE_DEFAULT_INDEX;
    qdsp6_arch = qdsp6_arch_table[arch_index].arch;
    qdsp6_features = qdsp6_arch_table[arch_index].features;
  }
#endif /* !GCC_3_4_6 */

  if(qdsp6_arch == QDSP6_ARCH_V1){
    error("Architecture qdsp6v1 is no longer supported.");
  }

#if GCC_3_4_6
  if(qdsp6_abi_string != NULL){
    for(abi_index = 0; abi_index < NUM_QDSP6_ABI; abi_index++){
      if(strcmp(qdsp6_abi_string, qdsp6_abi_table[abi_index].name) == 0){
        qdsp6_abi = qdsp6_abi_table[abi_index].abi;
        break;
      }
    }
    if(abi_index == NUM_QDSP6_ABI){
      error("bad value (%s) for -mabi= option", qdsp6_abi_string);
    }
  }
#endif /* GCC_3_4_6 */
  if(qdsp6_abi == QDSP6_ABI_UNSPECIFIED){
    abi_index = QDSP6_ABI_TABLE_DEFAULT_INDEX;
    qdsp6_abi = qdsp6_abi_table[abi_index].abi;
  }

#if GCC_3_4_6
  if(TARGET_NO_FALIGN){
    qdsp6_falign = QDSP6_NO_FALIGN;
  }
  else if(TARGET_FALIGN_LOOPS){
    qdsp6_falign = QDSP6_FALIGN_LOOPS;
  }
  else if(TARGET_FALIGN_LABELS){
    qdsp6_falign = QDSP6_FALIGN_LABELS;
  }
#endif /* GCC_3_4_6 */

  if(TARGET_UNCACHED_DATA){
    if(qdsp6_arch == QDSP6_ARCH_V1 || qdsp6_arch == QDSP6_ARCH_V2){
      qdsp6_dual_memory_accesses = false;
    }
    else {
#if GCC_3_4_6
      warning("Ignoring the -mv1-v2-uncached-data option as it is only valid for V1 an V2.");
#else /* !GCC_3_4_6 */
      warning(0, "Ignoring the -mv1-v2-uncached-data option as it is only valid for V1 an V2.");
#endif /* !GCC_3_4_6 */
    }
  }

  if(!g_switch_set){
    g_switch_value = 2 * UNITS_PER_WORD;
  }

  if(TARGET_COMPRESSED){
    flag_schedule_insns = 0;
    flag_schedule_insns_after_reload = 0;
    target_flags &= ~MASK_PACKETS;
  }

  if(!TARGET_PACKETS){
    target_flags &= ~MASK_PULLUP;
  }

  /* Align functions to 16-byte boundaries to prevent
     target-packet-crosses-16-byte-boundary (falign) stalls. */
  if(align_functions == 0){
    align_functions = 16;
  }

#if GCC_3_4_6
  /* In GCC 3.4.6, when unswitching hardware loops, GCC does not duplicate the
     loop setup instruction. */
  flag_unswitch_loops = 0;
#endif /* GCC_3_4_6 */
}




/* Implements macro OPTIMIZATION_OPTIONS

   Set defaults for flags based on optimization level. */

void
qdsp6_optimization_options(int level, int size)
{
  if(level >= 2){
    target_flags |= MASK_PACKETS;
    target_flags |= MASK_PULLUP;
    flag_optimize_memset = 1;
  }

  qdsp6_falign = QDSP6_NO_FALIGN;

  if (level >= 1)
    {
      target_flags |= MASK_PRED_MUX;
    }

  if(size){
    target_flags |= MASK_EXTENDED_CROSSJUMPING; 
    target_flags |= MASK_LOCAL_COMBINE;
  }

  if(level >= 3 && !size){
    qdsp6_falign = QDSP6_FALIGN_LABELS;
  }
  else if(level >= 1 && !size){
    qdsp6_falign = QDSP6_FALIGN_LOOPS;
  }

#if GCC_3_4_6
  if(level >= 2){
    flag_reduce_all_givs = 1;
    flag_sched2_use_superblocks = 1;
  }
#endif /* GCC_3_4_6 */
}




/*---------------------------------------------------
Defining data structures for per-function information
---------------------------------------------------*/

/* Implements macro INIT_EXPANDERS */

void
qdsp6_init_expanders(void)
{
  init_machine_status = qdsp6_init_machine_status;
}




/* initializes the machine specific per-function data */

static struct machine_function *
qdsp6_init_machine_status(void)
{
  struct machine_function *mf;
  mf = ggc_alloc_cleared(sizeof(struct machine_function));
  return mf;
}




/*------------
Storage Layout
------------*/

/* Return the TYPE of the elements comprising
   the innermost dimension of ARRAY.  */

tree
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
qdsp6_array_alignment(tree type, int align)
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
qdsp6_data_alignment(tree type, int align)
{
  if(TREE_CODE (type) == ARRAY_TYPE){
    return qdsp6_array_alignment(type, align);
  }

  return align;
}




/* Implements macro CONSTANT_ALIGNMENT

   Doubleword align constant strings. */

int
qdsp6_constant_alignment(tree constant, int align)
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

int
qdsp6_local_alignment(tree type, int align)
{
  if(TREE_CODE (type) == ARRAY_TYPE){
    return qdsp6_array_alignment(type, align);
  }

  return align;
}




/* Implements hook TARGET_ALIGN_ANON_BITFIELD

   Unnamed (anonymous) bitfields affect alignment and padding the same way named
   bitfields do. */

static bool
qdsp6_align_anon_bitfield(void)
{
  return true;
}




/*----------------------------------
Layout of Source Language Data Types
----------------------------------*/

#if !GCC_3_4_6
/* Implements hook TARGET_DEFAULT_SHORT_ENUMS

   The default ABI specifies that enumerated types behave like the smallest
   integer type that can hold all of the enumerated constants associated with
   the enumerated type.  Linux requires its ABI to specify non-short enums. */

static bool
qdsp6_default_short_enums(void)
{
  return qdsp6_abi != QDSP6_ABI_LINUX;
}
#endif /* !GCC_3_4_6 */




/*--------------------------------
Basic Characteristics of Registers
--------------------------------*/

/* Implements macro CONDITIONAL_REGISTER_USAGE

   QDSP6 ABI 2 increases the number of callee save registers from 4 to 12. */

void
qdsp6_conditional_register_usage(void)
{
  int i;
  if(qdsp6_abi != QDSP6_ABI_1){
    for(i = 16; i < 24; i++){
      if(!fixed_regs[i]){
        call_used_regs[i] = 0;
      }
    }
  }
}




/*--------------
Register Classes
--------------*/

/* Implements macro CANNOT_CHANGE_MODE_CLASS

   Prevent predicates from being represented as QImode SUBREGs of SImode. */

bool
qdsp6_cannot_change_mode_class(
  enum machine_mode from,
  enum machine_mode to,
  enum reg_class rclass
)
{
  if(from == to){
    return false;
  }

  if((   rclass == PREDICATE_DOT_OLD_REGS
      || rclass == PREDICATE_DOT_NEW_REGS
      || rclass == PREDICATE_REGS)
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

   K16 means 16
   K32 means 32
   Ku7p1 integers in [1, 128]
   Ks8p1 integers in [-127, 128]
   Ku9p1 integers in [1, 512]
   Ks10p1 integers in [-511, 512]
   Ks8s8 means integers that can be formed using combine(#s8,#s8)
   Konehot32 means power of 2 integers that can be represented in 32 bits
   Konenot32 means one's complements of Konehot32 constants */

bool
qdsp6_const_ok_for_constraint_p(HOST_WIDE_INT value, char c, const char *str)
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
      if(QDSP6_CONSTRAINT_P(str, 16)){
        return value == 16;
      }
      else if(QDSP6_CONSTRAINT_P(str, 32)){
        return value == 32;
      }
      else if(QDSP6_CONSTRAINT_P(str, u7p1)){
        return IN_RANGE (value, 1, 128);
      }
      else if(QDSP6_CONSTRAINT_P(str, s8p1)){
        return IN_RANGE (value, -127, 128);
      }
      else if(QDSP6_CONSTRAINT_P(str, u9p1)){
        return IN_RANGE (value, 1, 512);
      }
      else if(QDSP6_CONSTRAINT_P(str, s10p1)){
        return IN_RANGE (value, -511, 512);
      }
      else if(QDSP6_CONSTRAINT_P(str, s8s8)){
        high = value >> 32ULL;
        low = value & 0xFFFFFFFFULL;
        return ((high & 0xFFFFFF00) == (high & 0x80 ? 0xFFFFFF00 : 0))
            && ((low  & 0xFFFFFF00) == (low  & 0x80 ? 0xFFFFFF00 : 0));
      }
      else if(QDSP6_CONSTRAINT_P(str, onehot32)){
        value &= 0xFFFFFFFFULL;
        return value == (value & -value);
      }
      else if(QDSP6_CONSTRAINT_P(str, onenot32)){
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

#if GCC_3_4_6
enum reg_class
qdsp6_secondary_reload_class(
  rtx x,
  enum reg_class reload_class
)
#else /* !GCC_3_4_6 */
static enum reg_class
qdsp6_secondary_reload(
  bool in_p ATTRIBUTE_UNUSED,
  rtx x,
  enum reg_class reload_class,
  enum machine_mode reload_mode ATTRIBUTE_UNUSED,
  secondary_reload_info *sri ATTRIBUTE_UNUSED
)
#endif /* !GCC_3_4_6 */
{
  switch(reload_class){
    case PREDICATE_DOT_OLD_REGS:
    case PREDICATE_DOT_NEW_REGS:
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
qdsp6_return_addr_rtx(int count, rtx frame)
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

/* QDSP6 stack frames look like:

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
qdsp6_save_register_p(unsigned int regno)
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

#define QDSP6_BIGGEST_ALIGN(SIZE) \
  (((SIZE) + BIGGEST_ALIGNMENT / 8 - 1) & ~(BIGGEST_ALIGNMENT / 8 - 1))

/* Helper function for qdsp6_frame_info

   Make all of the decisions about how to generate the prologue and epilogue. */

static void
qdsp6_make_prologue_epilogue_decisions(struct qdsp6_frame_info *info)
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
  if(qdsp6_abi == QDSP6_ABI_2){
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
    if(!TARGET_COMPRESSED && info->frame_size <= 256){
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
  if((use_common_functions || (optimize && TARGET_PACKETS))
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
  if(optimize && TARGET_PACKETS
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

static struct qdsp6_frame_info *
qdsp6_frame_info(void)
{
  struct qdsp6_frame_info *info;
  unsigned int regno;

  info = &cfun->machine->frame_info;

  if(info->computed){
    return info;
  }

  /* Space for outgoing arguments */
  info->args_size = QDSP6_BIGGEST_ALIGN (crtl->outgoing_args_size);

  /* Space for local variables, temporaries, and spills */
  info->var_size = QDSP6_BIGGEST_ALIGN (get_frame_size());

  /* Space needed for callee-save registers */
  info->num_saved_pairs = 0;
  info->num_saved_singles = 0;
  for(regno = 0; regno < FIRST_PSEUDO_REGISTER; regno += 2){
    if(qdsp6_save_register_p(regno)){
      if(qdsp6_save_register_p(regno + 1)){
        info->saved_pairs[info->num_saved_pairs++] = regno;
      }
      else {
        info->saved_singles[info->num_saved_singles++] = regno;
      }
    }
    else if(qdsp6_save_register_p(regno + 1)){
      info->saved_singles[info->num_saved_singles++] = regno + 1;
    }
  }
  info->reg_size = 2 * UNITS_PER_WORD * info->num_saved_pairs
                   + UNITS_PER_WORD * info->num_saved_singles;
  info->reg_size = QDSP6_BIGGEST_ALIGN (info->reg_size);

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
    qdsp6_make_prologue_epilogue_decisions(info);
  }

  info->computed = reload_completed != 0;

  gcc_assert(info->frame_size % 8 == 0);

  return info;
}




/* Implements macro INITIAL_ELIMINATION_OFFSET

   Returns the number of bytes offset between FROM_REG and TO_REG
   for the current function. */

HOST_WIDE_INT
qdsp6_initial_elimination_offset(int from_reg, int to_reg)
{
  struct qdsp6_frame_info *frame;

  frame = qdsp6_frame_info();

  if(      from_reg == ARG_POINTER_REGNUM
          && to_reg == STACK_POINTER_REGNUM){
    return frame->total_size;
  }
  else if( from_reg == FRAME_POINTER_REGNUM
          && to_reg == STACK_POINTER_REGNUM){
    return frame->args_size;
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
    return -(frame->reg_size + frame->var_size);
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
qdsp6_function_arg(
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

  if(qdsp6_must_pass_in_stack(mode, type)){
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

  if(cum >= QDSP6_NUM_ARG_REGS){
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

#if GCC_3_4_6
bool
#else /* !GCC_3_4_6 */
static bool
#endif /* !GCC_3_4_6 */
qdsp6_must_pass_in_stack(enum machine_mode mode ATTRIBUTE_UNUSED, const_tree type)
{
  return type && TYPE_SIZE (type)
         && (TREE_CODE (TYPE_SIZE (type)) != INTEGER_CST
             || TREE_ADDRESSABLE (type)
             || int_size_in_bytes(type) > 8);
}




/* Implements macro FUNCTION_ARG_ADVANCE

   Advance the cumulative arg pointer past the current argument. */

int
qdsp6_function_arg_advance(
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

  if(qdsp6_must_pass_in_stack(mode, type)){
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




#if !GCC_3_4_6
/* Implements hook TARGET_VECTOR_MODE_SUPPORTED_P */

static bool
qdsp6_vector_mode_supported_p(enum machine_mode mode)
{
  return    mode == V2SImode
         || mode == V4HImode
         || mode == V8QImode
         || mode == V2HImode
         || mode == V4QImode;
}
#endif /* !GCC_3_4_6 */




/*-------------------------------------
How Scalar Function Values Are Returned
-------------------------------------*/

/* Implements hook TARGET_FUNCTION_VALUE */

#if GCC_3_4_6
rtx
#else /* !GCC_3_4_6 */
static rtx
#endif /* !GCC_3_4_6 */
qdsp6_function_value(
  const_tree ret_type,
  const_tree func,
  bool outgoing ATTRIBUTE_UNUSED
)
{
  enum machine_mode mode;
  int unsignedp ATTRIBUTE_UNUSED;

  mode = TYPE_MODE (ret_type);
  mode = promote_function_mode(ret_type, mode, &unsignedp, func, 1);
  return gen_rtx_REG (mode, RETURN_VALUE_REGNUM);
}




/*---------------------------
How Large Values Are Returned
---------------------------*/

/* Implements hook TARGET_RETURN_IN_MEMORY

   Return true if function return value returned in memory.
   Return false if it is in a register. */

static bool
qdsp6_return_in_memory(const_tree type, const_tree fntype ATTRIBUTE_UNUSED)
{
  enum machine_mode mode;
  HOST_WIDE_INT byte_size;

  mode = TYPE_MODE (type);
  byte_size = GET_MODE_SIZE (mode);
  if(mode == BLKmode){
    byte_size = int_size_in_bytes(type);
  }

  return !IN_RANGE (byte_size, 0, 2 * UNITS_PER_WORD);
}




#if GCC_3_4_6
/* Implements hook TARGET_STRUCT_VALUE_RTX

   If a function returns a struct that does not fit in a register, then the
   address where the struct should be stored should be passed to the function
   as if it were the first argument. */

static rtx
qdsp6_struct_value_rtx(
  tree fndecl ATTRIBUTE_UNUSED,
  int incoming ATTRIBUTE_UNUSED
)
{
  return NULL_RTX;
}
#endif /* GCC_3_4_6 */




/*---------------------
Function Entry and Exit
---------------------*/

/* Implements hook TARGET_ASM_FUNCTION_PROLOGUE */

static void
qdsp6_asm_function_prologue(
  FILE *file,
  HOST_WIDE_INT size ATTRIBUTE_UNUSED
)
{
  struct qdsp6_frame_info *frame;
  frame = qdsp6_frame_info();
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

  qdsp6_final_pack_insns();

  qdsp6_compute_dwarf_frame_information();
}




/*-------------------
Permitting tail calls
-------------------*/

/* Implements hook TARGET_FUNCTION_OK_FOR_SIBCALL */

static bool
qdsp6_function_ok_for_sibcall(tree decl, tree exp ATTRIBUTE_UNUSED)
{
  if(TARGET_LONG_CALLS){
    return false;
  }
  return decl != NULL;
}




/*--------------------------------
Implicit Calls to Library Routines
--------------------------------*/

#if QDSP6_DINKUMWARE
/* Implements hook TARGET_INIT_LIBFUNCS */

static void
qdsp6_init_libfuncs(void)
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

  set_optab_libfunc(add_optab, SFmode, "__qdsp_addsf3");
  set_optab_libfunc(add_optab, DFmode, "__qdsp_adddf3");

  set_optab_libfunc(sub_optab, SFmode, "__qdsp_subsf3");
  set_optab_libfunc(sub_optab, DFmode, "__qdsp_subdf3");

  set_optab_libfunc(smul_optab, SFmode, "__qdsp_mulsf3");
  set_optab_libfunc(smul_optab, DFmode, "__qdsp_muldf3");

  set_optab_libfunc(sdiv_optab, SFmode, "__qdsp_divsf3");
  set_optab_libfunc(sdiv_optab, DFmode, "__qdsp_divdf3");

  set_optab_libfunc(neg_optab, SFmode, "__qdsp_negsf3");
  set_optab_libfunc(neg_optab, DFmode, "__qdsp_negdf3");

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

  set_optab_libfunc(lt_optab, SFmode, "__qdsp_ltsf2");
  set_optab_libfunc(lt_optab, DFmode, "__qdsp_ltdf2");

  set_optab_libfunc(le_optab, SFmode, "__qdsp_lesf2");
  set_optab_libfunc(le_optab, DFmode, "__qdsp_ledf2");

  set_optab_libfunc(gt_optab, SFmode, "__qdsp_gtsf2");
  set_optab_libfunc(gt_optab, DFmode, "__qdsp_gtdf2");

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

#if !GCC_3_4_6
  set_conv_libfunc(ufloat_optab, SFmode, SImode, "__qdsp_floatunsisf");
  set_conv_libfunc(ufloat_optab, SFmode, DImode, "__qdsp_floatundisf");

  set_conv_libfunc(ufloat_optab, DFmode, SImode, "__qdsp_floatunsidf");
  set_conv_libfunc(ufloat_optab, DFmode, DImode, "__qdsp_floatundidf");
#endif /* !GCC_3_4_6 */
}
#endif /* QDSP6_DINKUMWARE */




/*--------------
Addressing Modes
--------------*/

/* Helper for qdsp6_legitimate_address_p

   Determine if the constant fits in the encoding
     - Check the range based on the number of bits and signedness
     - Check that the "scaling" bits are zero */

static bool
qdsp6_legit_addr_const_p(
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




#if GCC_3_4_6
/* Implements macro REG_OK_FOR_BASE_P */

bool
#else /* !GCC_3_4_6 */
/* Helper function for qdsp6_legitimate_address_p */

static bool
#endif /* !GCC_3_4_6 */
qdsp6_reg_ok_for_base_p(rtx x, bool reg_ok_strict_p)
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




/* Helper function for qdsp6_legitimate_address_p */

static bool
qdsp6_reg_ok_for_index_p(rtx x, bool reg_ok_strict_p)
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
   noext   basic loads and stores
   cond    conditional loads and stores
   econd   conditional loads and stores, allowing an immediate extender
   si      store immediate
   csi     conditional store immediate
   memop   load-op-stores
   ememop  load-op-stores, allowing an immediate extender */

bool
qdsp6_legitimate_address_p(
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

  if(!strcmp(constraint, "m") || !strcmp(constraint, "noext")){
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
    return qdsp6_reg_ok_for_base_p(x, reg_ok_strict_p);
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
     && ((REG_P (xop0) && qdsp6_reg_ok_for_base_p(xop0, reg_ok_strict_p))
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
      return qdsp6_legit_addr_const_p(INTVAL (offset), mode, offset_bits);
    }

    /* base+index address */
    if(allow_base_plus_index){
      if(REG_P (offset)){
        return qdsp6_reg_ok_for_base_p(offset, reg_ok_strict_p);
      }
      if(GET_CODE (offset) == MULT){
        return    REG_P (index)
               && qdsp6_reg_ok_for_index_p(index, reg_ok_strict_p)
               && GET_CODE (scale) == CONST_INT
               && (   INTVAL (scale) == 1
                   || INTVAL (scale) == 2
                   || INTVAL (scale) == 4
                   || INTVAL (scale) == 8);
      }
      if(GET_CODE (offset) == ASHIFT){
        return    REG_P (index)
               && qdsp6_reg_ok_for_index_p(index, reg_ok_strict_p)
               && GET_CODE (scale) == CONST_INT
               && IN_RANGE (INTVAL (scale), 0, 3);
      }
    }
  }

  if(allow_post_inc){
    /* post increment/decrement address with the increment/decrement equal to
       the access size */
    if(GET_CODE (x) == POST_INC || GET_CODE (x) == POST_DEC){
      return REG_P (xop0) && qdsp6_reg_ok_for_base_p(xop0, reg_ok_strict_p);
    }

    /* post increment/decrement address */
    if(GET_CODE (x) == POST_MODIFY){
      return    REG_P (xop0)
             && qdsp6_reg_ok_for_base_p(xop0, reg_ok_strict_p)
             && GET_CODE (xop1) == PLUS
             && REG_P (xop1op0)
             && REGNO (xop1op0) == REGNO (xop0)
             && GET_CODE (xop1op1) == CONST_INT
             && qdsp6_legit_addr_const_p(INTVAL (xop1op1), mode, -4);
    }
  }

  return false;
}




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

  string = alloca (nlen + plen + 1);
  memcpy (string, prefix, plen);
  memcpy (string + plen, name, nlen + 1);

  DECL_SECTION_NAME (decl) = build_string (nlen + plen, string);
}




static void
qdsp6_unique_section (tree decl, int reloc)
{
  default_unique_section_2 (decl, reloc);
}




/* _LSY_ Loks for smallest addressable entity in
   a declaration, not overall declaration size. */  
static unsigned HOST_WIDE_INT 
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
        if(!SYMBOL_REF_SMALL_P (op))    size;
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




/* copy of general_operand() rtl predicate plus memory sorting */  
int
qdsp6_GP_or_reg_operand_c (rtx op, enum machine_mode mode)
{
  enum rtx_code code = GET_CODE (op);
  
  if (mode == VOIDmode)	mode = GET_MODE (op);  

  /* Don't accept CONST_INT or anything similar
     if the caller wants something floating.  */
  if (GET_MODE (op) == VOIDmode && mode != VOIDmode
      && GET_MODE_CLASS (mode) != MODE_INT
      && GET_MODE_CLASS (mode) != MODE_PARTIAL_INT)
    return 0;

  if (GET_CODE (op) == CONST_INT
      && mode != VOIDmode
      && trunc_int_for_mode (INTVAL (op), mode) != INTVAL (op))
    return 0;

  if (CONSTANT_P (op)){
    return ((GET_MODE (op) == VOIDmode || GET_MODE (op) == mode
             || mode == VOIDmode)
            && (! flag_pic || LEGITIMATE_PIC_OPERAND_P (op))
            && LEGITIMATE_CONSTANT_P (op));
   }

  /* Except for certain constants with VOIDmode, already checked for,
     OP's mode must match MODE if MODE specifies a mode.  */
  if (GET_MODE (op) != mode)	return 0; 

  if (code == SUBREG){ 
      rtx sub = SUBREG_REG (op);

#ifdef INSN_SCHEDULING
      /* On machines that have insn scheduling, we want all memory
	 reference to be explicit, so outlaw paradoxical SUBREGs.
	 However, we must allow them after reload so that they can
	 get cleaned up by cleanup_subreg_operands.  */
      if (!reload_completed && MEM_P (sub)
	  && GET_MODE_SIZE (mode) > GET_MODE_SIZE (GET_MODE (sub)))
	return 0;
#endif
      /* Avoid memories with nonzero SUBREG_BYTE, as offsetting the memory
         may result in incorrect reference.  We should simplify all valid
         subregs of MEM anyway.  But allow this after reload because we
         might be called from cleanup_subreg_operands.
         ??? This is a kludge.  */
      if (!reload_completed && SUBREG_BYTE (op) != 0 && MEM_P (sub))	
        return 0;

      /* FLOAT_MODE subregs can't be paradoxical.  Combine will occasionally
         create such rtl, and we must reject it.  */
      if (SCALAR_FLOAT_MODE_P (GET_MODE (op))
	  && GET_MODE_SIZE (GET_MODE (op)) > GET_MODE_SIZE (GET_MODE (sub)))
	return 0;

      op = sub;
      code = GET_CODE (op);
    }
  if (code == REG) 
    /* A register whose class is NO_REGS is not a general operand.  */
    return (REGNO (op) >= FIRST_PSEUDO_REGISTER
            || REGNO_REG_CLASS (REGNO (op)) != NO_REGS);

  if (code == MEM){ 
      rtx y = XEXP (op, 0);

      if (! volatile_ok && MEM_VOLATILE_P (op))	return 0; 
      /* _LSY_ if (GET_CODE (y) == ADDRESSOF)		return 1; */  

      /* Use the mem's mode, since it will be reloaded thus.  */
      mode = GET_MODE (op);

      /* Catch GP relative MEM accesses */  
      if(sdata_symbolic_operand(y, Pmode)){
    	/* Will be GP relative */
	unsigned HOST_WIDE_INT mem_size = 0; 

	if((GET_CODE (op) == MEM) && MEM_SIZE (op))	
		mem_size = INTVAL (MEM_SIZE (op)); 
	/* Dev warning. if(GET_MODE_SIZE(mode) != mem_size)	
           fprintf(stderr,"Warning. GET_MODE_SIZE(%d) != mem_size(%d)\n",
	   GET_MODE_SIZE(mode),mem_size); 
        */

	/* This makes this predicate to reject GP relative 
	   addressing if access unit is smaller than declaration unit*/ 
	if(TARGET_SECTION_SORTING_CODE_SUPPORT 
	&& TARGET_SECTION_SORTING 
	/* There is a difference in approach possible here: In case of a struct
           we can consider overal struct size as grounds for rejection, on the other
           hand we can see what is the smallest accessable member of the struct is, and 
           use that instead. Currently it makes no significant difference in performance
           or size, but we can easily think of a theoretical example where it might.
           Alternative code:
           mem_size < sdata_symbolic_operand_size(y)
        */
	&& (mem_size < sdata_symbolic_operand_smallest_accessable_size(y))){ 
	   if(reload_completed)	; /* Dev warning. fprintf(stderr,
                                     "Warning. Skip late section sorting match\n"); */ 
	   else	return 0;
	}
      }
      if (memory_address_p (mode, y))	return 1;
   }
  return 0;
}




int
qdsp6_nonimmediate_operand_with_GP_c (rtx op, enum machine_mode mode)
{
  return (! CONSTANT_P (op) && GP_or_reg_operand (op, mode));
}




static GTY(()) tree qdsp6_builtin_mask_for_load;

#if !GCC_3_4_6
/* Implements hook TARGET_VECTORIZE_BUILTIN_MASK_FOR_LOAD */

static tree
qdsp6_vectorize_builtin_mask_for_load(void)
{
  return qdsp6_builtin_mask_for_load;
}
#endif /* !GCC_3_4_6 */




/*-------------------------------------
Describing Relative Costs of Operations
-------------------------------------*/

/* Implements hook STORE_BY_PIECES_P */

bool
qdsp6_store_by_pieces_p(unsigned HOST_WIDE_INT size, unsigned int alignment)
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




/* Helper function for qdsp6_rtx_costs */

static bool
qdsp6_free_immediate(rtx x, int outer_code, int value)
{
  return true;
}




/* Implements hook TARGET_RTX_COSTS */

static bool
qdsp6_rtx_costs(rtx x, int code, int outer_code, int *total, bool speed)
{
  enum machine_mode mode = GET_MODE (x);

  switch(code){
    case CONST_INT:
      if(qdsp6_free_immediate(x,outer_code,INTVAL(x))){
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
      else if(TARGET_V2_FEATURES
              && (outer_code == PLUS || outer_code == MINUS)){
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
      *total = COSTS_N_INSNS(1);
      return false;

    case FFS:
      *total = TARGET_V2_FEATURES ? COSTS_N_INSNS (1) : COSTS_N_INSNS (10);
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




static bool
qdsp6_rtx_costs_debug(rtx x, int code, int outer_code, int *total, bool speed)
{
  bool retval;

  debug_rtx(x);
  retval = qdsp6_rtx_costs(x, code, outer_code, total, speed);
  fprintf(stderr, "rtx_cost:  %d, %s\n\n", *total, retval ? "true" : "false");

  return retval;
}




/* Implements hook TARGET_ADDRESS_COST */

static int
qdsp6_address_cost(rtx address, bool speed)
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




static int
qdsp6_address_cost_debug(rtx address, bool speed)
{
  int retval;

  debug_rtx(address);
  retval = qdsp6_address_cost(address, speed);
  fprintf(stderr, "address_cost:  %d\n\n", retval);

  return retval;
}




/*---------------------------------
Adjusting the Instruction Scheduler
---------------------------------*/

/* Implements hook TARGET_SCHED_ISSUE_RATE */

static int
qdsp6_sched_issue_rate(void)
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


#if GCC_3_4_6
/* Implements hook TARGET_SCHED_USE_DFA_PIPELINE_INTERFACE

   Yes, please actually use the automaton description
   in the machine description for scheduling.  Thank you. */

static int
qdsp6_sched_use_dfa_pipeline_interface(void)
{
  return 1;
}
#endif /* GCC_3_4_6 */




/* Implements hook TARGET_SCHED_FIRST_CYCLE_MULTIPASS_DFA_LOOKAHEAD */

static int
qdsp6_sched_first_cycle_multipass_dfa_lookahead(void)
{
  return 8; /* ??? dunno */
}




/*--------------------------------------------------
Dividing the Output into Sections (Texts, Data, ...)
--------------------------------------------------*/

/* Implements hook TARGET_ASM_SELECT_RTX_SECTION */

#if GCC_3_4_6
static void
qdsp6_asm_select_rtx_section(
  enum machine_mode mode,
  rtx x,
  unsigned HOST_WIDE_INT align
)
{
  if(GET_MODE_SIZE (mode) > 0 && GET_MODE_SIZE (mode) <= g_switch_value){
    named_section(NULL_TREE, ".sdata", 0);
  }
  else {
    default_elf_select_rtx_section(mode, x, align);
  }
}
#else /* !GCC_3_4_6 */
static section *
qdsp6_asm_select_rtx_section(
  enum machine_mode mode,
  rtx x,
  unsigned HOST_WIDE_INT align
)
{
  if(GET_MODE_SIZE (mode) > 0 && GET_MODE_SIZE (mode) <= g_switch_value){
    return sdata_section;
  }
  else {
    return default_elf_select_rtx_section(mode, x, align);
  }
}
#endif /* !GCC_3_4_6 */




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
descent_smallest(const char *prefix, tree node, unsigned int smallest){
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
qdsp6_categorize_decl_for_section (const_tree decl, int reloc)
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
qdsp6_select_section (tree decl, int reloc,
                        unsigned HOST_WIDE_INT align)
{
  const char *sname;

  switch (qdsp6_categorize_decl_for_section (decl, reloc)){ 
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
qdsp6_elf_asm_named_section (const char *name, unsigned int flags,
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
    }

  putc ('\n', asm_out_file);
  
  /* _LSY_ Also put subsection for better sorting */ 
  if(TARGET_SECTION_SORTING && decl && (smallest_accessable_entity_in_declaration(decl) > 1))
     fprintf (asm_out_file, "\t.subsection\t-%d\n",floor_log2(smallest_accessable_entity_in_declaration(decl)));
}




/* Implements hook TARGET_IN_SMALL_DATA_P */

static bool
qdsp6_in_small_data_p(const_tree exp)
{
  /* GP relative addressing is a V2 feature. */
  if(!TARGET_V2_FEATURES){
    return false;
  }

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
qdsp6_asm_output_aligned_decl_common(
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
qdsp6_asm_output_aligned_decl_local(
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

/* Helper function for qdsp6_asm_output_opcode */

static void
qdsp6_output_operand(FILE *f, rtx x, int code ATTRIBUTE_UNUSED)
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
qdsp6_asm_output_opcode(FILE *f, const char *ptr)
{
  struct qdsp6_final_info *final_info;
  int c;
  int oporder[MAX_RECOG_OPERANDS];
  char opoutput[MAX_RECOG_OPERANDS];
  int ops = 0;

  if(!(TARGET_PACKETS && optimize)){
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
           Other letters are passed to `qdsp6_output_operand' so that
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
              qdsp6_output_operand(f, final_info->insn_ops[opnum], 'c');
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
            qdsp6_output_operand(f, final_info->insn_ops[opnum], letter);
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
          qdsp6_output_operand(f, final_info->insn_ops[opnum], 0);

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

  return ptr;
}




/* Implements macro FINAL_PRESCAN_INSN

   Looks at the current and next insns to determine how to format the next insn
   to be printed and whether or not to print open or close curly brackets in
   order to begin or end a packet. */

void
qdsp6_final_prescan_insn(
  rtx insn,
  rtx *ops,
  int numops ATTRIBUTE_UNUSED
)
{
  struct qdsp6_final_info *final_info;
  rtx next_insn;

  if(!(TARGET_PACKETS && optimize)){
    return;
  }

  final_info = &cfun->machine->final_info;

  final_info->insn_ops = ops;
  final_info->start_packet = false;
  final_info->end_packet = false;
  final_info->indent_insn = true;
  final_info->print_insn = true;
  final_info->print_endloop0 = false;
  final_info->print_endloop1 = false;

  if(!INSN_P (insn) || INSN_CODE (insn) == -1){
    return;
  }

  /* Check whether this insn starts a new packet. */
  if(GET_MODE (insn) == TImode){
    final_info->endloop0 = false;

    /* If this is not actually a packet but a sequence of serial instructions,
       then it should not be grouped with any other insns, and it should not
       have curly brackets printed around it. */
    if(get_attr_type(insn) == TYPE_MULTIPLE){
      final_info->indent_insn = false;
      return;
    }

    final_info->start_packet = true;
  }

  /* Insns that are actually sequences of serial instructions should always
     start a packet. */
  gcc_assert(get_attr_type(insn) != TYPE_MULTIPLE);

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

  /* Advance and skip notes. */
  for(next_insn = NEXT_INSN (insn);
      next_insn && (!INSN_P (next_insn) || INSN_CODE (next_insn) == -1);
      next_insn = NEXT_INSN (next_insn));
  /* If this is the last insn in a packet, then end the packet. */
  if(!next_insn || GET_MODE (next_insn) == TImode){
    final_info->end_packet = true;
  }
}




/* globals used to pass information from qdsp6_print_operand to
   qdsp6_print_operand_address */

/* whether the current operand contains an extended constant */
static bool qdsp6_extended_constant;

/* the mode of the current address being printed */
static enum machine_mode qdsp6_address_mode;

/* Implements macro PRINT_OPERAND */

void
qdsp6_print_operand(FILE *stream, rtx x, int code)
{
  qdsp6_extended_constant = false;

  switch(code){
    case 'P':
      if(G_REG_P (x) && REGNO (x) % 2 == 0){
        fprintf(stream, "%s:%d", reg_names[REGNO (x) + 1], REGNO (x));
      }
      else {
        output_operand_lossage("qdsp6_print_operand: invalid operand for %%P");
      }
      return;

    case 'H':
      /* Output the second register of a 64 bit register pair. */
      if(G_REG_P (x) && REGNO (x) % 2 == 0){
        fputs(reg_names[REGNO (x) + 1], stream);
      }
      else {
        output_operand_lossage("qdsp6_print_operand: invalid operand for %%H");
      }
      return;

    case 'L':
      /* Output the first register of a 64 bit register pair. */
      if(G_REG_P (x) && REGNO (x) % 2 == 0){
        fputs(reg_names[REGNO (x)], stream);
      }
      else {
        output_operand_lossage("qdsp6_print_operand: invalid operand for %%L");
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
      }
      else {
        if(code == 'C'){
          output_operand_lossage("qdsp6_print_operand: invalid operand for %%C");
        }
        else {
          output_operand_lossage("qdsp6_print_operand: invalid operand for %%I");
        }
      }
      return;

    /* The four parts of a double */
    case 'S':
      if(GET_CODE (x) == CONST_DOUBLE){
        rtx subword = operand_subword(x, 1, 1, DFmode);
        HOST_WIDE_INT bits = INTVAL (subword);
        unsigned short immValueHH = (bits & 0xffff0000UL) >> 16;
        fprintf(stream, "%u", immValueHH);
      }
      else {
        output_operand_lossage("qdsp6_print_operand: invalid operand for %%S");
      }
      return;
    case 'T':
      if(GET_CODE (x) == CONST_DOUBLE){
        rtx subword = operand_subword(x, 1, 1, DFmode);
        HOST_WIDE_INT bits = INTVAL (subword);
        unsigned short immValueHL = bits & 0x0000ffffUL;
        fprintf(stream, "%u", immValueHL);
      }
      else {
        output_operand_lossage("qdsp6_print_operand: invalid operand for %%T");
      }
      return;
    case 'U':
      if(GET_CODE (x) == CONST_DOUBLE){
        rtx subword = operand_subword(x, 0, 1, DFmode);
        HOST_WIDE_INT bits = INTVAL (subword);
        unsigned short immValueLH = (bits & 0xffff0000UL) >> 16;
        fprintf(stream, "%u", immValueLH);
      }
      else {
        output_operand_lossage("qdsp6_print_operand: invalid operand for %%U");
      }
      return;
    case 'V':
      if(GET_CODE (x) == CONST_DOUBLE){
        rtx subword = operand_subword(x, 0, 1, DFmode);
        HOST_WIDE_INT bits = INTVAL (subword);
        unsigned short immValueLL = bits & 0x0000ffffUL;
        fprintf(stream, "%u", immValueLL);
      }
      else {
        output_operand_lossage("qdsp6_print_operand: invalid operand for %%V");
      }
      return;

    /* The four parts of a long long */
    case 'W':
      if(GET_CODE (x) == CONST_DOUBLE){
        rtx subword = operand_subword(x, 1, 1, DImode);
        HOST_WIDE_INT bits = INTVAL (subword);
        unsigned short immValueHH = (bits & 0xffff0000UL) >> 16;
        fprintf(stream, "%u", immValueHH);
      }
      else {
        output_operand_lossage("qdsp6_print_operand: invalid operand for %%W");
      }
      return;
    case 'X':
      if(GET_CODE (x) == CONST_DOUBLE){
        rtx subword = operand_subword(x, 1, 1, DImode);
        HOST_WIDE_INT bits = INTVAL (subword);
        unsigned short immValueHL = bits & 0x0000ffffUL;
        fprintf(stream, "%u", immValueHL);
      }
      else {
        output_operand_lossage("qdsp6_print_operand: invalid operand for %%X");
      }
      return;
    case 'Y':
      if(GET_CODE (x) == CONST_DOUBLE){
        rtx subword = operand_subword(x, 0, 1, DImode);
        HOST_WIDE_INT bits = INTVAL (subword);
        unsigned short immValueLH = (bits & 0xffff0000UL) >> 16;
        fprintf(stream, "%u", immValueLH);
      }
      else {
        output_operand_lossage("qdsp6_print_operand: invalid operand for %%Y");
      }
      return;
    case 'Z':
      if(GET_CODE (x) == CONST_DOUBLE){
        rtx subword = operand_subword(x, 0, 1, DImode);
        HOST_WIDE_INT bits = INTVAL (subword);
        unsigned short immValueLL = bits & 0x0000ffffUL;
        fprintf(stream, "%u", immValueLL);
      }
      else {
        output_operand_lossage("qdsp6_print_operand: invalid operand for %%Z");
      }
      return;

    case 'J':
      {
        int log = exact_log2(INTVAL (x) & 0xFFFFFFFFULL);
        if(log == -1){
          output_operand_lossage("qdsp6_print_operand: invalid operand for %%J");
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
          output_operand_lossage("qdsp6_print_operand: invalid operand for %%K");
        }
        else {
          fprintf(stream, "%d", log);
        }
      }
      return;

    case 'E':
      gcc_assert(TARGET_V4_FEATURES);
      qdsp6_extended_constant = true;
      /* handled below */
      break;

    case 0:
      /* handled below */
      break;

    default:
      output_operand_lossage("qdsp6_print_operand: unknown code, 0x%x", code);
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
          output_operand_lossage("qdsp6_print_operand: invalid register");
        }
      }
      break;

    case MEM:
      qdsp6_address_mode = GET_MODE (x);
      output_address(XEXP (x, 0));

      break;

    case CONST_INT:
      if(INTVAL (x) < -0xFFFFFFFFLL){
        fprintf(stream, HOST_WIDE_INT_PRINT_HEX, INTVAL (x));
      }
      else {
        fprintf(stream, HOST_WIDE_INT_PRINT_DEC, INTVAL (x));
      }
      break;

    case CONST_DOUBLE:
      /* We handle floating point constants here because output_addr_const
         doesn't. */
      if(GET_MODE (x) == SFmode){
        REAL_VALUE_TYPE rv;
        long l;

        REAL_VALUE_FROM_CONST_DOUBLE (rv, x);
        REAL_VALUE_TO_TARGET_SINGLE (rv, l);
        l &= 0xFFFFFFFFUL;
        fprintf(stream, "0x%08lx", l);
        break;
      }
      else if(GET_MODE (x) == DFmode){
        REAL_VALUE_TYPE rv;
        long l[2];

        REAL_VALUE_FROM_CONST_DOUBLE (rv, x);
        REAL_VALUE_TO_TARGET_DOUBLE (rv, l);
        l[0] &= 0xFFFFFFFFUL;
        l[1] &= 0xFFFFFFFFUL;
        fprintf(stream, "0x%08lx%08lx", l[1], l[0]);
        break;
      }
      /* FALL THROUGH.  Let output_addr_const deal with it. */

    default:
      output_addr_const(stream, x);
      break;
  }

  return;
}




/* Implements macro PRINT_OPERAND_ADDRESS

   Print a memory address as an operand to reference that memory location. */

void
qdsp6_print_operand_address(FILE *stream, rtx x)
{
  switch(GET_CODE (x)){
    case REG:
      if(G_REG_P (x)){
        fputs(reg_names[REGNO (x)], stream);
        fputs("+#0", stream);
      }
      else {
        output_operand_lossage("qdsp6_print_operand_address: invalid base register");
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
          output_operand_lossage("qdsp6_print_operand_address: invalid base+index base");
          break;
        }

        if(CONSTANT_P (offset)){
          fputc('#', stream);
          if(qdsp6_extended_constant){
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
            output_operand_lossage("qdsp6_print_operand_address: invalid base+index scale amount");
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
          output_operand_lossage("qdsp6_print_operand_address: invalid base+index index");
        }

        if(CONSTANT_P (base)){
          fputc('+', stream);
          fputc('#', stream);
          if(qdsp6_extended_constant){
            fputc('#', stream);
          }
          output_addr_const(stream, base);
        }
        break;
      }

    case POST_INC:
      if(G_REG_P (XEXP (x, 0))){
        fprintf(stream, "%s++#%d", reg_names[REGNO (XEXP (x, 0))], GET_MODE_SIZE (qdsp6_address_mode));
      }
      else {
        output_operand_lossage("qdsp6_print_operand_address: invalid post increment base register");
      }
      break;

    case POST_DEC:
      if(G_REG_P (XEXP (x, 0))){
        fprintf(stream, "%s++#-%d", reg_names[REGNO (XEXP (x, 0))], GET_MODE_SIZE (qdsp6_address_mode));
      }
      else {
        output_operand_lossage("qdsp6_print_operand_address: invalid post decrement base register");
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
          output_operand_lossage("qdsp6_print_operand_address: invalid post modify base register");
        }
      }
      break;

    case SYMBOL_REF:
    case CONST:
    case CONST_INT:
    case LABEL_REF:
      if(sdata_symbolic_operand(x, Pmode) && !qdsp6_extended_constant){
        fputc('#', stream);
      }
      else if(CONSTANT_P (x)){
        fputs("##", stream);
      }
      output_addr_const(stream, x);
      break;

    default:
      output_operand_lossage("qdsp6_print_operand_address: invalid address code 0x%x", GET_CODE (x));
      break;
  }
}




/*----------------------
Miscellaneous Parameters
----------------------*/

#if GCC_3_4_6
#define dump_file rtl_dump_file
#endif /* GCC_3_4_6 */

static void
qdsp6_fixup_cfg(void)
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




static void
qdsp6_fixup_doloops(void)
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
    fprintf(dump_file, ";; qdsp6 org loops starting\n");
  }

  FOR_EACH_BB (bb){
    tail = BB_END (bb);

    if(!INSN_P (tail)){
      tail = prev_real_insn(tail);
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


/* Implements hook TARGET_MACHINE_DEPENDENT_REORG */

static void
qdsp6_machine_dependent_reorg(void)
{
  rtx insn;
  rtx next;

  compute_bb_for_insn();

#if 0
  verify_flow_info();
#endif /* 0 */

  if(cfun->machine->has_hardware_loops
     || (TARGET_PULLUP && optimize)){
    qdsp6_fixup_cfg();
  }

  /* doloop fixups */
  if(cfun->machine->has_hardware_loops){
    qdsp6_fixup_doloops();
  }
  
  if (TARGET_LOCAL_COMBINE) 
    {
      qdsp6_local_combine_pass();
    }

  if(TARGET_PULLUP && optimize){
    qdsp6_packet_optimizations();
  }

  /* Performance degradation. Disable it.
      schedule_ebbs ();  */ 

  if(!optimize || optimize_size){
    return;
  }

  /* Insert .faligns. */
  if(qdsp6_falign == QDSP6_FALIGN_LABELS){
    insn = get_insns(); 
    for(; insn; insn = NEXT_INSN (insn)){
      if(GET_CODE (insn) == CODE_LABEL){
        if(!(next = next_real_insn(insn))){
          break;
        }
        if(!JUMP_TABLE_DATA_P (next)){
          PUT_MODE (emit_insn_before(gen_falign(), insn), TImode);
        }
        insn = next;
      }
    }
  }
  else if(qdsp6_falign == QDSP6_FALIGN_LOOPS){
    rtx label; 

    /* _LSY_ Go backwards and falign only labels that are targets
       for backward jumps */ 
    insn = get_last_insn(); 
    for(; insn; insn = PREV_INSN(insn)){ 
  	if(JUMP_P(insn)){
		/* If label first seen in jump, mark it */ 
	  label = JUMP_LABEL(insn); 
	  if(label)	LABEL_START_LOOP(label) = 1; 
	}

	if(LABEL_P(insn)){
	  if(!(next = next_real_insn(insn)))	continue; 
          if(!JUMP_TABLE_DATA_P (next)){
		if(LABEL_START_LOOP(insn))
          		PUT_MODE (emit_insn_before(gen_falign(), insn), TImode);
          }
	}
    } 
  }

#if 0
  verify_flow_info();
#endif /* 0 */

}




#if GCC_3_4_6
#define def_builtin(NAME, TYPE, CODE) \
  builtin_function(NAME, TYPE, END_BUILTINS + 1 + CODE, BUILT_IN_MD, NULL, \
                   NULL_TREE)
#else /* !GCC_3_4_6 */
#define def_builtin(NAME, TYPE, CODE) \
  do { \
    tree t; \
    t = add_builtin_function(NAME, TYPE, END_BUILTINS + 1 + CODE, \
                             BUILT_IN_MD, NULL, \
                             tree_cons(get_identifier("const"), \
                                       NULL_TREE, NULL_TREE));  \
    if (CODE == QDSP6_BUILTIN_val_for_valignb) { \
      qdsp6_builtin_mask_for_load = t; \
    } \
  } while (0);
#endif /* !GCC_3_4_6 */

#define BI_type_node boolean_type_node
#define QI_type_node char_type_node
#define HI_type_node short_integer_type_node
#define SI_type_node integer_type_node
#define USI_type_node unsigned_type_node
#define DI_type_node long_long_integer_type_node
#define UDI_type_node long_long_unsigned_type_node

/* Implements hook TARGET_INIT_BUILTINS */

static void
qdsp6_init_builtins(void)
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

#define BUILTIN_INFO(TAG, TYPE, NARGS) \
  def_builtin("__builtin_" #TAG, TYPE, QDSP6_BUILTIN_##TAG);
#include "builtins.def"
#include "manual_builtins.def"
#undef BUILTIN_INFO

#if !GCC_3_4_6
  gcc_assert(qdsp6_builtin_mask_for_load);
#endif /* !GCC_3_4_6 */
}




/* Helper function for qdsp6_expand_builtin */

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
qdsp6_expand_builtin(
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
    case QDSP6_BUILTIN_##TAG: \
      return expand_one_builtin(CODE_FOR_qdsp6_builtin_##TAG, \
                                target, exp, NARGS);
#include "builtins.def"
#include "manual_builtins.def"
#undef BUILTIN_INFO
    default:
      abort();
      break;
  }
}




/* Implements hook TARGET_INVALID_WITHIN_DOLOOP

   Don't form a hardware loop around a call or a set or clobber of a loop
   register. */

static const char *
qdsp6_invalid_within_doloop(const_rtx insn)
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




/* Helper function for qdsp6_print_rtl_pseudo_asm

   (set (pc) (...)) */

static void
qdsp6_print_jump(FILE *stream, rtx x)
{
  /* (set (pc) (if_then_else (...) (...) (...))) */
  if(x && GET_CODE (x) == SET
     && SET_SRC (x) && GET_CODE (SET_SRC (x)) == IF_THEN_ELSE){
    /* (set (pc) (if_then_else (...) (pc) (...))) */
    if(XEXP (SET_SRC (x), 1) && XEXP (SET_SRC (x), 1) == pc_rtx){
      qdsp6_print_condition(stream, XEXP (SET_SRC (x), 0), false);
      /* (set (pc) (if_then_else (...) (pc) (label))) */
      if(GET_CODE (XEXP (SET_SRC (x), 2)) == LABEL_REF){
        fputs("jump", stream);
      }
      else {
        fputs("jump ", stream);
        qdsp6_print_rtx(stream, XEXP (SET_SRC (x), 2));
      }
    }
    /* (set (pc) (if_then_else (...) (...) (pc))) */
    else if(XEXP (SET_SRC (x), 2) && XEXP (SET_SRC (x), 2) == pc_rtx){
      qdsp6_print_condition(stream, XEXP (SET_SRC (x), 0), true);
      /* (set (pc) (if_then_else (...) (label) (pc))) */
      if(GET_CODE (XEXP (SET_SRC (x), 1)) == LABEL_REF){
        fputs("jump", stream);
      }
      else {
        fputs("jump ", stream);
        qdsp6_print_rtx(stream, XEXP (SET_SRC (x), 1));
      }
    }
    else {
      fputs("jump ", stream);
      qdsp6_print_rtx(stream, SET_SRC (x));
    }
  }
  /* (set (pc) (reg)) */
  else if(x && GET_CODE (x) == SET
          && SET_DEST (x) == pc_rtx
          && SET_SRC (x) && REG_P (SET_SRC (x))){
    fputs("jump ", stream);
    qdsp6_print_rtx(stream, SET_SRC (x));
  }
  else {
    fputs("jump", stream);
  }
}




/* Helper function for qdsp6_print_rtl_pseudo_asm

   (set (...) (...)) */

static void
qdsp6_print_transfer(FILE *stream, rtx x)
{
  if(!x){
    qdsp6_print_rtx(stream, x);
  }
  /* (set (pc) (...)) */
  else if(XEXP (x, 0) == pc_rtx){
    qdsp6_print_jump(stream, x);
  }
  /* (set (reg) (call)) */
  else if(XEXP (x, 0) && REG_P (XEXP (x, 0))
          && XEXP (x, 1) && GET_CODE (XEXP (x, 1)) == CALL){
    fputs("call", stream);
  }
  /* (set (zero_extract (...) (...) (...)) (...)) */
  else if(XEXP (x, 0) && GET_CODE (XEXP (x, 0)) == ZERO_EXTRACT){
    qdsp6_print_rtx(stream, XEXP (XEXP (x, 0), 0));
    fputs(" = insert(", stream);
    qdsp6_print_rtx(stream, XEXP (x, 1));
    fputc(',', stream);
    qdsp6_print_rtx(stream, XEXP (XEXP (x, 0), 1));
    fputc(',', stream);
    qdsp6_print_rtx(stream, XEXP (XEXP (x, 0), 2));
    fputc(')', stream);
  }
  /* (set (...) (high (...))) */
  else if(XEXP (x, 1) && GET_CODE (XEXP (x, 1)) == HIGH){
    qdsp6_print_rtx(stream, XEXP (x, 0));
    fputs(".h = ", stream);
    qdsp6_print_rtx(stream, XEXP (XEXP (x, 1), 0));
  }
  /* (set (reg X) (lo_sum (reg X) (...))) */
  else if(XEXP (x, 1) && GET_CODE (XEXP (x, 1)) == LO_SUM
          && XEXP (x, 0) && REG_P (XEXP (x, 0))
          && XEXP (XEXP (x, 1), 0) && REG_P (XEXP (XEXP (x, 1), 0))
          && REGNO (XEXP (x, 0)) == REGNO (XEXP (XEXP (x, 1), 0))){
    qdsp6_print_rtx(stream, XEXP (x, 0));
    fputs(".l = ", stream);
    qdsp6_print_rtx(stream, XEXP (XEXP (x, 1), 1));
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
    qdsp6_print_rtx(stream, XEXP (x, 0));
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
    qdsp6_print_rtx(stream, XEXP (XEXP (x, 1), 1));
  }
  else if(XEXP (x, 1) && (   GET_CODE (XEXP (x, 1)) == PLUS
                          || GET_CODE (XEXP (x, 1)) == MULT
                          || GET_CODE (XEXP (x, 1)) == AND
                          || GET_CODE (XEXP (x, 1)) == IOR
                          || GET_CODE (XEXP (x, 1)) == XOR)
          && XEXP (x, 0) && REG_P (XEXP (x, 0))
          && XEXP (XEXP (x, 1), 1) && REG_P (XEXP (XEXP (x, 1), 1))){
    qdsp6_print_rtx(stream, XEXP (x, 0));
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
    qdsp6_print_rtx(stream, XEXP (XEXP (x, 1), 0));
  }
*/
  else {
    qdsp6_print_rtx(stream, XEXP (x, 0));
    fputs(" = ", stream);
    qdsp6_print_rtx(stream, XEXP (x, 1));
  }
}




/* Helper function for qdsp6_print_rtl_pseudo_asm */

static void
qdsp6_print_condition(FILE *stream, rtx x, bool non_inverted)
{
  fputs("if (", stream);
  if(!x){
    qdsp6_print_rtx(stream, x);
  }
  /* (reg) */
  else if(REG_P (x)){
    if(GET_MODE (x) == BImode && !non_inverted){
      fputc('!', stream);
    }
    qdsp6_print_rtx(stream, x);
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
    qdsp6_print_rtx(stream, XEXP (x, 0));
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
    qdsp6_print_rtx(stream, XEXP (x, 0));
    if(GET_MODE (XEXP (x, 0)) != BImode){
      fputs(non_inverted ? "==#0" : "!=#0", stream);
    }
  }
  /* (gt (reg) (const_int 0/-1)) */
  else if(GET_CODE (x) == GT
          && XEXP (x, 0) && REG_P (XEXP (x, 0))
          && GET_MODE (XEXP (x, 0)) != BImode
          && (XEXP (x, 1) == const0_rtx || XEXP (x, 1) == constm1_rtx)){
    qdsp6_print_rtx(stream, XEXP (x, 0));
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
    qdsp6_print_rtx(stream, XEXP (x, 0));
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
    qdsp6_print_rtx(stream, XEXP (x, 0));
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
    qdsp6_print_rtx(stream, XEXP (x, 0));
    if(XEXP (x, 1) == const0_rtx){
      fputs(non_inverted ? "<=#0" : ">#0", stream);
    }
    else {
      fputs(non_inverted ? "<#0" : ">=#0", stream);
    }
  }
  else {
    qdsp6_print_rtx(stream, x);
  }
  fputs(") ", stream);
}




/* Helper function for qdsp6_print_rtl_pseudo_asm */

static void
qdsp6_print_address(FILE *stream, rtx x)
{
  /* (plus (...) (...)) */
  if(x && GET_CODE (x) == PLUS){
    qdsp6_print_rtx(stream, XEXP (x, 0));
    fputc('+', stream);
    qdsp6_print_rtx(stream, XEXP (x, 1));
  }
  else {
    qdsp6_print_rtx(stream, x);
  }
}




/* Helper function for qdsp6_print_rtl_pseudo_asm

   (op (...)) */

static void
qdsp6_print_unary_op(FILE *stream, const char *op, rtx x)
{
  fputs(op, stream);
  fputc('(', stream);
  qdsp6_print_rtx(stream, XEXP (x, 0));
  fputc(')', stream);
}




/* Helper function for qdsp6_print_rtl_pseudo_asm

   (op (...) (...)) */

static void
qdsp6_print_binary_op(FILE *stream, const char *op, rtx x)
{
  fputs(op, stream);
  fputc('(', stream);
  qdsp6_print_rtx(stream, XEXP (x, 0));
  fputc(',', stream);
  qdsp6_print_rtx(stream, XEXP (x, 1));
  fputc(')', stream);
}




/* Helper function for qdsp6_print_rtl_pseudo_asm

   (op (...) (...)) */

static void
qdsp6_print_swapped_binary_op(FILE *stream, const char *op, rtx x)
{
  fputs(op, stream);
  fputc('(', stream);
  qdsp6_print_rtx(stream, XEXP (x, 1));
  fputc(',', stream);
  qdsp6_print_rtx(stream, XEXP (x, 0));
  fputc(')', stream);
}




/* Helper function for qdsp6_print_rtl_pseudo_asm

   (op (...) (...)) */

static void
qdsp6_print_binary_op_with_option(
  FILE *stream,
  const char *op,
  const char *option,
  rtx x
)
{
  fputs(op, stream);
  fputc('(', stream);
  qdsp6_print_rtx(stream, XEXP (x, 0));
  fputc(',', stream);
  qdsp6_print_rtx(stream, XEXP (x, 1));
  fputs("):", stream);
  fputs(option, stream);
}




/* Helper function for qdsp6_print_rtl_pseudo_asm

   (op (...) (...) (...)) */

static void
qdsp6_print_trinary_op(FILE *stream, const char *op, rtx x)
{
  fputs(op, stream);
  fputc('(', stream);
  qdsp6_print_rtx(stream, XEXP (x, 0));
  fputc(',', stream);
  qdsp6_print_rtx(stream, XEXP (x, 1));
  fputc(',', stream);
  qdsp6_print_rtx(stream, XEXP (x, 2));
  fputc(')', stream);
}




/* Helper function for qdsp6_print_rtl_pseudo_asm

   (parallel/unspec/unspec_volatile [...]) */

static void
qdsp6_print_vecexp(
  FILE *stream,
  const char *open,
  const char *separator,
  const char *close,
  rtx x
)
{
  int i;
  fputs(open, stream);
  for(i = 0; i < XVECLEN (x, 0); i++){
    if(i > 0){
      fputs(separator, stream);
    }
    qdsp6_print_rtx(stream, XVECEXP (x, 0, i));
  }
  fputs(close, stream);
}




/* Helper function for qdsp6_print_rtl_pseudo_asm */

static void
qdsp6_print_rtx(FILE *stream, rtx x)
{
  const char *op;
  int size_in_bytes;
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
      qdsp6_print_transfer(stream, x);
      break;
    case COND_EXEC:
      qdsp6_print_condition(stream, XEXP (x, 0), true);
      qdsp6_print_rtx(stream, XEXP (x, 1));
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
      qdsp6_print_vecexp(stream, "{ ", "; ", " }", x);
      break;
    case UNSPEC:
      fprintf(stream, "unspec" HOST_WIDE_INT_PRINT_DEC, XINT (x, 1));
      qdsp6_print_vecexp(stream, "(", ",", ")", x);
      break;
    case UNSPEC_VOLATILE:
      fprintf(stream, "unspec_volatile" HOST_WIDE_INT_PRINT_DEC, XINT (x, 1));
      qdsp6_print_vecexp(stream, "(", ",", ")", x);
      break;
    case PREFETCH:
      qdsp6_print_unary_op(stream, "dcfetch", x);
      break;
    case USE:
      qdsp6_print_unary_op(stream, "use", x);
      break;
    case CLOBBER:
      qdsp6_print_rtx(stream, XEXP (x, 0));
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
      qdsp6_print_rtx(stream, XEXP (x, 0));
      break;
    case SUBREG:
      if(reload_completed){
        qdsp6_print_rtx(stream, XEXP (x, 0));
      }
      else {
        if(GET_MODE (x) == SImode
           && XEXP (x, 0) && REG_P (XEXP (x, 0))
           && GET_MODE (XEXP (x, 0)) == DImode
           && (XINT (x, 1) == 0 || XINT (x, 1) == 4)){
          fputc('R', stream);
        }
        else {
          qdsp6_print_rtx(stream, XEXP (x, 0));
/*
          fputc('.', stream);
          size_in_bytes = 1;
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
      switch(GET_MODE (x)){
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
      fputc('(', stream);
      qdsp6_print_address(stream, XEXP (x, 0));
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
        qdsp6_print_rtx(stream, XEXP (XEXP (x, 0), 0));
        fputc(',', stream);
        qdsp6_print_rtx(stream, XEXP (x, 1));
        fputc(',', stream);
        qdsp6_print_rtx(stream, XEXP (x, 2));
        fputc(')', stream);
      }
      else if(XEXP (x, 0) && GET_CODE (XEXP (x, 0)) == EQ
              && XEXP (XEXP (x, 0), 1) == const0_rtx){
        fputs("mux(", stream);
        qdsp6_print_rtx(stream, XEXP (XEXP (x, 0), 0));
        fputc(',', stream);
        qdsp6_print_rtx(stream, XEXP (x, 2));
        fputc(',', stream);
        qdsp6_print_rtx(stream, XEXP (x, 1));
        fputc(')', stream);
      }
      else {
        qdsp6_print_trinary_op(stream, "mux", x);
      }
      break;
    case PLUS:
      qdsp6_print_binary_op(stream, "add", x);
      break;
    case MINUS:
      qdsp6_print_binary_op(stream, "sub", x);
      break;
    case NEG:
      qdsp6_print_unary_op(stream, "neg", x);
      break;
    case MULT:
      qdsp6_print_binary_op(stream, "mpyi", x);
      break;
    case AND:
      qdsp6_print_binary_op(stream, "and", x);
      break;
    case IOR:
      qdsp6_print_binary_op(stream, "or", x);
      break;
    case XOR:
      qdsp6_print_binary_op(stream, "xor", x);
      break;
    case NOT:
      qdsp6_print_unary_op(stream, "not", x);
      break;
    case ASHIFT:
      qdsp6_print_binary_op(stream, "asl", x);
      break;
    case ROTATE:
      if(XEXP (x, 0) && REG_P (XEXP (x, 0)) && GET_MODE (XEXP (x, 0)) == SImode
         && XEXP (x, 1) && GET_CODE (XEXP (x, 1)) == CONST_INT
         && INTVAL (XEXP (x, 1)) == 16){
        fputs("combine(", stream);
        qdsp6_print_rtx(stream, XEXP (x, 0));
        fputs(".l,", stream);
        qdsp6_print_rtx(stream, XEXP (x, 0));
        fputs(".h)", stream);
      }
      else {
        qdsp6_print_binary_op(stream, "rotate_left", x);
      }
      break;
    case ASHIFTRT:
      qdsp6_print_binary_op(stream, "asr", x);
      break;
    case LSHIFTRT:
      qdsp6_print_binary_op(stream, "lsr", x);
      break;
    case ROTATERT:
      if(XEXP (x, 0) && REG_P (XEXP (x, 0)) && GET_MODE (XEXP (x, 0)) == SImode
         && XEXP (x, 1) && GET_CODE (XEXP (x, 1)) == CONST_INT
         && INTVAL (XEXP (x, 1)) == 16){
        fputs("combine(", stream);
        qdsp6_print_rtx(stream, XEXP (x, 0));
        fputs(".l,", stream);
        qdsp6_print_rtx(stream, XEXP (x, 0));
        fputs(".h)", stream);
      }
      else {
        qdsp6_print_binary_op(stream, "rotate_right", x);
      }
      break;
    case SMIN:
      qdsp6_print_binary_op(stream, "min", x);
      break;
    case SMAX:
      qdsp6_print_binary_op(stream, "max", x);
      break;
    case UMIN:
      qdsp6_print_binary_op(stream, "minu", x);
      break;
    case UMAX:
      qdsp6_print_binary_op(stream, "maxu", x);
      break;
    case POST_DEC:
    case POST_INC:
      qdsp6_print_rtx(stream, XEXP (x, 0));
      fputs("++#", stream);
      break;
    case POST_MODIFY:
      if(XEXP (x, 0) && REG_P (XEXP (x, 0))
         && XEXP (x, 1) && GET_CODE (XEXP (x, 1)) == PLUS
         && XEXP (XEXP (x, 1), 0) && REG_P (XEXP (XEXP (x, 1), 0))
         && REGNO (XEXP (x, 0)) == REGNO (XEXP (XEXP (x, 1), 0))){
        qdsp6_print_rtx(stream, XEXP (x, 0));
        fputs("++", stream);
        qdsp6_print_rtx(stream, XEXP (XEXP (x, 1), 1));
      }
      else {
        qdsp6_print_rtx(stream, XEXP (x, 0));
        fputs(", ", stream);
        qdsp6_print_transfer(stream, x);
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
        qdsp6_print_rtx(stream, XEXP (XEXP (x, 0), 0));
        fputc(',', stream);
        qdsp6_print_rtx(stream, XEXP (XEXP (x, 0), 2));
        fputc(')', stream);
      }
      else {
        qdsp6_print_binary_op(stream, GET_CODE (x) == NE ? "cmp.ne" : "cmp.eq",
                              x);
      }
      break;
    case GE:
      qdsp6_print_binary_op(stream, "cmp.ge", x);
      break;
    case GT:
      qdsp6_print_binary_op(stream, "cmp.gt", x);
      break;
    case LE:
      qdsp6_print_swapped_binary_op(stream, "cmp.gt", x);
      break;
    case LT:
      qdsp6_print_swapped_binary_op(stream, "cmp.ge", x);
      break;
    case GEU:
      qdsp6_print_binary_op(stream, "cmp.geu", x);
      break;
    case GTU:
      qdsp6_print_binary_op(stream, "cmp.gtu", x);
      break;
    case LEU:
      qdsp6_print_swapped_binary_op(stream, "cmp.gtu", x);
      break;
    case LTU:
      qdsp6_print_swapped_binary_op(stream, "cmp.geu", x);
      break;
    case SIGN_EXTEND:
    case ZERO_EXTEND:
      op = GET_CODE (x) == SIGN_EXTEND ? "sxt" : "zxt";
      if(!XEXP (x, 0)){
        qdsp6_print_unary_op(stream, op, XEXP (x, 0));
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
          qdsp6_print_address(stream, XEXP (XEXP (x, 0), 0));
          fputc(')', stream);
        }
        else {
          qdsp6_print_unary_op(stream, "", x);
        }
      }
      break;
    case TRUNCATE:
      qdsp6_print_rtx(stream, XEXP (x, 0));
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
      qdsp6_print_unary_op(stream, "abs", x);
      break;
    case CLZ:
      qdsp6_print_unary_op(stream, "cl0", x);
      break;
    case CTZ:
      qdsp6_print_unary_op(stream, "ct0", x);
      break;
    case POPCOUNT:
      qdsp6_print_unary_op(stream, "count_ones", x);
      break;
    case PARITY:
      qdsp6_print_unary_op(stream, "parity", x);
      break;
    case SIGN_EXTRACT:
      qdsp6_print_trinary_op(stream, "extract", x);
      break;
    case ZERO_EXTRACT:
      qdsp6_print_trinary_op(stream, "extractu", x);
      break;
    case HIGH:
      qdsp6_print_rtx(stream, XEXP (x, 0));
      fputs(".h", stream);
      break;
    case LO_SUM:
      fputs("add(", stream);
      qdsp6_print_rtx(stream, XEXP (x, 0));
      fputc(',', stream);
      qdsp6_print_rtx(stream, XEXP (x, 1));
      fputs(".l)", stream);
      break;
    case SS_PLUS:
      qdsp6_print_binary_op_with_option(stream, "add", "sat", x);
      break;
    case US_PLUS:
      qdsp6_print_binary_op_with_option(stream, "add", "satu", x);
      break;
    case SS_MINUS:
      qdsp6_print_binary_op_with_option(stream, "sub", "sat", x);
      break;
    case US_MINUS:
      qdsp6_print_binary_op_with_option(stream, "sub", "satu", x);
      break;
    case SS_TRUNCATE:
      switch(GET_MODE (x)){
        case HImode:
          qdsp6_print_unary_op(stream, "sath", x);
          break;
        case QImode:
          qdsp6_print_unary_op(stream, "satb", x);
          break;
        default:
          qdsp6_print_unary_op(stream, "sat", x);
      }
      break;
    case US_TRUNCATE:
      switch(GET_MODE (x)){
        case HImode:
          qdsp6_print_unary_op(stream, "satuh", x);
          break;
        case QImode:
          qdsp6_print_unary_op(stream, "satub", x);
          break;
        default:
          qdsp6_print_unary_op(stream, "satu", x);
      }
      break;
    default:
      fprintf(stream, "[%s]", GET_RTX_NAME (GET_CODE (x)));
  }
}




/* Implements hook TARGET_PRINT_RTL_PSEUDO_ASM */

void
qdsp6_print_rtl_pseudo_asm(FILE *stream, rtx x)
{
  if(x && INSN_P (x)){
    qdsp6_print_rtx(stream, PATTERN (x));
  }
  else {
    qdsp6_print_rtx(stream, x);
  }
}




/*----------------------------
Machine Description Predicates
----------------------------*/

#if GCC_3_4_6
/*-------
Registers
-------*/

/* general purpose register */

int
gr_register_operand(rtx op, enum machine_mode mode)
{
  unsigned int regno;
  if(!register_operand(op, mode)){
    return false;
  }
  if(GET_CODE (op) == SUBREG){
    op = SUBREG_REG (op);
    /* Paradoxical SUBREGs where the smaller mode is BI are causing problems.
       Try disallowing them here. */
    if(GET_MODE (op) == BImode){
      return false;
    }
  }
  /* ??? Allow (subreg (mem))? */
  if(!REG_P (op)){
    return false;
  }
  regno = REGNO (op);
  return G_REGNO_P (regno)
         || regno == FRAME_POINTER_REGNUM
         || regno == ARG_POINTER_REGNUM
         || regno >= FIRST_PSEUDO_REGISTER;
}




/* predicate register */

int
pr_register_operand(rtx op, enum machine_mode mode)
{
  unsigned int regno;
  if(!register_operand(op, mode)){
    return false;
  }
  if(GET_CODE (op) == SUBREG){
    op = SUBREG_REG (op);
  }
  /* ??? Allow (subreg (mem))? */
  if(!REG_P (op)){
    return false;
  }
  regno = REGNO (op);
  return P_REGNO_P (regno) || regno >= FIRST_PSEUDO_REGISTER;
}




/* non-general purpose register */

int
nongr_register_operand(rtx op, enum machine_mode mode)
{
  if(!register_operand(op, mode)){
    return false;
  }
  if(GET_CODE (op) == SUBREG){
    op = SUBREG_REG (op);
  }
  /* ??? Allow (subreg (mem))? */
  return REG_P (op) && !G_REG_P (op);
}




/* vector suitable for splatting */

int
splattable_vector(rtx op, enum machine_mode mode)
{
  int i;
  if(!gr_register_operand(op, mode)){
    return false;
  }
  for(i = 1; i < GET_MODE_NUNITS (mode); i++){
    if(!rtx_equal_p(XVECEXP (op, 0, i), XVECEXP (op, 0, 0))){
      return false;
    }
  }
  return true;
}




/*---------------
Memory/References
---------------*/

/* memory with address in register */

int
indirect_memory_operand(rtx op, enum machine_mode mode)
{
  return memory_operand(op, mode) && REG_P (XEXP (op, 0));
}




/* call target */

int
call_target_operand(rtx op, enum machine_mode mode)
{
  return GET_CODE (op) == SYMBOL_REF || register_operand(op, mode);
}




/* small data reference */

int
sdata_symbolic_operand(rtx op, enum machine_mode mode ATTRIBUTE_UNUSED)
{
  HOST_WIDE_INT offset = 0, size = 0;
  tree t;
  switch(GET_CODE (op)){
    case CONST:
      op = XEXP (op, 0);
      if(!(GET_CODE (op) == PLUS
           && GET_CODE (XEXP (op, 0)) == SYMBOL_REF
           && GET_CODE (XEXP (op, 1)) == CONST_INT)){
        return false;
      }
      offset = INTVAL (XEXP (op, 1));
      op = XEXP (op, 0);
      /* FALL THROUGH */
    case SYMBOL_REF:
      if(CONSTANT_POOL_ADDRESS_P (op)){
        size = GET_MODE_SIZE (get_pool_mode(op));
        if((unsigned HOST_WIDE_INT) size > g_switch_value){
          return false;
        }
      }
      else {
        if(!SYMBOL_REF_SMALL_P (op)){
          return false;
        }
        t = SYMBOL_REF_DECL (op);
        if(DECL_P (t)){
          t = DECL_SIZE_UNIT (t);
        }
        else {
          t = TYPE_SIZE_UNIT (TREE_TYPE (t));
        }
        if(t && host_integerp(t, 0)){
          size = tree_low_cst(t, 0);
          if(size < 0){
            size = 0;
          }
        }
      }
      return offset >= 0 && offset <= size;
    default:
      return false;
  }
}




/*-------
Constants
-------*/

/* s16 constant */

int
s16_const_int_operand(rtx op, enum machine_mode mode ATTRIBUTE_UNUSED)
{
  return GET_CODE (op) == CONST_INT && IN_RANGE (INTVAL (op), -32768, 32767);
}




/* s12 constant */

int
s12_const_int_operand(rtx op, enum machine_mode mode ATTRIBUTE_UNUSED)
{
  return GET_CODE (op) == CONST_INT && IN_RANGE (INTVAL (op), -2048, 2047);
}




/* s10 constant */

int
s10_const_int_operand(rtx op, enum machine_mode mode ATTRIBUTE_UNUSED)
{
  return GET_CODE (op) == CONST_INT && IN_RANGE (INTVAL (op), -512, 511);
}




/* s8 constant */

int
s8_const_int_operand(rtx op, enum machine_mode mode ATTRIBUTE_UNUSED)
{
  return GET_CODE (op) == CONST_INT && IN_RANGE (INTVAL (op), -128, 127);
}




/* u9 constant */

int
u9_const_int_operand(rtx op, enum machine_mode mode ATTRIBUTE_UNUSED)
{
  return GET_CODE (op) == CONST_INT && IN_RANGE (INTVAL (op), 0, 511);
}




/* u8 constant */

int
u8_const_int_operand(rtx op, enum machine_mode mode ATTRIBUTE_UNUSED)
{
  return GET_CODE (op) == CONST_INT && IN_RANGE (INTVAL (op), 0, 255);
}




/* u7 constant */

int
u7_const_int_operand(rtx op, enum machine_mode mode ATTRIBUTE_UNUSED)
{
  return GET_CODE (op) == CONST_INT && IN_RANGE (INTVAL (op), 0, 127);
}




/* u6 constant */

int
u6_const_int_operand(rtx op, enum machine_mode mode ATTRIBUTE_UNUSED)
{
  return GET_CODE (op) == CONST_INT && IN_RANGE (INTVAL (op), 0, 63);
}




/* u5 constant */

int
u5_const_int_operand(rtx op, enum machine_mode mode ATTRIBUTE_UNUSED)
{
  return GET_CODE (op) == CONST_INT && IN_RANGE (INTVAL (op), 0, 31);
}




/* u3 constant */

int
u3_const_int_operand(rtx op, enum machine_mode mode ATTRIBUTE_UNUSED)
{
  return GET_CODE (op) == CONST_INT && IN_RANGE (INTVAL (op), 0, 7);
}




/* u2 constant */

int
u2_const_int_operand(rtx op, enum machine_mode mode ATTRIBUTE_UNUSED)
{
  return GET_CODE (op) == CONST_INT && IN_RANGE (INTVAL (op), 0, 3);
}




/* u1 constant */

int
u1_const_int_operand(rtx op, enum machine_mode mode ATTRIBUTE_UNUSED)
{
  return GET_CODE (op) == CONST_INT && IN_RANGE (INTVAL (op), 0, 1);
}




/* u0 constant */

int
zero_constant(rtx op, enum machine_mode mode)
{
  return op == CONST0_RTX (mode);
}




/* m9 signed magnitude constant */

int
m9_const_int_operand(rtx op, enum machine_mode mode ATTRIBUTE_UNUSED)
{
  return GET_CODE (op) == CONST_INT && IN_RANGE (INTVAL (op), -255, 255);
}




/* constant == 2^N where N is an integer */

int
power_of_two_operand(rtx op, enum machine_mode mode ATTRIBUTE_UNUSED)
{
  return GET_CODE (op) == CONST_INT && exact_log2(INTVAL (op)) != -1;
}




/* constant == 2^N where N is an element of {0, 1, 2, 3, 4, 5, 6, 7} */

int
addasl_const_int_operand(rtx op, enum machine_mode mode ATTRIBUTE_UNUSED)
{
  return GET_CODE (op) == CONST_INT && (   INTVAL (op) == (1 << 0)
                                        || INTVAL (op) == (1 << 1)
                                        || INTVAL (op) == (1 << 2)
                                        || INTVAL (op) == (1 << 3)
                                        || INTVAL (op) == (1 << 4)
                                        || INTVAL (op) == (1 << 5)
                                        || INTVAL (op) == (1 << 6)
                                        || INTVAL (op) == (1 << 7));
}




/* constant that might not fit in s16 */

int
immediate_not_s16_operand(rtx op, enum machine_mode mode)
{
  switch(GET_CODE (op)){
    case CONST_INT:
    case CONST_DOUBLE:
    case CONST_VECTOR:
    case CONST:
    case LABEL_REF:
    case SYMBOL_REF:
      return immediate_operand(op, mode) && !s16_const_int_operand(op, mode);
    default:
      return false;
  }
}




/*-----------------
Memory or Registers
-----------------*/

/* non-general purpose register or memory */

int
nongr_reg_or_memory_operand(rtx op, enum machine_mode mode)
{
  return nongr_register_operand(op, mode) || memory_operand(op, mode);
}




/* conditional move destination */

int
conditional_dest_operand(rtx op, enum machine_mode mode)
{
  return !reload_completed ? nonimmediate_operand(op, mode)
                           : (memory_operand(op, mode)
                              && qdsp6_legitimate_address_p(GET_MODE (op),
                                                            XEXP (op, 0),
                                                            true, "cond"))
                             || gr_register_operand(op, mode);
}




/*--------------------
Registers or Constants
--------------------*/

/* conditional add operand */

int
conditional_add_operand(rtx op, enum machine_mode mode)
{
  return !reload_completed ? nonmemory_operand(op, mode)
                           : gr_register_operand(op, mode)
                             || s8_const_int_operand(op, mode);
}




/*-----
General
-----*/

/* conditional move source */

int
conditional_src_operand(rtx op, enum machine_mode mode)
{
  return !reload_completed ? general_operand(op, mode)
                           : (memory_operand(op, mode)
                              && qdsp6_legitimate_address_p(GET_MODE (op),
                                                            XEXP (op, 0),
                                                            true, "cond"))
                             || gr_register_operand(op, mode)
                             || s12_const_int_operand(op, mode);
}




/*-------
Operators
-------*/

/* operator used for predication */

int
predicate_operator(rtx op, enum machine_mode mode ATTRIBUTE_UNUSED)
{
  return GET_CODE (op) == NE || GET_CODE (op) == EQ;
}
#endif /* GCC_3_4_6 */




/*-------------------------------------------
Functions called from the machine description
-------------------------------------------*/

/* Compute the DWARF information for the frame of the current function, used for
   exception handling and debugging. */

static void
qdsp6_compute_dwarf_frame_information(void)
{
  struct qdsp6_frame_info *frame;
  HOST_WIDE_INT offset;
  char *label;
  int i;

  if(!dwarf2out_do_frame()){
    return;
  }

  label = dwarf2out_cfi_label(false);

  frame = qdsp6_frame_info();

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




/* Helper function for qdsp6_expand_prologue

   Allocate stack space by decrementing SP. */

static void
qdsp6_allocate_stack(unsigned HOST_WIDE_INT size, int allocate_stack_insn){
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
qdsp6_expand_prologue(void)
{
  struct qdsp6_frame_info *frame;
  rtx base_reg;
  HOST_WIDE_INT offset;
  unsigned int i;

  frame = qdsp6_frame_info();

  /* Do we need to use the allocframe instruction? */
  if(frame->use_allocframe){
    rtx allocframe_size = gen_int_mode(frame->allocframe_size, SImode);
    emit_insn(GEN_FCN (frame->allocframe_insn)(allocframe_size));
  }

  /* Allocate any remaning stack space. */
  qdsp6_allocate_stack(frame->sp_adjustment, frame->allocate_stack_insn);

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

}




/* Return true if the current function's epilogue consists only of a return
   instruction. */

bool
qdsp6_direct_return(void)
{
  struct qdsp6_frame_info *frame = qdsp6_frame_info();

  return reload_completed && (frame->total_size == 0
                              || (TARGET_V4_FEATURES && frame->use_allocframe
                                                     && frame->reg_size == 0));
}




/* Helper function for qdsp6_expand_epilogue

   Deallocate stack space by incrementing SP. */

static void
qdsp6_deallocate_stack(unsigned HOST_WIDE_INT size){
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
qdsp6_expand_epilogue(bool sibcall)
{
  bool emit_return;
  struct qdsp6_frame_info *frame;
  rtx base_reg;
  HOST_WIDE_INT offset;
  int i;

  emit_return = !sibcall;

  frame = qdsp6_frame_info();

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
    qdsp6_deallocate_stack(frame->sp_adjustment);
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
#define SWAP_OPERANDS op0 = cfun->machine->compare_op1; \
                      op1 = cfun->machine->compare_op0

rtx
qdsp6_expand_compare(enum rtx_code code)
{
  rtx op0 = cfun->machine->compare_op0;
  rtx op1 = cfun->machine->compare_op1;
  enum rtx_code compare_code, jump_code;
  rtx p_reg, const_reg;
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

  /* emit (set (reg:BI p_reg) (compare_code:BI op0 op1)) */
  emit_insn(gen_rtx_SET (VOIDmode, p_reg,
                         gen_rtx_fmt_ee(compare_code, BImode, op0, op1)));

  /* return (eq/ne:BI (reg:BI p_reg) (const_int 0)) */
  return gen_rtx_fmt_ee(jump_code, BImode, p_reg, const0_rtx);
}




/* Creates a tree node for a block-move function named NAME. */

static tree
qdsp6_special_case_memcpy_fn(const char *name)
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
qdsp6_emit_special_case_memcpy_fn(
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
    *fn = qdsp6_special_case_memcpy_fn(name);
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
qdsp6_expand_movmem_inline(rtx operands[], bool volatile_p)
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
      qdsp6_hardware_loop();
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

static GTY(()) tree qdsp6_memcpy_volatile;
static GTY(()) tree qdsp6_memcpy_likely_aligned8_min32_mult8;

/* Emits RTL to perform a block move or returns false.  OPERANDS[0] is a MEM
   containing the destination address.  OPERANDS[1] is a MEM containing the
   source address.  OPERANDS[2] is a CONST_INT containing the number of bytes to
   be copied.  OPERANDS[3] is a CONST_INT containing the guaranteed minimum
   alignment of both the source and destination addresses.  OPERANDS[6] is a
   CONST_INT with a non-zero value only if the block move may be performed via a
   tail call. */

bool
qdsp6_expand_movmem(rtx operands[])
{
  HOST_WIDE_INT length, align;
  int cycles, leftovers;
  bool volatile_p, simple_copy_p;
  const int O3_inline_cycle_threshold = 10;
  const int O2_inline_cycle_threshold = 5;
  const int likely_aligned_cycle_threshold = 100;

  volatile_p = !TARGET_V4_FEATURES
               && (MEM_VOLATILE_P (operands[0]) || MEM_VOLATILE_P (operands[1])
                   || !qdsp6_dual_memory_accesses);

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
    qdsp6_expand_movmem_inline(operands, volatile_p);
    return true;
  }

  if(optimize && !volatile_p
     && (align & 3) == 0 && length >= 32 && length % 8 == 0
     && cycles < likely_aligned_cycle_threshold){
    qdsp6_emit_special_case_memcpy_fn(&qdsp6_memcpy_likely_aligned8_min32_mult8,
                                      "__qdsp_memcpy_likely_aligned_min32bytes_mult8bytes",
                                      operands[0], operands[1], operands[2],
                                      INTVAL (operands[6]));
    return true;
  }

  if(volatile_p){
    qdsp6_emit_special_case_memcpy_fn(&qdsp6_memcpy_volatile, "memcpy_v",
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
qdsp6_expand_setmem(rtx operands[])
{
#define MEMSET_LIBCALL_THRESHOLD 64
  HOST_WIDE_INT align_intval, nbytes_intval, initval_intval;
  rtx destaddr, nbytes, initval, align;

  if (!flag_optimize_memset)
    return false;

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
          qdsp6_hardware_loop();
        }

      /* Count leftover */
      nbytes_left = nbytes_left % GET_MODE_SIZE(curr_mode);
    }
  gcc_assert(nbytes_left == 0);
  return true;
}


#if 0
bool
qdsp6_expand_clrstr(rtx operands[])
{
  rtx str_0, str_reg, str_mem, zero_reg, label;
  int count, loopcount, align;

  align = INTVAL (operands[2]);
  if((align & 3) != 0 || GET_CODE (operands[1]) != CONST_INT){
    return false;
  }

  str_0 = operands[0];
  str_reg = copy_to_mode_reg(SImode, XEXP (str_0, 0));
  count = INTVAL (operands[1]);

  if((align & 7) == 0){

    loopcount = count >> 3;
    if(loopcount){

      zero_reg = gen_reg_rtx(DImode);
      emit_move_insn(gen_highpart(SImode, zero_reg), const0_rtx);
      emit_move_insn(gen_lowpart(SImode, zero_reg), const0_rtx);

      if(loopcount > 3){
        str_mem = gen_rtx_MEM (DImode, str_reg);
        MEM_COPY_ATTRIBUTES (str_mem, str_0);
        label = gen_label_rtx();
        emit_insn(gen_loop0(gen_int_mode(loopcount, SImode), label));
        emit_note(NOTE_INSN_LOOP_BEG);
        emit_label(label);
        emit_move_insn(str_mem, zero_reg);
        emit_insn(gen_addsi3(str_reg, str_reg, gen_int_mode(8, SImode)));
        emit_jump_insn(gen_endloop0(label));
        emit_note(NOTE_INSN_LOOP_END);
      }
      else {
        for(; loopcount; loopcount--){
          str_mem = gen_rtx_MEM (DImode, str_reg);
          MEM_COPY_ATTRIBUTES (str_mem, str_0);
          emit_move_insn(str_mem, zero_reg);
          emit_insn(gen_addsi3(str_reg, str_reg, gen_int_mode(8, SImode)));
        }
      }
    }
    if(count & 4){
      zero_reg = gen_reg_rtx(SImode);
      emit_move_insn(zero_reg, const0_rtx);
      str_mem = gen_rtx_MEM (SImode, str_reg);
      MEM_COPY_ATTRIBUTES (str_mem, str_0);
      emit_move_insn(str_mem, zero_reg);
      emit_insn(gen_addsi3(str_reg, str_reg, gen_int_mode(4, SImode)));
    }

  }
  else {

    loopcount = count >> 2;
    if(loopcount){

      zero_reg = gen_reg_rtx(SImode);
      emit_move_insn(zero_reg, const0_rtx);

      if(loopcount > 3){
        str_mem = gen_rtx_MEM (SImode, str_reg);
        MEM_COPY_ATTRIBUTES (str_mem, str_0);
        label = gen_label_rtx();
        emit_insn(gen_loop0(gen_int_mode(loopcount, SImode), label));
        emit_note(NOTE_INSN_LOOP_BEG);
        emit_label(label);
        emit_move_insn(str_mem, zero_reg);
        emit_insn(gen_addsi3(str_reg, str_reg, gen_int_mode(4, SImode)));
        emit_jump_insn(gen_endloop0(label));
        emit_note(NOTE_INSN_LOOP_END);
      }
      else {
        for(; loopcount; loopcount--){
          str_mem = gen_rtx_MEM (SImode, str_reg);
          MEM_COPY_ATTRIBUTES (str_mem, str_0);
          emit_move_insn(str_mem, zero_reg);
          emit_insn(gen_addsi3(str_reg, str_reg, gen_int_mode(4, SImode)));
        }
      }
    }

  }
  if(count & 2){
    zero_reg = gen_reg_rtx(HImode);
    emit_move_insn(zero_reg, const0_rtx);
    str_mem = gen_rtx_MEM (HImode, str_reg);
    MEM_COPY_ATTRIBUTES (str_mem, str_0);
    emit_move_insn(str_mem, zero_reg);
    emit_insn(gen_addsi3(str_reg, str_reg, gen_int_mode(2, SImode)));
  }
  if(count & 1){
    zero_reg = gen_reg_rtx(QImode);
    emit_move_insn(zero_reg, const0_rtx);
    str_mem = gen_rtx_MEM (QImode, str_reg);
    MEM_COPY_ATTRIBUTES (str_mem, str_0);
    emit_move_insn(str_mem, zero_reg);
  }

  return true;
}




bool
qdsp6_expand_strlen(rtx operands[])
{
  rtx str_reg, str_mem, rtrn_reg, pat_reg, load_reg, p2, p3, cmp_reg, neg_reg, label;
  unsigned int pattern;

  if(INTVAL (operands[3]) != 8){
    return false;
  }

  rtrn_reg = operands[0];
  str_reg = copy_to_mode_reg(SImode, XEXP (operands[1], 0));
  str_mem = gen_rtx_MEM (DImode, str_reg);
  MEM_COPY_ATTRIBUTES (str_mem, operands[1]);
  pattern = INTVAL (operands[2]);
  pattern |= (pattern << 24) | (pattern << 16) | (pattern << 8);
  pat_reg = gen_reg_rtx(DImode);
  load_reg = gen_reg_rtx(DImode);
  cmp_reg = gen_reg_rtx(SImode);
  neg_reg = gen_reg_rtx(SImode);
  p2 = gen_raw_REG (BImode, P2_REGNUM);
  p3 = gen_raw_REG (BImode, P3_REGNUM);

  emit_move_insn(rtrn_reg, gen_int_mode(23, SImode));  /* 23 == -8 + 31 */
  if(pattern != 0){
    emit_move_insn(gen_highpart(SImode, pat_reg), gen_int_mode(pattern, SImode));
    emit_move_insn(gen_lowpart(SImode, pat_reg), gen_int_mode(pattern, SImode));
  }

  label = gen_label_rtx();

  emit_note(NOTE_INSN_LOOP_BEG);
  emit_label(label);
  if(pattern == 0){
    emit_move_insn(pat_reg, const0_rtx);
  }
  emit_move_insn(load_reg, str_mem);
  emit_insn(gen_addsi3(str_reg, str_reg, gen_int_mode(8, SImode)));
  emit_insn(gen_addsi3(rtrn_reg, rtrn_reg, gen_int_mode(8, SImode)));
  emit_insn(gen_vcmpb_eq(p3, load_reg, pat_reg));
  emit_insn(gen_any8(p2, p3));
  emit_insn(gen_move_predicate_to_reg(cmp_reg, p3));
  emit_jump_insn(gen_jump_if_false(p2, label));
  emit_note(NOTE_INSN_LOOP_END);
  emit_insn(gen_negsi2(neg_reg, cmp_reg));
  emit_insn(gen_andsi3(cmp_reg, cmp_reg, neg_reg));
  emit_insn(gen_clzsi2(cmp_reg, cmp_reg));
  emit_insn(gen_subsi3(rtrn_reg, rtrn_reg, cmp_reg));

  return true;
}




/* not currently working */

bool
qdsp6_expand_cmpstr(rtx operands[])
{
  rtx rtrn, str0_addr, str0_mem, str0, str1_addr, str1_mem, str1;
  rtx gt_rtrn, lt_rtrn, null, end, nend, equal, nequal, grtr, ngrtr;
  rtx p0, p1, p2, p3, label0, label1, label2;

  fputs("\ncmpstr\n", stderr);
  debug_rtx(operands[0]);
  debug_rtx(operands[1]);
  debug_rtx(operands[2]);
  debug_rtx(operands[3]);
  debug_rtx(operands[4]);
  fputc('\n', stderr);

  if(INTVAL (operands[4]) != 8){
    return false;
  }

  rtrn = operands[0];
  str0_addr = copy_to_mode_reg(SImode, XEXP (operands[1], 0));
  str0_mem = gen_rtx_MEM (DImode, str0_addr);
  MEM_COPY_ATTRIBUTES (str0_mem, operands[1]);
  str0 = gen_reg_rtx(DImode);
  str1_addr = copy_to_mode_reg(SImode, XEXP (operands[2], 0));
  str1_mem = gen_rtx_MEM (DImode, str1_addr);
  MEM_COPY_ATTRIBUTES (str1_mem, operands[1]);
  str1 = gen_reg_rtx(DImode);
  gt_rtrn = gen_reg_rtx(SImode);
  lt_rtrn = gen_reg_rtx(SImode);
  null = gen_reg_rtx(DImode);
  end = gen_reg_rtx(SImode);
  nend = gen_reg_rtx(SImode);
  equal = gen_reg_rtx(SImode);
  nequal = gen_reg_rtx(SImode);
  grtr = gen_reg_rtx(SImode);
  ngrtr = gen_reg_rtx(SImode);
  p0 = gen_raw_REG (BImode, P0_REGNUM);
  p1 = gen_raw_REG (BImode, P1_REGNUM);
  p2 = gen_raw_REG (BImode, P2_REGNUM);
  p3 = gen_raw_REG (BImode, P3_REGNUM);
  label0 = gen_label_rtx();
  label1 = gen_label_rtx();
  label2 = gen_label_rtx();

  emit_note(NOTE_INSN_LOOP_BEG);
  emit_label(label0);
  emit_move_insn(null, const0_rtx);
  emit_move_insn(str0, str0_mem);
  emit_insn(gen_addsi3(str0_addr, str0_addr, gen_int_mode(8, SImode)));
  emit_move_insn(str1, str1_mem);
  emit_insn(gen_addsi3(str1_addr, str1_addr, gen_int_mode(8, SImode)));
  emit_insn(gen_vcmpb_eq(p0, str0, str1));
  emit_insn(gen_vcmpb_eq(p1, str1, null));
  emit_move_insn(gt_rtrn, const1_rtx);
  emit_move_insn(lt_rtrn, constm1_rtx);
  emit_move_insn(rtrn, const0_rtx);
  emit_insn(gen_all8(p2, p0));
  emit_jump_insn(gen_jump_if_false(p2, label1));
  emit_insn(gen_any8(p3, p1));
  emit_jump_insn(gen_jump_if_false(p3, label0));
  emit_note(NOTE_INSN_LOOP_END);
  emit_jump_insn(gen_jump(label2));
  emit_label(label1);
  emit_insn(gen_move_predicate_to_reg(end, p1));
  emit_insn(gen_addsi3(end, end, gen_int_mode(256, SImode)));
  emit_insn(gen_move_predicate_to_reg(equal, p0));
  emit_insn(gen_vcmpb_gtu(p0, str0, str1));
  emit_insn(gen_negsi2(nend, end));
  emit_insn(gen_one_cmplsi2(nequal, equal));
  emit_insn(gen_addsi3(equal, equal, const1_rtx));
  emit_insn(gen_move_predicate_to_reg(grtr, p0));
  emit_insn(gen_andsi3(end, end, nend));
  emit_insn(gen_andsi3(equal, equal, nequal));
  emit_insn(gen_negsi2(ngrtr, grtr));
  emit_insn(gen_cmp_gtu(p0, equal, end));
  emit_insn(gen_andsi3(grtr, grtr, ngrtr));
  emit_insn(gen_cmp_eq(p1, equal, grtr));
  emit_jump_insn(gen_jump_if_true(p0, label2));
  emit_insn(gen_muxt(rtrn, p1, gt_rtrn, lt_rtrn));
  emit_label(label2);

  return true;
}
#endif /* 0 */




void
qdsp6_hardware_loop(void)
{
  cfun->machine->has_hardware_loops++;
}




/*--------------------------------------------
Functions for forming and manipulating packets
--------------------------------------------*/

struct GTY((chain_next ("%h.next"))) qdsp6_reg_access {
  unsigned int regno;
  int flags;
  struct qdsp6_reg_access *next;
};

struct GTY((chain_next ("%h.next"))) qdsp6_mem_access {
  rtx mem;
  int flags;
  struct qdsp6_mem_access *next;
};

struct GTY(()) qdsp6_insn_info {
  rtx insn;
  struct qdsp6_reg_access *reg_reads;
  struct qdsp6_reg_access *reg_writes;
  struct qdsp6_mem_access *loads;
  struct qdsp6_mem_access *stores;
  int flags;
};

struct GTY((chain_prev ("%h.prev"), chain_next ("%h.next"))) qdsp6_packet_info {
  struct qdsp6_insn_info *insns[QDSP6_MAX_INSNS_PER_PACKET];
  int num_insns;
  struct qdsp6_packet_info *prev;
  struct qdsp6_packet_info *next;
};

struct GTY((chain_next ("%h.next"))) qdsp6_bb_aux_info {
  struct qdsp6_packet_info *head_packet;
  struct qdsp6_packet_info *end_packet;
  struct qdsp6_bb_aux_info *next;
};

#define QDSP6_BB_AUX(BB) ((struct qdsp6_bb_aux_info *) (BB->aux))
#define BB_HEAD_PACKET(BB) (QDSP6_BB_AUX (BB)->head_packet)
#define BB_END_PACKET(BB) (QDSP6_BB_AUX (BB)->end_packet)

enum qdsp6_transformation_type {
  QDSP6_DOT_NEWIFY /* 0 */
};

struct GTY((chain_next ("%h.next"))) qdsp6_insn_transformation_list {
  enum qdsp6_transformation_type type;
  union qdsp6_transformation_union {
    struct qdsp6_dot_newify {
      rtx predicate;
    } GTY((tag ("0"))) dot_newify;
  } GTY((desc ("%1.type"))) info;
  struct qdsp6_insn_transformation_list *next;
};

struct GTY((chain_next ("%h.prev"))) qdsp6_transformed_insn_stack {
  struct qdsp6_insn_info *insn;
  struct qdsp6_packet_info *packet;
  struct qdsp6_transformed_insn_stack *prev;
};




void qdsp6_print_insn_info(FILE *file, struct qdsp6_insn_info *insn_info);
void qdsp6_debug_insn_info(struct qdsp6_insn_info *insn_info);
void qdsp6_print_packet(FILE *file, struct qdsp6_packet_info *packet);
void qdsp6_print_packets(FILE *file, struct qdsp6_packet_info *packet);
void qdsp6_debug_packet(struct qdsp6_packet_info *packet);
void qdsp6_print_bb_packets(FILE *file, basic_block bb);
void qdsp6_debug_bb_packets(basic_block bb);

static bool qdsp6_wandered_too_far_p(rtx insn);
static int  qdsp6_get_flags(rtx insn);
static int  qdsp6_record_writes(rtx *x, void *insn_info);
static int  qdsp6_record_reads(rtx *x, void *insn_info);
static struct qdsp6_insn_info *qdsp6_get_insn_info(rtx insn);
static struct qdsp6_packet_info *qdsp6_start_new_packet(
                                   struct qdsp6_insn_info *insn_info);
static void qdsp6_create_bb_sentinel_packet(struct qdsp6_packet_info *packet);
static void qdsp6_remove_insn_from_packet(
              struct qdsp6_packet_info *packet,
              struct qdsp6_insn_info *insn_info);
static void qdsp6_add_insn_to_packet(
              struct qdsp6_packet_info *packet,
              struct qdsp6_insn_info *insn_info);
static bool qdsp6_control_conflict_p(
              struct qdsp6_insn_info *first,
              struct qdsp6_insn_info *second);
static bool qdsp6_predicable(struct qdsp6_insn_info *insn_info);
static bool qdsp6_dot_newable(struct qdsp6_insn_info *insn_info);
static bool qdsp6_prologue_insn_p(struct qdsp6_insn_info *insn_info);
static void qdsp6_insns_truly_dependent(
              struct qdsp6_insn_info *writer,
              struct qdsp6_insn_info *reader,
              int *dependence);
static void qdsp6_insns_output_dependent(
              struct qdsp6_insn_info *insn0,
              struct qdsp6_insn_info *insn1,
              int *dependence);
static void qdsp6_insns_anti_dependent(
              struct qdsp6_insn_info *earlier,
              struct qdsp6_insn_info *later,
              int *dependence);
static void qdsp6_packet_insn_dependence(
              struct qdsp6_packet_info *packet,
              struct qdsp6_insn_info *insn_info,
              bool ignore_jump,
              int *dependence);
static void qdsp6_packet_insn_internal_dependence(
              struct qdsp6_packet_info *packet,
              struct qdsp6_insn_info *insn_info,
              int *dependence);
static struct qdsp6_insn_info *qdsp6_copy_insn_info(
                                 struct qdsp6_insn_info *insn_info);
static struct qdsp6_insn_info *qdsp6_predicate_insn(
                                 struct qdsp6_insn_info *insn_info,
                                 struct qdsp6_insn_info *jump_insn_info,
                                 bool invert_condition);
static int qdsp6_dot_newify_reg(rtx *x, void *y);
static struct qdsp6_insn_info *qdsp6_dot_newify_insn(
                                 struct qdsp6_insn_info *insn_info);
static rtx  qdsp6_bb_real_head_insn(basic_block bb);
static rtx  qdsp6_bb_real_end_insn(basic_block bb);
static void qdsp6_pack_insns(void);
static void qdsp6_push_insn(
              struct qdsp6_insn_info *insn,
              struct qdsp6_packet_info *packet);
static struct qdsp6_insn_info *qdsp6_pop_insn(void);
static bool qdsp6_insn_fits_in_packet(
              struct qdsp6_insn_info *insn,
              struct qdsp6_packet_info *packet);
static void qdsp6_move_insn(
              struct qdsp6_insn_info *old_insn,
              struct qdsp6_packet_info *from_packet,
              struct qdsp6_insn_info *new_insn,
              struct qdsp6_packet_info *to_packet);
static void qdsp6_sanity_check_cfg_packet_info(void);
static void qdsp6_pull_up_insns(void);
static void qdsp6_init_packing_info(void);
static void qdsp6_free_packing_info(void);




#define QDSP6_MASK(WIDTH, LOW) (((1 << (WIDTH)) - 1) << (LOW))

#define QDSP6_PREDICATE_NUMBER_MASK QDSP6_MASK(2, 0)
#define QDSP6_DOT_NEW               QDSP6_MASK(1, 2)
#define QDSP6_IF_TRUE               QDSP6_MASK(1, 3)
#define QDSP6_IF_FALSE              QDSP6_MASK(1, 4)
#define QDSP6_PREDICATE_MASK \
  (QDSP6_PREDICATE_NUMBER_MASK | QDSP6_DOT_NEW)
#define QDSP6_CONDITION_MASK        (QDSP6_IF_TRUE | QDSP6_IF_FALSE)
#define QDSP6_UNCONDITIONAL         QDSP6_CONDITION_MASK

#define QDSP6_DIRECT_JUMP           QDSP6_MASK(1, 5)
#define QDSP6_INDIRECT_JUMP         QDSP6_MASK(1, 6)
#define QDSP6_ENDLOOP               QDSP6_MASK(1, 7)
#define QDSP6_CALL                  QDSP6_MASK(1, 8)
#define QDSP6_EMULATION_CALL        QDSP6_MASK(1, 9)
#define QDSP6_CONTROL (QDSP6_CALL | QDSP6_JUMP)

#define QDSP6_MEM                   QDSP6_MASK(1, 10)
#define QDSP6_VOLATILE              QDSP6_MASK(1, 11)

#define QDSP6_WANDERED              QDSP6_MASK(1, 12)
#define QDSP6_REGCOND_JUMP          QDSP6_MASK(1, 13)

#define QDSP6_JUMP \
  (QDSP6_DIRECT_JUMP | QDSP6_INDIRECT_JUMP | QDSP6_ENDLOOP  | QDSP6_REGCOND_JUMP) 

#define QDSP6_PREDICATE_NUMBER(INSN) \
  ((INSN)->flags & QDSP6_PREDICATE_NUMBER_MASK)
#define QDSP6_PREDICATE(INSN) ((INSN)->flags & QDSP6_PREDICATE_MASK)
#define QDSP6_DOT_NEW_P(INSN) (((INSN)->flags & QDSP6_DOT_NEW) != 0)
#define QDSP6_CONDITION(INSN) ((INSN)->flags & QDSP6_CONDITION_MASK)
#define QDSP6_CONFLICT_P(ACCESS0, ACCESS1) \
  (gcc_assert(QDSP6_CONDITION (ACCESS0) && QDSP6_CONDITION (ACCESS1)), \
   ((ACCESS0)->flags & (ACCESS1)->flags & QDSP6_CONDITION_MASK \
    || QDSP6_PREDICATE (ACCESS0) != QDSP6_PREDICATE (ACCESS1)))

#define QDSP6_DIRECT_JUMP_P(INSN)    (((INSN)->flags & QDSP6_DIRECT_JUMP) != 0)
#define QDSP6_INDIRECT_JUMP_P(INSN)  (((INSN)->flags & QDSP6_INDIRECT_JUMP) != 0)
#define QDSP6_ENDLOOP_P(INSN)        (((INSN)->flags & QDSP6_ENDLOOP) != 0)
#define QDSP6_CALL_P(INSN)           (((INSN)->flags & QDSP6_CALL) != 0)
#define QDSP6_EMULATION_CALL_P(INSN) (((INSN)->flags & QDSP6_EMULATION_CALL) != 0)
#define QDSP6_JUMP_P(INSN)           (((INSN)->flags & QDSP6_JUMP) != 0)
#define QDSP6_CONTROL_P(INSN)        (((INSN)->flags & QDSP6_CONTROL) != 0)

#define QDSP6_MEM_P(INSN)      (((INSN)->flags & QDSP6_MEM) != 0)
#define QDSP6_VOLATILE_P(INSN) (((INSN)->flags & QDSP6_VOLATILE) != 0)

#define QDSP6_WANDERED_P(INSN) (((INSN)->flags & QDSP6_WANDERED) != 0)

/* PDB. True if ((insn_info*)INSN)->insn is a register conditional jump */
#define QDSP6_REGCOND_JUMP_P(INSN) (((INSN)->flags & QDSP6_REGCOND_JUMP) != 0)

#define QDSP6_CONFLICT_P(ACCESS0, ACCESS1) \
  (gcc_assert(QDSP6_CONDITION (ACCESS0) && QDSP6_CONDITION (ACCESS1)), \
   ((ACCESS0)->flags & (ACCESS1)->flags & QDSP6_CONDITION_MASK \
    || QDSP6_PREDICATE (ACCESS0) != QDSP6_PREDICATE (ACCESS1)))

/* PDB. Register conditional jump is also a conditional jump */
#define QDSP6_CONDITIONAL_P(INSN) \
  ((((INSN)->flags & QDSP6_CONDITION_MASK) != QDSP6_UNCONDITIONAL) || \
  (((INSN)->flags & QDSP6_REGCOND_JUMP) != 0))

#define QDSP6_DEP_NONE            0
#define QDSP6_DEP_UNCONDITIONAL   QDSP6_MASK(1, 0)
#define QDSP6_DEP_NOT_DOT_NEWABLE QDSP6_MASK(1, 1)
#define QDSP6_DEP_DOT_NEWABLE     QDSP6_MASK(1, 2)
/* PDB. Dual jump is a new special kind of dependence between two instructions. */
#define QDSP6_DEP_DUALJUMP        QDSP6_MASK(1, 3)

#define QDSP6_DEP_NONE_P(DEP) ((DEP) == 0)
#define QDSP6_DEP_UNCONDITIONAL_P(DEP) (((DEP) & QDSP6_DEP_UNCONDITIONAL) != 0)
#define QDSP6_DEP_NOT_DOT_NEWABLE_P(DEP) \
  (((DEP) & QDSP6_DEP_NOT_DOT_NEWABLE) != 0)
#define QDSP6_DEP_DOT_NEWABLE_P(DEP) (((DEP) & QDSP6_DEP_DOT_NEWABLE) != 0)
/* PDB. True if the dependence DEP is a dual jump dependence. Put the instructions that depend in terms of DEP in one packet. */
#define QDSP6_DEP_DUALJUMP_P(DEP) (((DEP) & QDSP6_DEP_DUALJUMP) != 0)




static bool final_packing = false;
static state_t qdsp6_state;

static GTY(()) struct qdsp6_packet_info *qdsp6_head_packet;
static GTY(()) struct qdsp6_packet_info *qdsp6_tail_packet;
static GTY(()) struct qdsp6_bb_aux_info *qdsp6_head_bb_aux;
static GTY(()) struct qdsp6_transformed_insn_stack *qdsp6_insn_stack;




void
qdsp6_print_insn_info(FILE *file, struct qdsp6_insn_info *insn_info)
{
  struct qdsp6_reg_access *reg_access;
  struct qdsp6_mem_access *mem_access;
  bool first;

  if(insn_info == NULL){
    fputs("!!!! NULL INSN_INFO !!!!\n", file);
    return;
  }

  fputs(";; condition: ", file);
  if(QDSP6_CONDITION (insn_info) == QDSP6_UNCONDITIONAL){
    fputs("unconditional", file);
  }
  else if(QDSP6_CONDITION (insn_info) == 0){
    fputs("never", file);
  }
  else {
    if(QDSP6_CONDITION (insn_info) == QDSP6_IF_FALSE){
      fputc('!', file);
    }
    fputs(reg_names[P0_REGNUM + QDSP6_PREDICATE_NUMBER (insn_info)], file);
    if(QDSP6_DOT_NEW_P (insn_info)){
      fputs(".new", file);
    }
  }
  fputc('\n', file);

  fputs(";; control: ", file);
  if(QDSP6_CONTROL_P (insn_info)){
    if(QDSP6_DIRECT_JUMP_P (insn_info)){
      fputs("jump", file);
    }
    if(QDSP6_INDIRECT_JUMP_P (insn_info)){
      fputs("indirect jump", file);
    }
    if(QDSP6_CALL_P (insn_info)){
      fputs("call", file);
    }
    if(QDSP6_ENDLOOP_P (insn_info)){
      fputs("endloop", file);
    }
  }
  else {
    fputs("none", file);
  }
  fputc('\n', file);

  fputs(";; flags: (", file);
  first = true;
  if(QDSP6_EMULATION_CALL_P (insn_info)){
    fputs("emulation_call", file);
    first = false;
  }
  if(QDSP6_VOLATILE_P (insn_info)){
    if(!first){
      fputs(", ", file);
    }
    fputs("volatile", file);
    first = false;
  }
  if(QDSP6_MEM_P (insn_info)){
    if(!first){
      fputs(", ", file);
    }
    fputs("mem", file);
    first = false;
  }
  if(QDSP6_WANDERED_P (insn_info)){
    if(!first){
      fputs(", ", file);
    }
    fputs("wandered", file);
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
qdsp6_debug_insn_info(struct qdsp6_insn_info *insn_info)
{
  qdsp6_print_insn_info(stderr, insn_info);
}




void
qdsp6_print_packet(FILE *file, struct qdsp6_packet_info *packet)
{
  int i;

  if(packet == NULL){
    fputs("!!!! NULL PACKET !!!!\n", file);
    return;
  }

  fputs(";; ==== BEGIN PACKET ====\n", file);
  for(i = 0; i < packet->num_insns && i < QDSP6_MAX_INSNS_PER_PACKET; i++){
    qdsp6_print_insn_info(file, packet->insns[i]);
  }
  fputs(";; ==== END PACKET ====\n", file);
}




void
qdsp6_print_packets(FILE *file, struct qdsp6_packet_info *packet)
{
  if(packet == NULL){
    qdsp6_print_packet(file, packet);
    return;
  }

  do {
    qdsp6_print_packet(file, packet);
    packet = packet->next;
  }while(packet);
}




void
qdsp6_debug_packet(struct qdsp6_packet_info *packet)
{
  qdsp6_print_packet(stderr, packet);
}




void
qdsp6_print_bb_packets(FILE *file, basic_block bb)
{
#if !GCC_3_4_6
  struct qdsp6_packet_info *packet;

  dump_bb_info(bb, true, false, TDF_DETAILS, ";; ", file);
  packet = BB_HEAD_PACKET (bb);
  if(packet){
    fputs("\n;; sentinel packet:\n", file);
    qdsp6_print_packet(file, packet->prev);
  }
  fputc('\n', file);
  while(packet && packet != BB_END_PACKET (bb)){
    qdsp6_print_packet(file, packet);
    packet = packet->next;
  }
  qdsp6_print_packet(file, packet);
  dump_bb_info(bb, false, true, TDF_DETAILS, ";; ", file);
  fputs("\n\n", file);
#endif /* !GCC_3_4_6 */
}




void
qdsp6_debug_bb_packets(basic_block bb)
{
#if !GCC_3_4_6
  qdsp6_print_bb_packets(stderr, bb);
#endif /* !GCC_3_4_6 */
}




/* Return true if INSN references a label out of range and consequently was
   expanded into multiple dependent instructions. */

static bool
qdsp6_wandered_too_far_p(rtx insn)
{
  if(!final_packing){
    return false;
  }

  switch(INSN_CODE (insn)){
    case CODE_FOR_cond_jump:
    case CODE_FOR_loop0:
    case CODE_FOR_loop1:
    case CODE_FOR_gpr_cond_jump:
      if(get_attr_length(insn) > 4){
        return true;
      }
      else {
        return false;
      }
    default:
      return false;
  }
}




/* Return true if TEST is a valid relational operator for a conditional jump */
static int
qdsp6_cond_jump_compare_operator (rtx test)
{
  enum rtx_code code = GET_CODE (test);
  /* v3 has more compare codes because of the register conditional jumps. */
  if (TARGET_V3_FEATURES)
    return (code == NE || code == EQ || code == LE || code == GE || code == GT || code == LT);
  else
    return (code == NE || code == EQ);
}




static int
qdsp6_get_flags(rtx insn)
{
  int flags;
  rtx pattern;
  rtx test;

  flags = 0;

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
      flags |= QDSP6_ENDLOOP;
      test = NULL_RTX;
    }
  }
  else {
    test = NULL_RTX;
  }

  if(test){
    if (TARGET_V3_FEATURES)
      gcc_assert (qdsp6_cond_jump_compare_operator (test)
		  && XEXP (test,1 ) == const0_rtx);
    else
      gcc_assert(qdsp6_cond_jump_compare_operator (test)
               && P_REG_P (XEXP (test, 0))
               && XEXP (test, 1) == const0_rtx);
    if (P_REG_P (XEXP (test, 0)))
      {
	flags |= REGNO (XEXP (test, 0)) - P0_REGNUM;
	flags |= GET_CODE (test) == NE ? QDSP6_IF_TRUE : QDSP6_IF_FALSE;
      }
    else
      {
	/* This is a speculative-register-conditional jump. */
	flags |= QDSP6_REGCOND_JUMP;

	/* PDB.  **IMPORTANT**.This really is a condition instruction, but here it means that it is not 
	   predicated on a predicate register. To check whether an instruction is conditional
	   use QDSP6_CONDITIONAL_P, _not_ QDSP6_UNCONDITIONAL. The latter only tell us if a '!'
	   needs to be added before a predicate register, if used. */
	flags |= QDSP6_UNCONDITIONAL;
      }
  }
  else {
    flags |= QDSP6_UNCONDITIONAL;
  }

  if(JUMP_P (insn) && !(flags & QDSP6_ENDLOOP)){
    if(GET_CODE (pattern) == SET){
      if(GET_CODE (SET_SRC (pattern)) == IF_THEN_ELSE){
        if(GET_CODE (XEXP (SET_SRC (pattern), 1)) == LABEL_REF){
          flags |= QDSP6_DIRECT_JUMP;
        }
        else {
          flags |= QDSP6_INDIRECT_JUMP;
        }
      }
      else {
        if(GET_CODE (SET_SRC (pattern)) == LABEL_REF){
          flags |= QDSP6_DIRECT_JUMP;
        }
        else {
          flags |= QDSP6_INDIRECT_JUMP;
        }
      }
    }
  }
  else if(CALL_P (insn)){
    flags |= QDSP6_CALL;
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
    flags |= QDSP6_EMULATION_CALL;
  }

  if(qdsp6_wandered_too_far_p(insn)){
    flags |= QDSP6_WANDERED;
  }

  return flags;
}




static int
qdsp6_record_writes(rtx *y, void *info)
{
  rtx x;
  struct qdsp6_insn_info *insn_info;
  struct qdsp6_reg_access *reg_access;
  struct qdsp6_mem_access *mem_access;
  unsigned int regno;
  unsigned int next_hard_regno;

  x = *y;
  insn_info = (struct qdsp6_insn_info *) info;

  switch(GET_CODE (x)){
    case MEM:
      mem_access = ggc_alloc_cleared(sizeof(struct qdsp6_mem_access));
      mem_access->mem = x;
      mem_access->flags = insn_info->flags;
      mem_access->next = insn_info->stores;
      insn_info->stores = mem_access;
      insn_info->flags |= QDSP6_MEM;
      if(MEM_VOLATILE_P (x)){
        insn_info->flags |= QDSP6_VOLATILE;
      }
      for_each_rtx(&XEXP (x, 0), qdsp6_record_reads, insn_info);
      return -1;
    case REG:
      regno = REGNO (x);
      next_hard_regno = regno + HARD_REGNO_NREGS (regno, GET_MODE (x));
      for(; regno < next_hard_regno; regno++){
        reg_access = ggc_alloc_cleared(sizeof(struct qdsp6_reg_access));
        reg_access->regno = PN_REGNO_P (regno) ? regno - DOT_NEW_OFFSET : regno;
        reg_access->flags = insn_info->flags;
        reg_access->next = insn_info->reg_writes;
        insn_info->reg_writes = reg_access;
      }
      return 0;
    default:
      return 0;
  }
}




static int
qdsp6_record_reads(rtx *y, void *info)
{
  rtx x;
  struct qdsp6_insn_info *insn_info;
  struct qdsp6_reg_access *reg_access;
  struct qdsp6_mem_access *mem_access;
  int saved_flags;
  unsigned int regno;
  unsigned int next_hard_regno;

  x = *y;
  insn_info = (struct qdsp6_insn_info *) info;

  switch(GET_CODE (x)){
    case COND_EXEC:
      saved_flags = insn_info->flags;
      insn_info->flags = QDSP6_UNCONDITIONAL;
      for_each_rtx(&COND_EXEC_TEST (x), qdsp6_record_reads, insn_info);
      insn_info->flags = saved_flags;
      for_each_rtx(&COND_EXEC_CODE (x), qdsp6_record_reads, insn_info);
      return -1;
    case SET:
    case POST_MODIFY:
      if(GET_CODE (XEXP (x, 1)) != CALL){
        for_each_rtx(&XEXP (x, 0), qdsp6_record_writes, insn_info);
      }
      for_each_rtx(&XEXP (x, 1), qdsp6_record_reads, insn_info);
      return -1;
    case CALL:
      gcc_assert(MEM_P (XEXP (x, 0)));
      for_each_rtx(&XEXP (XEXP (x, 0), 0), qdsp6_record_reads, insn_info);
      return -1;
    case CLOBBER:
      for_each_rtx(&XEXP (x, 0), qdsp6_record_writes, insn_info);
      return -1;
    case POST_DEC:
    case POST_INC:
      for_each_rtx(&XEXP (x, 0), qdsp6_record_writes, insn_info);
      return 0;
    case MEM:
      mem_access = ggc_alloc_cleared(sizeof(struct qdsp6_mem_access));
      mem_access->mem = x;
      mem_access->flags = insn_info->flags;
      mem_access->next = insn_info->loads;
      insn_info->loads = mem_access;
      insn_info->flags |= QDSP6_MEM;
      if(MEM_VOLATILE_P (x)){
        insn_info->flags |= QDSP6_VOLATILE;
      }
      return 0;
    case REG:
      regno = REGNO (x);
      next_hard_regno = regno + HARD_REGNO_NREGS (regno, GET_MODE (x));
      for(; regno < next_hard_regno; regno++){
        reg_access = ggc_alloc_cleared(sizeof(struct qdsp6_reg_access));
        reg_access->regno = PN_REGNO_P (regno) ? regno - DOT_NEW_OFFSET : regno;
        reg_access->flags = insn_info->flags;
        reg_access->next = insn_info->reg_reads;
        insn_info->reg_reads = reg_access;
      }
      return 0;
    case RETURN:
      if(!QDSP6_CALL_P (insn_info)){
        reg_access = ggc_alloc_cleared(sizeof(struct qdsp6_reg_access));
        reg_access->regno = LINK_REGNUM;
        reg_access->flags = insn_info->flags;
        reg_access->next = insn_info->reg_reads;
        insn_info->reg_reads = reg_access;
      }
      return 0;
    default:
      return 0;
  }
}




static struct qdsp6_insn_info *
qdsp6_get_insn_info(rtx insn)
{
  struct qdsp6_insn_info *insn_info;

  insn_info = ggc_alloc_cleared(sizeof(struct qdsp6_insn_info));

  insn_info->insn = insn;
  insn_info->flags = qdsp6_get_flags(insn);

  for_each_rtx(&PATTERN (insn), qdsp6_record_reads, insn_info);

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
      insn_info->flags |= QDSP6_MEM;
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
qdsp6_replace_transfer_map(VEC(rtx, gc)* transfer_source, unsigned orig_reg, 
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
qdsp6_register_copy_word_p (rtx insn)
{
  rtx reg_copy;
  bool dest_reg, src_reg_imm;
  if (!insn || (!(reg_copy = single_set(insn))))
    {
      return false;
    }
  
  dest_reg = register_operand(SET_DEST (reg_copy), SImode);
  src_reg_imm = register_operand(SET_SRC (reg_copy), SImode) || 
    const_int_operand(SET_SRC (reg_copy), SImode);

  return (dest_reg && src_reg_imm);
}

/* Predicate that checks if REG is a lower component of a pair register */
#define QDSP6_LOWER_PAIR(REG)         (!(REG & 0x1))


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
qdsp6_local_combine_pass(void) 
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
	  struct qdsp6_insn_info *insn_info;
	  struct qdsp6_reg_access *read;
	  struct qdsp6_reg_access *write;

	  /* Only process instructions */
	  if (!INSN_P(insn)) 
	    {
	      continue;
	    }
	  insn_info = qdsp6_get_insn_info(insn);

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
	  

	  if (qdsp6_register_copy_word_p (insn))
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
	      qdsp6_replace_transfer_map (transfer_source, dest_regno, NULL_RTX);
	      
	      /* Get the pair register for dest_regno */
	      dest_pair_regno = get_pair_reg(dest_regno);
	      if ((dest_pair_insn = VEC_index(rtx, transfer_source, dest_pair_regno)))
		{
		  enum machine_mode dummy_mode;
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
		      if (QDSP6_LOWER_PAIR (dest_regno))
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
	    } /* qdsp6_is_register_copy */
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
			qdsp6_replace_transfer_map (transfer_source, i, NULL_RTX);
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
		  qdsp6_replace_transfer_map(transfer_source, defined_reg, NULL_RTX); 
		}
	    }
	}
    }
}


static struct qdsp6_packet_info *
qdsp6_start_new_packet(struct qdsp6_insn_info *insn_info)
{
  struct qdsp6_packet_info *new_packet;

  gcc_assert(insn_info);

  state_reset(qdsp6_state);
  state_transition(qdsp6_state, insn_info->insn);

  new_packet = ggc_alloc_cleared(sizeof(struct qdsp6_packet_info));

  if(qdsp6_head_packet == NULL){
    qdsp6_head_packet = new_packet;
  }
  else {
    gcc_assert(qdsp6_tail_packet);
    qdsp6_tail_packet->next = new_packet;
    new_packet->prev = qdsp6_tail_packet;
  }
  qdsp6_tail_packet = new_packet;

  return new_packet;
}




static void
qdsp6_create_bb_sentinel_packet(struct qdsp6_packet_info *packet)
{
  struct qdsp6_packet_info *sentinel_packet;
  struct qdsp6_insn_info *sentinel_insn;

  sentinel_packet = ggc_alloc_cleared(sizeof(struct qdsp6_packet_info));
  sentinel_insn = ggc_alloc_cleared(sizeof(struct qdsp6_insn_info));

  sentinel_insn->insn = PREV_INSN (packet->insns[0]->insn);
  sentinel_packet->insns[0] = sentinel_insn;
  sentinel_packet->num_insns = 1;
  sentinel_packet->prev = packet->prev;
  sentinel_packet->next = packet;

  if(packet->prev){
    packet->prev->next = sentinel_packet;
  }
  else {
    qdsp6_head_packet = sentinel_packet;
  }
  packet->prev = sentinel_packet;
}




static void
qdsp6_remove_insn_from_packet(
  struct qdsp6_packet_info *packet,
  struct qdsp6_insn_info *insn_info
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




static void
qdsp6_add_insn_to_packet(
  struct qdsp6_packet_info *packet,
  struct qdsp6_insn_info *insn_info
)
{
  if(packet->num_insns == 0){
    PUT_MODE (insn_info->insn, TImode);
    packet->insns[0] = insn_info;
  }
  else {
    if(JUMP_P (packet->insns[packet->num_insns - 1]->insn)
       && !JUMP_P (insn_info->insn)){
      if(packet->num_insns == 1){
        PUT_MODE (insn_info->insn, TImode);
        PUT_MODE (packet->insns[0]->insn, VOIDmode);
      }
      else {
        PUT_MODE (insn_info->insn, VOIDmode);
      }
      packet->insns[packet->num_insns] = packet->insns[packet->num_insns - 1];
      packet->insns[packet->num_insns - 1] = insn_info;
    }
    else {
      PUT_MODE (insn_info->insn, VOIDmode);
      packet->insns[packet->num_insns] = insn_info;
    }
  }

  gcc_assert(packet->num_insns < QDSP6_MAX_INSNS_PER_PACKET);
  packet->num_insns++;
}




static bool
qdsp6_control_conflict_p(
  struct qdsp6_insn_info *first,
  struct qdsp6_insn_info *second
)
{
  if(!QDSP6_CONTROL_P (first) || !QDSP6_CONTROL_P (second)){
    return false;
  }

  if(!TARGET_V2_FEATURES){
    return true;
  }

  if(QDSP6_CONDITIONAL_P (first)
     && !QDSP6_DOT_NEW_P (first) && QDSP6_DIRECT_JUMP_P (first)
     && !QDSP6_DOT_NEW_P (second) && QDSP6_DIRECT_JUMP_P (second)){
    return false;
  }

  return true;
}




static bool
qdsp6_predicable(struct qdsp6_insn_info *insn_info)
{
  rtx cond_exec;
  rtx cond_exec_wrapper; 

  /* Ignore calls for now, which are predicable in V1. */
  if(!TARGET_V2_FEATURES){
    return false;
  }

  /* Ignore calls for now. */
  if(QDSP6_CALL_P (insn_info)){
    return false;
  }

  /* Form a COND_EXEC wrapper to test for predicability. */
  cond_exec = gen_rtx_COND_EXEC (VOIDmode,
    gen_rtx_NE (BImode,
                gen_rtx_REG (BImode, P0_REGNUM),
                const0_rtx),
                NULL_RTX);
  start_sequence();
  emit_insn(cond_exec);
  cond_exec_wrapper = get_insns();
  end_sequence();

  /* Wrap the pattern of the insn in a COND_EXEC. */
  COND_EXEC_CODE (PATTERN (cond_exec_wrapper))
    = PATTERN (insn_info->insn);

  /* If the COND_EXEC version exists, then the original insn is predicable. 
          Must check both instruction and operand constraints */
		  
   if(MEM_P (cond_exec_wrapper)){
	if (! memory_address_p (GET_MODE (cond_exec_wrapper), 
		XEXP (cond_exec_wrapper, 0)))
		return 0; 
   }
   else if(insn_invalid_p(cond_exec_wrapper)){
     	return 0; 
   }
   return 1; 

}




static bool
qdsp6_dot_newable(struct qdsp6_insn_info *insn_info)
{
  rtx x;

  if(!TARGET_DOT_NEW){
    return false;
  }

  /* .new is a V2 feature. */
  if(!TARGET_V2_FEATURES){
    return false;
  }

  /* Insns must already be conditional to be .newable. */
  if(!QDSP6_CONDITIONAL_P (insn_info) || QDSP6_DOT_NEW_P (insn_info)){
    return false;
  }

  /* Before V4, the only control insns that could be .new predicated were direct
     jumps. In V4, all control instructions can be .new predicated except calls
     and register-condition jumps. */
  if(QDSP6_CONTROL_P (insn_info)
     && (QDSP6_REGCOND_JUMP_P (insn_info)
         || QDSP6_CALL_P (insn_info)
         || (!TARGET_V4_FEATURES && !QDSP6_DIRECT_JUMP_P (insn_info)))){
    return false;
  }

  /* In V4, all non-control predicable instructions are .new predicable. */
  if(TARGET_V4_FEATURES){
    return true;
  }

  x = PATTERN (insn_info->insn);
  if(GET_CODE (x) == COND_EXEC){
    x = COND_EXEC_CODE (x);
    if(GET_CODE (x) == SET){
      /* Stores are not .newable. */
      if(MEM_P (SET_DEST (x))){
        return false;
      }
      /* loads */
      if(MEM_P (SET_SRC (x))){
        x = XEXP (SET_SRC (x), 0);
        /* Only base + offset loads are .newable. */
        if(G_REG_P (x) || (GET_CODE (x) == PLUS && G_REG_P (XEXP (x, 0)))){
          return true;
        }
        return false;
      }
    }
  }

  return true;
}




/* Return true if INSN_INFO appears to be part of the prologue. */

static bool
qdsp6_prologue_insn_p(struct qdsp6_insn_info *insn_info)
{
  struct qdsp6_reg_access *write;
  struct qdsp6_reg_access *read;
  struct qdsp6_mem_access *store;
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




#define QDSP6_LOOP_INSN(INSN) (   INSN_CODE (INSN->insn) == CODE_FOR_loop0 \
                               || INSN_CODE (INSN->insn) == CODE_FOR_loop1)

static void
qdsp6_insns_truly_dependent(
  struct qdsp6_insn_info *writer,
  struct qdsp6_insn_info *reader,
  int *dependence
)
{
  struct qdsp6_mem_access *store;
  struct qdsp6_mem_access *load;
  struct qdsp6_reg_access *write;
  struct qdsp6_reg_access *read;

  if(QDSP6_CONTROL_P (writer)){
    /* need to handle calls and multiple jumps */
    if (TARGET_V3_FEATURES) {
      if (QDSP6_CONDITIONAL_P(writer) && QDSP6_DIRECT_JUMP_P(writer) &&
          QDSP6_CONDITIONAL_P(reader) && QDSP6_DIRECT_JUMP_P(reader) &&
          /* not a dot-new jump */
          (!QDSP6_DOT_NEW_P(reader) && !QDSP6_DOT_NEW_P(writer)) &&
          /* not a register-condition jump */
          (!QDSP6_REGCOND_JUMP_P(reader) && !QDSP6_REGCOND_JUMP_P(writer)) &&
          (!QDSP6_LOOP_INSN(reader) && !QDSP6_LOOP_INSN(writer))) {
        *dependence |= QDSP6_DEP_DUALJUMP;
      }
    }
    *dependence = QDSP6_DEP_UNCONDITIONAL;
    return;
  }

  if(QDSP6_EMULATION_CALL_P (writer)){
    /* For an emulation call followed by another insn, consider anti
       dependencies to be true dependencies since emulation calls do not read
       their inputs until after all results in the current packet have been
       written. */
    qdsp6_insns_anti_dependent(writer, reader, dependence);
  }
  else if(QDSP6_EMULATION_CALL_P (reader)){
    /* For an emulation call following another insn, ignore true dependencies
       since emulation calls do not read their inputs until after all results in
       the current packet have been written. */
    return;
  }

  /* When generating exception handling information, do not put a call in the
     same packet as a prologue insn. */
  if(flag_exceptions
     && QDSP6_CALL_P (reader) && qdsp6_prologue_insn_p(writer)){
    *dependence = QDSP6_DEP_UNCONDITIONAL;
    return;
  }

  /* If a memory access is volatile, then it should be the only memory access in
     a packet.  (not really a dependency, but oh well) */
  if((QDSP6_VOLATILE_P (writer) || QDSP6_VOLATILE_P (reader))
     && (QDSP6_MEM_P (writer) && QDSP6_MEM_P (reader))){
    *dependence = QDSP6_DEP_UNCONDITIONAL;
    return;
  }

  /* Check for possible true memory dependencies. */
  for(store = writer->stores; store; store = store->next){
    for(load = reader->loads; load; load = load->next){
      if(true_dependence(store->mem, VOIDmode, load->mem, rtx_varies_p)){
        if(QDSP6_DEP_DOT_NEWABLE_P (*dependence)){
          load->flags |= QDSP6_DOT_NEW;
        }
        if(QDSP6_CONFLICT_P (store, load)){
          if(QDSP6_DEP_DOT_NEWABLE_P (*dependence)){
            load->flags &= ~QDSP6_DOT_NEW;
          }
          *dependence = QDSP6_DEP_UNCONDITIONAL;
          return;
        }
        else if(!QDSP6_DOT_NEW_P (writer)){
          *dependence |= QDSP6_DEP_NOT_DOT_NEWABLE;
        }
        if(QDSP6_DEP_DOT_NEWABLE_P (*dependence)){
          load->flags &= ~QDSP6_DOT_NEW;
        }
      }
    }
  }

  /* Check for true register dependencies. */
  for(write = writer->reg_writes; write; write = write->next){
    for(read = reader->reg_reads; read; read = read->next){
      if(write->regno == read->regno){
        if(QDSP6_DEP_DOT_NEWABLE_P (*dependence)){
          read->flags |= QDSP6_DOT_NEW;
        }
        if(QDSP6_CONFLICT_P (write, read)){
          if(PO_REGNO_P (read->regno)
             && qdsp6_dot_newable(reader)){
            *dependence |= QDSP6_DEP_DOT_NEWABLE;
          }
          else {
            if(QDSP6_DEP_DOT_NEWABLE_P (*dependence)){
              read->flags &= ~QDSP6_DOT_NEW;
            }
            *dependence = QDSP6_DEP_UNCONDITIONAL;
            return;
          }
        }
        else if(!QDSP6_DOT_NEW_P (writer)){
          *dependence |= QDSP6_DEP_NOT_DOT_NEWABLE;
        }
        if(QDSP6_DEP_DOT_NEWABLE_P (*dependence)){
          read->flags &= ~QDSP6_DOT_NEW;
        }
      }
    }
  }

  if(QDSP6_DEP_DOT_NEWABLE_P (*dependence)
     && QDSP6_DEP_NOT_DOT_NEWABLE_P (*dependence)){
    *dependence = QDSP6_DEP_UNCONDITIONAL;
  }

}




static void
qdsp6_insns_output_dependent(
  struct qdsp6_insn_info *insn0,
  struct qdsp6_insn_info *insn1,
  int *dependence
)
{
  struct qdsp6_reg_access *write0;
  struct qdsp6_reg_access *write1;

  if(QDSP6_EMULATION_CALL_P (insn1)){
    /* For an emulation call following another insn, ignore output dependencies
       since emulation calls do not write their outputs until after all results
       in the current packet have been written.  The exception is LR, since it
       is written by the call insn itself. */
    for(write0 = insn0->reg_writes; write0; write0 = write0->next){
      if(write0->regno == LINK_REGNUM){
        *dependence = QDSP6_DEP_UNCONDITIONAL;
      }
    }
    return;
  }

  /* Check for register output dependencies. */
  for(write0 = insn0->reg_writes; write0; write0 = write0->next){
    for(write1 = insn1->reg_writes; write1; write1 = write1->next){
      if(write0->regno == write1->regno){
        if(QDSP6_DEP_DOT_NEWABLE_P (*dependence)){
          write1->flags |= QDSP6_DOT_NEW;
        }
        if(QDSP6_CONFLICT_P (write0, write1)){
          if(QDSP6_DEP_DOT_NEWABLE_P (*dependence)){
            write1->flags &= ~QDSP6_DOT_NEW;
          }
          *dependence = QDSP6_DEP_UNCONDITIONAL;
          return;
        }
        else if(!QDSP6_DOT_NEW_P (insn0)){
          *dependence |= QDSP6_DEP_NOT_DOT_NEWABLE;
        }
        if(QDSP6_DEP_DOT_NEWABLE_P (*dependence)){
          write1->flags &= ~QDSP6_DOT_NEW;
        }
      }
    }
  }

  if(QDSP6_DEP_DOT_NEWABLE_P (*dependence)
     && QDSP6_DEP_NOT_DOT_NEWABLE_P (*dependence)){
    *dependence = QDSP6_DEP_UNCONDITIONAL;
  }

}




static void
qdsp6_insns_anti_dependent(
  struct qdsp6_insn_info *earlier,
  struct qdsp6_insn_info *later,
  int *dependence
)
{
  struct qdsp6_mem_access *mem;
  struct qdsp6_mem_access *store;
  struct qdsp6_reg_access *read;
  struct qdsp6_reg_access *write;

  /* Don't allow insns to move across control insns and vice versa. */
  if(   QDSP6_CONTROL_P (earlier)
     || QDSP6_CONTROL_P (later)){
    *dependence = QDSP6_DEP_UNCONDITIONAL;
    return;
  }

  /* Check for possible memory anti dependencies. */
  for(store = later->stores; store; store = store->next){
    /* load followed by a store */
    for(mem = earlier->loads; mem; mem = mem->next){
      if(QDSP6_CONFLICT_P (mem, store)
         && anti_dependence(mem->mem, store->mem)){
        *dependence = QDSP6_DEP_UNCONDITIONAL;
        return;
      }
    }
    /* store followed by a store */
    for(mem = earlier->stores; mem; mem = mem->next){
      if(QDSP6_CONFLICT_P (mem, store)
         && output_dependence(mem->mem, store->mem)){
        *dependence = QDSP6_DEP_UNCONDITIONAL;
        return;
      }
    }
  }

  /* Check for register anti dependencies. */
  for(read = earlier->reg_reads; read; read = read->next){
    for(write = later->reg_writes; write; write = write->next){
      if(read->regno == write->regno && QDSP6_CONFLICT_P (read, write)){
        *dependence = QDSP6_DEP_UNCONDITIONAL;
        return;
      }
    }
  }

}




static void
qdsp6_packet_insn_dependence(
  struct qdsp6_packet_info *packet,
  struct qdsp6_insn_info *insn_info,
  bool ignore_jump,
  int *dependence
)
{
  int num_insns;
  int i;

  *dependence = QDSP6_DEP_NONE;

  num_insns = packet->num_insns;
  /* When pulling an insn across a basic block, ignore the jump. */
  if(ignore_jump && packet->num_insns > 0
     && QDSP6_JUMP_P (packet->insns[packet->num_insns - 1])){
    num_insns--;
  }

  for(i = 0; i < num_insns; i++){
    /* really just need to check .new dependencies here */
    qdsp6_insns_truly_dependent(packet->insns[i], insn_info, dependence);
    if(QDSP6_DEP_UNCONDITIONAL_P (*dependence)){
      *dependence = QDSP6_DEP_UNCONDITIONAL;
      return;
    }
    qdsp6_insns_output_dependent(packet->insns[i], insn_info, dependence);
    if(QDSP6_DEP_UNCONDITIONAL_P (*dependence)){
      *dependence = QDSP6_DEP_UNCONDITIONAL;
      return;
    }
  }

}




static void
qdsp6_packet_insn_internal_dependence(
  struct qdsp6_packet_info *packet,
  struct qdsp6_insn_info *insn_info,
  int *dependence
)
{
  int num_insns;
  int i;

  *dependence = QDSP6_DEP_NONE;

  num_insns = packet->num_insns;


/*   When pulling an insn across a basic block, ignore the jump. */
  
/* PDB. DO NOT ignore register conditional jumps though, because they do read something other than
     a predicate register.*/

  if(packet->num_insns
     && ((QDSP6_JUMP_P (packet->insns[packet->num_insns - 1]))
	 && (!QDSP6_REGCOND_JUMP_P(packet->insns[packet->num_insns - 1])))){
    num_insns--;
  }

  for(i = 0; i < num_insns; i++){
    /* We can have truly dependent insns in the same packet becasue of .new. */
    qdsp6_insns_truly_dependent(packet->insns[i], insn_info, dependence);
    if(QDSP6_DEP_UNCONDITIONAL_P (*dependence)){
      *dependence = QDSP6_DEP_UNCONDITIONAL;
      return;
    }
    qdsp6_insns_anti_dependent(packet->insns[i], insn_info, dependence);
    if(QDSP6_DEP_UNCONDITIONAL_P (*dependence)){
      *dependence = QDSP6_DEP_UNCONDITIONAL;
      return;
    }
  }

}




static struct qdsp6_insn_info *
qdsp6_copy_insn_info(struct qdsp6_insn_info *insn_info)
{
  rtx insn;
  rtx pattern;

  insn = insn_info->insn;
  pattern = copy_rtx(PATTERN (insn));

  start_sequence();
  if(JUMP_P (insn)){
    emit_jump_insn(pattern);
  }
  else if(CALL_P (insn)){
    emit_call_insn(pattern);
  }
  else {
    emit_insn(pattern);
  }
  insn = get_insns();
  end_sequence();

  return qdsp6_get_insn_info(insn);
}




static struct qdsp6_insn_info *
qdsp6_predicate_insn(
  struct qdsp6_insn_info *insn_info,
  struct qdsp6_insn_info *jump_insn_info,
  bool invert_condition
)
{
  rtx pattern;
  rtx test;
  enum rtx_code test_code;

  pattern = copy_rtx(PATTERN (insn_info->insn));
  test = XEXP (SET_SRC (PATTERN (jump_insn_info->insn)), 0);
  test_code = GET_CODE (test);
  if(invert_condition){
    test_code = test_code == EQ ? NE : EQ;
  }

  pattern = gen_rtx_COND_EXEC (VOIDmode,
                               gen_rtx_fmt_ee(test_code,
                                              GET_MODE (test),
                                              XEXP (test, 0),
                                              XEXP (test, 1)),
                               pattern);

  start_sequence();
  if(CALL_P (insn_info->insn)){
    emit_call_insn(pattern);
  }
  else {
    emit_insn(pattern);
  }
  insn_info = qdsp6_get_insn_info(get_insns());
  end_sequence();

  return insn_info;
}




static int
qdsp6_dot_newify_reg(rtx *x, void *y)
{
  rtx old_reg = (rtx) y;

  if(REG_P (*x) && REGNO (*x) == REGNO (old_reg)){
    *x = gen_rtx_REG (GET_MODE (old_reg), REGNO (old_reg) + DOT_NEW_OFFSET);
  }
  return 0;
}




static struct qdsp6_insn_info *
qdsp6_dot_newify_insn(struct qdsp6_insn_info *insn_info)
{
  rtx pattern;
  rtx old_reg;

  gcc_assert(QDSP6_CONDITIONAL_P (insn_info));

  pattern = PATTERN (insn_info->insn);
  if(GET_CODE (pattern) == PARALLEL){
    pattern = XVECEXP (pattern, 0, 0);
  }

  if(GET_CODE (pattern) == COND_EXEC){
    old_reg = XEXP (COND_EXEC_TEST (pattern), 0);
  }
  else {
    gcc_assert(JUMP_P (insn_info->insn));
    old_reg = XEXP (XEXP (SET_SRC (pattern), 0), 0);
  }

  gcc_assert(PO_REG_P (old_reg));

  if(final_packing){
    for_each_rtx(&pattern, qdsp6_dot_newify_reg, old_reg);
  }

  insn_info->flags |= QDSP6_DOT_NEW;

  return insn_info;
}




static rtx
qdsp6_bb_real_head_insn(basic_block bb)
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
qdsp6_bb_real_end_insn(basic_block bb)
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
qdsp6_pack_insns(void)
{
  basic_block bb;
  struct qdsp6_packet_info *packet;
  struct qdsp6_insn_info *insn_info;
  rtx insn;
  rtx bb_head_insn = NULL;
  rtx bb_end_insn  = NULL;
  int start_packet;
  int dependence;

  packet = NULL;
  start_packet = 1;

  if(!final_packing){
    bb = ENTRY_BLOCK_PTR->next_bb;
    do{
      if(bb){ 
        bb_head_insn = qdsp6_bb_real_head_insn(bb);
        bb_end_insn = qdsp6_bb_real_end_insn(bb);
        if(!(bb_head_insn && bb_end_insn)){
          bb = bb->next_bb;
        }
      }
    }while(bb && !(bb_head_insn && bb_end_insn));
    gcc_assert(bb_head_insn && bb_end_insn);
  }
  else {
    bb = NULL;
    bb_head_insn = NULL;
    bb_end_insn = NULL;
  }

  for(insn = get_insns(); insn; insn = NEXT_INSN (insn)){

    /* Ignore notes. */
    if(NOTE_P (insn)){
      continue;
    }

    /* Don't bundle insns across other non-insns, like labels. */
    if(!INSN_P (insn)){
      start_packet = 1;
      continue;
    }

    /* Ignore insns that don't do anything. */
    switch(GET_CODE (PATTERN (insn))){
      case USE:
      case CLOBBER:
      case ADDR_VEC:
      case ADDR_DIFF_VEC:
        PUT_MODE (insn, VOIDmode);
        continue;
      default:
        break;
    }

    insn_info = qdsp6_get_insn_info(insn);

    /* Start a new packet if
         we have already found a reason to do so
         or this insn references a label that is out of range, causing the insn
            to be expanded into multiple, depenent insns
         or the resources needed for this insn are already being used by the
            insns already bundled
         or this insn is dependent on another insn already bundled. */
    if(start_packet
       || QDSP6_WANDERED_P (insn_info)
       || state_transition(qdsp6_state, insn) >= 0){
      packet = qdsp6_start_new_packet(insn_info);
   } 
    else {
      qdsp6_packet_insn_dependence(packet, insn_info, false, &dependence);
      if(QDSP6_DEP_UNCONDITIONAL_P (dependence)){
        packet = qdsp6_start_new_packet(insn_info);
      }
      else if(QDSP6_DEP_DOT_NEWABLE_P (dependence)){
        insn_info = qdsp6_dot_newify_insn(insn_info);
      }
    }

    qdsp6_add_insn_to_packet(packet, insn_info);

    /* Don't bundle an insn that has expanded into multiple, dependent insns. */
    start_packet = QDSP6_WANDERED_P (insn_info);

    if(!final_packing){
      if(bb_head_insn == insn){
        BB_HEAD_PACKET (bb) = packet;
        qdsp6_create_bb_sentinel_packet(packet);
      }
      if(bb_end_insn == insn){
        BB_END_PACKET (bb) = packet;
        do {
          bb = bb->next_bb;
          if(!bb){
            bb_head_insn = NULL_RTX;
            bb_end_insn = NULL_RTX;
            break;
          }
          bb_head_insn = qdsp6_bb_real_head_insn(bb);
          bb_end_insn = qdsp6_bb_real_end_insn(bb);
        }while(!(bb_head_insn && bb_end_insn));
      }
    }

  }

}




static int
check_call_reorder_feasibility(struct qdsp6_insn_info *insn_info){  

   struct qdsp6_reg_access *write;
   struct qdsp6_reg_access *read;
   char call_used_regs[] = CALL_USED_REGISTERS;

   gcc_assert(insn_info);
   /* If this is a call, I should assume it to alias with any memory access,
               but I might try to reason about calee-save registers	*/
   if(QDSP6_MEM_P (insn_info))	return QDSP6_DEP_UNCONDITIONAL; 
    for(write = insn_info->reg_writes; write; write = write->next){
	  if(call_used_regs[write->regno] || (write->regno == LINK_REGNUM))
			return QDSP6_DEP_UNCONDITIONAL;
    }
    for(read = insn_info->reg_reads; read; read = read->next){
	  if(call_used_regs[read->regno] || (read->regno == LINK_REGNUM))
			return QDSP6_DEP_UNCONDITIONAL;
    }
	return QDSP6_DEP_NONE;
}




/* This function is  used by tail merging
   Looks at the relationship of two instructions
   and tries to establish their independenc. 
   Conservative.  
   Shaped after qdsp6_insns_truly_dependent(from,to,&dependence); 	*/ 

int
qdsp6_instructions_dependent (rtx from,rtx to){
 struct qdsp6_insn_info *insn_info_from = NULL; 
 struct qdsp6_insn_info *insn_info_to   = NULL; 
 struct qdsp6_mem_access *store;
 struct qdsp6_mem_access *load;
 struct qdsp6_reg_access *write;
 struct qdsp6_reg_access *read;
 

  /* I know it is INSN_P for both cases, and it should not be a jump, 
          since we are not at the "bottom" of BB, but I will double check 
          for generality */ 
  if(!INSN_P(from) || 
    (GET_CODE (PATTERN (from)) == USE) || 
	(GET_CODE (PATTERN (from)) == CLOBBER))
	return QDSP6_DEP_UNCONDITIONAL; 
  if(!INSN_P(to) || 
    (GET_CODE (PATTERN (to)) == USE) || 
	(GET_CODE (PATTERN (to)) == CLOBBER))
	return QDSP6_DEP_UNCONDITIONAL; 
  
  insn_info_from = qdsp6_get_insn_info(from); 
  insn_info_to   = qdsp6_get_insn_info(to); 
				
  if(QDSP6_JUMP_P(insn_info_from) || QDSP6_JUMP_P(insn_info_to))
    /* I really should not have jumps here... */ 
	return QDSP6_DEP_UNCONDITIONAL;
  
  if(QDSP6_EMULATION_CALL_P (insn_info_from) || 
     QDSP6_EMULATION_CALL_P (insn_info_to))
    /* not handling these yet */ 
    return QDSP6_DEP_UNCONDITIONAL;

  /* If this is a call, I should assume it to alias with any memory access,
               but I might try to reason about calee-save registers	*/
  if(QDSP6_CALL_P (insn_info_from))
    return check_call_reorder_feasibility(insn_info_to);  

  /* If this is a call, I should assume it to alias with any memory access,
               but I might try to reason about calee-save registers	*/
  if(QDSP6_CALL_P(insn_info_to))
    return check_call_reorder_feasibility(insn_info_from);  
  
  /* this will cover the case of memory output dependency   */
  if((QDSP6_VOLATILE_P (insn_info_from) || QDSP6_VOLATILE_P (insn_info_to)) 
  && (QDSP6_MEM_P (insn_info_from) && QDSP6_MEM_P (insn_info_to))) 
    return QDSP6_DEP_UNCONDITIONAL; 

  /* Check for possible true memory dependencies. */
  for(store = insn_info_from->stores; (store && store->mem); store = store->next){
    for(load = insn_info_to->loads; (load && load->mem); load = load->next){
	   if(true_dependence(store->mem, VOIDmode, load->mem, rtx_varies_p))
		  return QDSP6_DEP_UNCONDITIONAL;
    }
  }

  /* Check for possible anti memory dependencies. */
  for(store = insn_info_to->stores; (store && store->mem); store = store->next){
    for(load = insn_info_from->loads; (load && load->mem); load = load->next){
	   if(true_dependence(store->mem, VOIDmode, load->mem, rtx_varies_p))
		  return QDSP6_DEP_UNCONDITIONAL;
    }
  }
  
  /* Check for true register dependencies. */
  for(write = insn_info_from->reg_writes; write; write = write->next){
    for(read = insn_info_to->reg_reads; read; read = read->next){
	  if(write->regno == read->regno)
			return QDSP6_DEP_UNCONDITIONAL;
    }
  }
  /* Check for anti register dependencies. */
  for(write = insn_info_to->reg_writes; write; write = write->next){
    for(read = insn_info_from->reg_reads; read; read = read->next){
	  if(write->regno == read->regno)
		return QDSP6_DEP_UNCONDITIONAL;
    }
  }
  /* We do not need to check for output dependency since this is a check inside BB, and DCE has been recently
     performed */ 

  return QDSP6_DEP_NONE;
}




static void
qdsp6_push_insn(struct qdsp6_insn_info *insn, struct qdsp6_packet_info *packet)
{
  struct qdsp6_transformed_insn_stack *insn_entry;

  insn_entry = ggc_alloc(sizeof(struct qdsp6_transformed_insn_stack));
  insn_entry->insn = insn;
  insn_entry->packet = packet;
  insn_entry->prev = qdsp6_insn_stack;
  qdsp6_insn_stack = insn_entry;
}




static struct qdsp6_insn_info *
qdsp6_pop_insn(void)
{
  struct qdsp6_transformed_insn_stack *insn_entry;

  insn_entry = qdsp6_insn_stack;
  qdsp6_insn_stack = qdsp6_insn_stack->prev;;

  return insn_entry->insn;
}




static bool
qdsp6_insn_fits_in_packet(
  struct qdsp6_insn_info *insn,
  struct qdsp6_packet_info *packet
)
{
  int i;

  state_reset(qdsp6_state);
  for(i = 0; i < packet->num_insns; i++){
    gcc_assert(state_transition(qdsp6_state, packet->insns[i]->insn) < 0);
  }

  return state_transition(qdsp6_state, insn->insn) < 0;
}




static void
qdsp6_move_insn(
  struct qdsp6_insn_info *old_insn,
  struct qdsp6_packet_info *from_packet,
  struct qdsp6_insn_info *new_insn,
  struct qdsp6_packet_info *to_packet
)
{
  basic_block bb;
  rtx adjacent_insn;

  gcc_assert(to_packet != from_packet);

  qdsp6_remove_insn_from_packet(from_packet, old_insn);
  qdsp6_add_insn_to_packet(to_packet, new_insn);

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
    if(to_packet->insns[to_packet->num_insns - 1] == new_insn){
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

  set_block_for_insn(new_insn->insn, BLOCK_FOR_INSN (adjacent_insn));
  df_insn_change_bb (new_insn->insn, BLOCK_FOR_INSN (adjacent_insn)); /* Support for data flow analysis */ 
}




static void
qdsp6_sanity_check_cfg_packet_info(void)
{
  basic_block bb;
  struct qdsp6_packet_info *packet;
  struct qdsp6_insn_info *insn;
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

  for(packet = qdsp6_head_packet; packet; packet = packet->next){
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
      gcc_assert(packet == BB_END_PACKET (bb) && packet == qdsp6_tail_packet);
    }
  }
}




static unsigned int 
qdsp6_count_packets(void)
{
  unsigned int total = 0; 
  struct qdsp6_packet_info *packet	= NULL; 

  for(packet = qdsp6_head_packet; packet; packet = packet->next) 	total++; 
  return total; 
}




static void
qdsp6_pull_up_insns(void)
{
#if !GCC_3_4_6
  basic_block bb;
  basic_block successor_bb;
  edge e;
  edge_iterator ei;
  struct qdsp6_packet_info *top_packet;
  struct qdsp6_packet_info *forward_edge_packet;
  struct qdsp6_packet_info *back_edge_packet;
  struct qdsp6_packet_info *last_packet;
  struct qdsp6_packet_info *packet;
  struct qdsp6_packet_info *target_packet;
  struct qdsp6_insn_info *insn;
  struct qdsp6_insn_info *original_insn;
  struct qdsp6_insn_info *edge_insn;
  bool start_at_the_next_packet;
  int dependence;
  int i;
  int j,k;
  int num_edges = 0; 
  /* This fixed way of book keeping will need to be updated */
  edge sorted_edge_list[MAX_NUM_EDGES_IN_BB];


  qdsp6_sanity_check_cfg_packet_info();

#if 0
  verify_flow_info();
#endif /* 0 */

  if(dump_file){
    fputs("\n\nall packets:\n\n", dump_file);
    qdsp6_print_packets(dump_file, qdsp6_head_packet);
    fputs("\n\n\n\nall basic blocks:\n\n", dump_file);
    FOR_EACH_BB (bb){
      qdsp6_print_bb_packets(dump_file, bb);
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

  FOR_EACH_BB (bb){
    if(!(BB_HEAD_PACKET (bb) && BB_END_PACKET (bb))
       || !JUMP_P (BB_END (bb))){
      /* || !QDSP6_DIRECT_JUMP_P (qdsp6_get_insn_info(BB_END (bb)))*/ 
      continue;
    }
    /* construct a sorted list of edges */
    num_edges = 0; 
    FOR_EACH_EDGE (e, ei, bb->succs){
      edge insert_this = e; 
      /* Insert in sorted order */
      /* _LSY_ Here we can use a better sorting algorithm, but V2 will not have more than 2 edges
	 so this brute force should work for now */ 
      for(k=0;k<num_edges;k++){
	if(e->probability >= sorted_edge_list[k]->probability){
	  int ll; 
	  for(ll=num_edges;ll>k;ll--){
	    sorted_edge_list[ll] = sorted_edge_list[ll-1]; 
	  }
	  insert_this	= sorted_edge_list[num_edges]; 
	  sorted_edge_list[k]	= e; 
	}
      }
      sorted_edge_list[num_edges] = insert_this; 
      num_edges++; 
      gcc_assert(num_edges < MAX_NUM_EDGES_IN_BB);
    }
    for(k=0;k<num_edges;k++){
      e = sorted_edge_list[k]; 
      successor_bb = e->dest;
      if(e->flags & EDGE_COMPLEX
         || successor_bb->index == EXIT_BLOCK
         || !(BB_HEAD_PACKET (successor_bb) && BB_END_PACKET (successor_bb))
         || !single_pred_p(successor_bb)){
    /*   || e->probability < 0.1 ) Can set a threshold  to prevent low probability code 
         from speculation, but need more investigation. 
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
            qdsp6_packet_insn_dependence(target_packet, insn, false, &dependence);
            if(QDSP6_DEP_UNCONDITIONAL_P (dependence)
               || !qdsp6_insn_fits_in_packet(insn, target_packet)){
              target_packet = target_packet->next;
              if(target_packet == packet){
                break;
              }
            }
            qdsp6_remove_insn_from_packet(packet, insn);
            qdsp6_add_insn_to_packet(target_packet, insn);
            break;
          }

          /* We can't pull up insns anti-dependent on an insn in the same
             packet. */
          for(j = i - 1; j >= 0; j--){
            dependence = QDSP6_DEP_NONE;
            qdsp6_insns_anti_dependent(packet->insns[j], insn, &dependence);
            /* really just need to check .new dependencies here */
            qdsp6_insns_truly_dependent(packet->insns[j], insn, &dependence);
            if(dependence){
              goto continue_to_next_insn_in_successor_bb;
            }
          }

          /* pull up */
          target_packet = packet;
          start_at_the_next_packet = false;
          while(target_packet != top_packet){
            if(target_packet == back_edge_packet){
              target_packet = forward_edge_packet;
              edge_insn = target_packet->insns[target_packet->num_insns - 1];
              gcc_assert(JUMP_P (edge_insn->insn));
              if(!QDSP6_DIRECT_JUMP_P (edge_insn)){
                target_packet = back_edge_packet;
                break;
              }
              if(QDSP6_CONDITIONAL_P (edge_insn)){

		/* PDB. EDGE_INSN can be conditional if it is a conditional jump on a predicate regsiter or a register conditional
		   jump. In the latter case INSN cannot be predicated. Therefore, check for this latter case before predicating 
		   INSN. */
                if(!QDSP6_REGCOND_JUMP_P (edge_insn) && qdsp6_predicable(insn)){
                  /* predicate */
                  qdsp6_push_insn(insn, target_packet);
                  insn = qdsp6_predicate_insn(insn, edge_insn,
                                              bb->next_bb == successor_bb);
                }
                else {
                  target_packet = back_edge_packet;
                  break;
                }
              }
            }
            else {
              target_packet = target_packet->prev;
            }
            /* dependent? */
            qdsp6_packet_insn_dependence(target_packet, insn, true, &dependence);
            if(QDSP6_DEP_UNCONDITIONAL_P (dependence)){
              start_at_the_next_packet = true;
              break;
            }
            else if(QDSP6_DEP_DOT_NEWABLE_P (dependence)){
              qdsp6_push_insn(insn, target_packet);
              insn = qdsp6_dot_newify_insn(insn);
            }
            /* anti-dependent? */
            qdsp6_packet_insn_internal_dependence(target_packet, insn, &dependence);
	    if(dependence){
              break;
            }
          }

          /* trickle down */
          if(start_at_the_next_packet){
            goto try_the_next_packet;
          }
          while(target_packet != packet){
            if(qdsp6_insn_fits_in_packet(insn, target_packet)){
              break;
            }

            try_the_next_packet:

            while(qdsp6_insn_stack
                  && qdsp6_insn_stack->packet == target_packet){
              insn = qdsp6_pop_insn();
            }
            if(target_packet == forward_edge_packet){
              target_packet = back_edge_packet;
            }
            else {
              target_packet = target_packet->next;
            }
          }

          if(target_packet != packet){
            qdsp6_move_insn(original_insn, packet, insn, target_packet);
            i--;
          }
          qdsp6_insn_stack = NULL;
          continue_to_next_insn_in_successor_bb: i=i;
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
    fputs("\n\nall packets:\n\n", dump_file);
    qdsp6_print_packets(dump_file, qdsp6_head_packet);
    fputs("\n\n\n\nall basic blocks:\n\n", dump_file);
    FOR_EACH_BB (bb){
      qdsp6_print_bb_packets(dump_file, bb);
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
 

#endif /* !GCC_3_4_6 */

}




static void
qdsp6_init_packing_info(void)
{
  basic_block bb;
  struct qdsp6_bb_aux_info *new_bb_aux;

  dfa_start();
  qdsp6_state = xmalloc(state_size());
  state_reset(qdsp6_state);

  qdsp6_head_packet = NULL;
  qdsp6_tail_packet = NULL;

  if(!final_packing){
    qdsp6_head_bb_aux = NULL;
    new_bb_aux = NULL;
    FOR_EACH_BB (bb){
      if(qdsp6_head_bb_aux == NULL){
        qdsp6_head_bb_aux = ggc_alloc_cleared(sizeof(struct qdsp6_bb_aux_info));
        new_bb_aux = qdsp6_head_bb_aux;
      }
      else {
        new_bb_aux->next = ggc_alloc_cleared(sizeof(struct qdsp6_bb_aux_info));
        new_bb_aux = new_bb_aux->next;
      }
      bb->aux = new_bb_aux;
    }

    qdsp6_insn_stack = NULL;
  }
}




static void
qdsp6_free_packing_info(void)
{
  basic_block bb;

  if(!final_packing){
    FOR_EACH_BB (bb){
      bb->aux = NULL;
    }
    qdsp6_head_bb_aux = NULL;
  }

  qdsp6_head_packet = NULL;
  qdsp6_tail_packet = NULL;

  free(qdsp6_state);
  dfa_finish();
}




static void
qdsp6_packet_optimizations(void)
{
  if(!(TARGET_PACKETS && optimize)){
    return;
  }

  shorten_branches(get_insns());
  qdsp6_init_packing_info();
  qdsp6_pack_insns();
  qdsp6_pull_up_insns();
  qdsp6_free_packing_info();
}




static void
qdsp6_final_pack_insns(void)
{
  if(!(TARGET_PACKETS && optimize)){
    return;
  }

  final_packing = true;
  qdsp6_init_packing_info();
  qdsp6_pack_insns();
  qdsp6_free_packing_info();
  final_packing = false;
}

static bool
mips_can_eliminate (const int from ATTRIBUTE_UNUSED, const int to)
{
  return true;
}

#undef TARGET_FRAME_POINTER_REQUIRED
#define TARGET_FRAME_POINTER_REQUIRED hook_bool_void_true


/* Should be at the end of the file */
#include "gt-qdsp6.h"
