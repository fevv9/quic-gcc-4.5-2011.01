/*****************************************************************
# Copyright (c) $Date$ Qualcomm Innovation Center, Inc..
# All Rights Reserved.
# Modified by Qualcomm Innovation Center, Inc. on $Date$
*****************************************************************/
/* Prototypes for qdsp6.c functions used in the md file & elsewhere.
   Copyright (C) 1999, 2000, 2002 Free Software Foundation, Inc.

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

extern void qdsp6_override_options(void);
extern void qdsp6_optimization_options(int, int);
extern void qdsp6_init_expanders(void);
extern void qdsp6_conditional_register_usage(void);
extern bool qdsp6_cannot_change_mode_class(
  enum machine_mode,
  enum machine_mode,
  enum reg_class);
extern bool qdsp6_const_ok_for_constraint_p(HOST_WIDE_INT, char, const char *);
extern HOST_WIDE_INT qdsp6_initial_elimination_offset(int, int);
extern bool qdsp6_store_by_pieces_p(unsigned HOST_WIDE_INT, unsigned int);
extern const char *qdsp6_asm_output_opcode(FILE *, const char *);
extern void qdsp6_expand_prologue(void);
extern void qdsp6_expand_epilogue(bool);
extern bool qdsp6_direct_return(void);
extern void qdsp6_hardware_loop (void);

#ifdef TREE_CODE
extern int  qdsp6_data_alignment(tree, int);
extern int  qdsp6_constant_alignment(tree, int);
extern int  qdsp6_local_alignment(tree, int);
#if GCC_3_4_6
extern bool qdsp6_must_pass_in_stack(enum machine_mode, tree);
#endif /* GCC_3_4_6 */
extern int  qdsp6_function_arg_advance(CUMULATIVE_ARGS, enum machine_mode, tree, int);
extern void qdsp6_asm_output_aligned_decl_common(
              FILE *,
              tree,
              const char *,
              unsigned HOST_WIDE_INT,
              unsigned HOST_WIDE_INT);
extern void qdsp6_asm_output_aligned_decl_local(
              FILE *,
              tree,
              const char *,
              unsigned HOST_WIDE_INT,
              unsigned HOST_WIDE_INT);
#endif /* TREE_CODE */

#ifdef RTX_CODE
#if GCC_3_4_6
extern enum reg_class qdsp6_secondary_reload_class(rtx, enum reg_class);
#endif /* GCC_3_4_6 */
extern rtx  qdsp6_return_addr_rtx(int, rtx);
extern bool qdsp6_legitimate_address_p(enum machine_mode, rtx, bool, const char *);
#if GCC_3_4_6
extern bool qdsp6_reg_ok_for_base_p(rtx, bool);
#endif /* GCC_3_4_6 */
extern void qdsp6_final_prescan_insn(rtx, rtx *, int);
extern void qdsp6_print_operand(FILE *, rtx, int);
extern void qdsp6_print_operand_address(FILE *, rtx);
extern bool qdsp6_expand_movstr(rtx[]);
extern bool qdsp6_expand_movmem(rtx[]);
extern bool qdsp6_expand_setmem(rtx[]);
extern bool qdsp6_expand_clrstr(rtx[]);
extern bool qdsp6_expand_strlen(rtx[]);
extern bool qdsp6_expand_cmpstr(rtx[]);
extern rtx  qdsp6_expand_compare(enum rtx_code);
extern int  qdsp6_GP_or_reg_operand_c(rtx, enum machine_mode);
extern int  qdsp6_nonimmediate_operand_with_GP_c(rtx, enum machine_mode);
extern int  qdsp6_instructions_dependent(rtx, rtx);
#endif /* RTX_CODE */

#if defined(TREE_CODE) && defined(RTX_CODE)
extern rtx  qdsp6_function_arg(CUMULATIVE_ARGS, enum machine_mode, tree, int);
#if GCC_3_4_6
extern rtx  qdsp6_function_value(tree, tree, bool);
#endif /* GCC_3_4_6 */
#endif /* TREE_CODE && RTX_CODE */
