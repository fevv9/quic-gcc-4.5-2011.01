/* Prototypes for hexagon.c functions used in the md file & elsewhere.
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

extern void hexagon_override_options(void);
extern void hexagon_optimization_options(int, int);
extern void hexagon_init_expanders(void);
extern void hexagon_conditional_register_usage(void);
extern bool hexagon_cannot_change_mode_class(
  enum machine_mode,
  enum machine_mode,
  enum reg_class);
extern bool hexagon_const_ok_for_constraint_p(HOST_WIDE_INT, char, const char *);
extern HOST_WIDE_INT hexagon_initial_elimination_offset(int, int);
extern bool hexagon_store_by_pieces_p(unsigned HOST_WIDE_INT, unsigned int);
extern const char *hexagon_asm_output_opcode(FILE *, const char *);
extern void hexagon_expand_prologue(void);
extern void hexagon_expand_epilogue(bool);
extern bool hexagon_direct_return(void);
extern void hexagon_hardware_loop (void);

#ifdef TREE_CODE
extern int  hexagon_data_alignment(tree, int);
extern int  hexagon_constant_alignment(tree, int);
extern unsigned int hexagon_local_alignment(tree, int);
extern int  hexagon_function_arg_advance(CUMULATIVE_ARGS, enum machine_mode, tree, int);
extern void hexagon_asm_output_aligned_decl_common(
              FILE *,
              tree,
              const char *,
              unsigned HOST_WIDE_INT,
              unsigned HOST_WIDE_INT);
extern void hexagon_asm_output_aligned_decl_local(
              FILE *,
              tree,
              const char *,
              unsigned HOST_WIDE_INT,
              unsigned HOST_WIDE_INT);
#endif /* TREE_CODE */

#ifdef RTX_CODE
extern rtx  hexagon_return_addr_rtx(int, rtx);
extern bool hexagon_legitimate_address_p(enum machine_mode, rtx, bool, const char *);
extern bool hexagon_loop_invalid_for_forced_unroll(rtx loop_header);
extern void hexagon_final_prescan_insn(rtx, rtx *, int);
extern void hexagon_print_operand(FILE *, const_rtx, int);
extern void hexagon_print_operand_address(FILE *, const_rtx);
extern rtx  hexagon_expand_compare(enum rtx_code);
extern rtx  hexagon_expand_compare2(enum rtx_code, rtx op0, rtx op1);
extern bool hexagon_expand_movmem(rtx[]);
extern bool hexagon_expand_setmem(rtx[]);
extern rtx  hexagon_branch_hint(rtx);
extern int  hexagon_instructions_dependent(rtx, rtx);
extern unsigned HOST_WIDE_INT sdata_symbolic_operand_smallest_accessable_size(rtx);
#endif /* RTX_CODE */

extern void hexagon_fast_math_libfunc(rtx);

#if defined(TREE_CODE) && defined(RTX_CODE)
extern rtx  hexagon_function_arg(CUMULATIVE_ARGS, enum machine_mode, tree, int);
#endif /* TREE_CODE && RTX_CODE */

/* PIC support */
extern rtx legitimize_pic_address(rtx, enum machine_mode, rtx);
extern rtx hexagon_legitimize_address (rtx, rtx, enum machine_mode);
extern void require_pic_register (void);
