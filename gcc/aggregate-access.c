/* Optimize by combining instructions for GNU compiler.
   Copyright (C) 1987, 1988, 1992, 1993, 1994, 1995, 1996, 1997, 1998,
   1999, 2000, 2001, 2002, 2003, 2004, 2005, 2006, 2007, 2008, 2009
   Free Software Foundation, Inc.

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify it under
the terms of the GNU General Public License as published by the Free
Software Foundation; either version 3, or (at your option) any later
version.

GCC is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
for more details.

You should have received a copy of the GNU General Public License
along with GCC; see the file COPYING3.  If not see
<http://www.gnu.org/licenses/>.  */

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "tm.h"
#include "rtl.h"
#include "tree.h"
#include "tm_p.h"
#include "flags.h"
#include "regs.h"
#include "hard-reg-set.h"
#include "basic-block.h"
#include "insn-config.h"
#include "function.h"
#include "expr.h"
#include "insn-attr.h"
#include "recog.h"
#include "real.h"
#include "toplev.h"
#include "target.h"
#include "optabs.h"
#include "insn-codes.h"
#include "rtlhooks-def.h"
#include "output.h"
#include "params.h"
#include "timevar.h"
#include "tree-pass.h"
#include "df.h"
#include "cgraph.h"

static bool
gate_handle_aggregate_access (void)
{
  return TARGET_AGGREGATE_ACCESS;
}

/*******************************************************************************************
*   Try optimizing large struct member accesses                                            *
*                                                                                          *
*      R = #symbol                  R = #symbol + offset            R = #symbol + offset   *
*        /  |  \                      /  |  \                         /  |  \              *
*       /   |   \                    /   |   \                       /   |   \             *
*      /    |    \                  /    |    \       combine       /    |    \            *
*    add   add   add     ---->     add   add   add    ------->     memw  memw  memw        *
*     |(1)  |(2)  |(3)             |(1)  |(2)  |(3                 (1)   (2)   (3)         *
*     |     |     |                |     |     |                                           *
*   memw  memw  memw               memw  memw  memw                                        *
*******************************************************************************************/

static unsigned int
rest_of_handle_aggregate_access (void)
{
  /* Build the df object. */
  df_chain_add_problem (DF_DU_CHAIN + DF_UD_CHAIN);
  df_analyze ();

  basic_block bb;
  /* Loop thru all bb insns */
  FOR_ALL_BB (bb)
    {
      rtx insn;
      FOR_BB_INSNS (bb, insn)
        {
          if (!NONJUMP_INSN_P (insn))
            continue;

          if (PATTERN (insn) == NULL_RTX)
            continue;

          if (GET_CODE (PATTERN (insn)) != SET)
            continue;

           /**************************************************************************************************
           *  ;; insn --> R = #symbol                                                                        *
           *  (insn 5 2 7 2 bug2613.c:13 (set (reg/f:SI 53)                                                  *
           *    (symbol_ref:SI ("f") <var_decl 0x2b29b5916280 f>)) 17 {movsi_real} (nil))                    *
           *                                                                                                 *
           * ...                                                                                             *
           *                                                                                                 *
           *  ;; add_insn --> R = add(R,#5796)                                                               *
           *  ;; add_oprnds --> (plus:SI (reg/f:SI 53) ...)                                                  *
           *  (insn 7 5 10 2 bug2613.c:13 (set (reg/f:SI 55)                                                 *
           *    (plus:SI (reg/f:SI 53)                                                                       *
           *      (const_int 5796 [0x16a4]))) 30 {addsi3_real}                                               *
           *        (expr_list:REG_EQUAL (const:SI (plus:SI (symbol_ref:SI ("f") <var_decl 0x2b29b5916280 f>)* 
           *          (const_int 5796 [0x16a4])))                                                            *
           *            (nil)))                                                                              *
           *                                                                                                 *
           * ...                                                                                             *
           *                                                                                                 *
           * ;; mem_insn --> R = memw(R)                                                                     *
           * (insn 11 10 12 2 bug2613.c:13 (set (reg:SI 60 [ f.b ])                                          *
           *   (mem/s/c:SI (reg/f:SI 55) [3 f.b+0 S4 A32])) 17 {movsi_real}                                  *
           *     (expr_list:REG_DEAD (reg/f:SI 55)                                                           *
           *       (nil)))                                                                                   *
           **************************************************************************************************/

          rtx insn_result = XEXP (PATTERN (insn), 0);
          rtx insn_oprnds = XEXP (PATTERN (insn), 1);

          /* Avoid modifying hard registers */
          if (HARD_REGISTER_NUM_P (REGNO (insn_result)))
            continue;

          if (GET_CODE (insn_oprnds) != SYMBOL_REF)
            continue;

          df_ref *def_rec;
          struct df_link *defs;

          /* Make sure insn produces only 1 result */
          def_rec = DF_INSN_DEFS (insn);
          if (*def_rec && (*(def_rec+1) == 0))
            {
              bool flag_anchor = false;
              rtx new_reg = 0;
              HOST_WIDE_INT aligned_offset = 0;

              for (defs = DF_REF_CHAIN (*def_rec); defs; defs = defs->next)
                {
		  if (DF_REF_IS_ARTIFICIAL (defs->ref))
                    continue;

                  rtx add_insn = DF_REF_INSN (defs->ref);
                  rtx add_body = PATTERN (add_insn);

                  if (BLOCK_FOR_INSN (insn) != BLOCK_FOR_INSN (add_insn) ||
                      GET_CODE (add_body) != SET)
                    continue;

                  rtx add_result = XEXP (PATTERN (add_insn), 0);
                  rtx add_oprnds = XEXP (PATTERN (add_insn), 1);

                  /* Check for add insn */
                  if (GET_CODE (add_oprnds) != PLUS)
                    continue;

                  rtx add_op0 = XEXP (add_oprnds, 0);
                  rtx add_op1 = XEXP (add_oprnds, 1);

                  /* First operand must be insn_result */
                  if (add_op0 != insn_result)
                    continue;

                  /* Second operand must be an immediate */
                  if (GET_CODE (add_op1) != CONST_INT)
                    continue;

                  /* Record the original offset */
                  HOST_WIDE_INT original_offset = INTVAL (add_op1);

                  /* Result of add used in load/store */
                  df_ref *def_rec2;
                  struct df_link *defs2;
                  /* Make sure add_insn produces only 1 result */
                  def_rec2 = DF_INSN_DEFS (add_insn);
                  if (*def_rec2 && (*(def_rec2+1) == 0))
                    {
                      /* Make sure there is only 1 use of defs2 */
                      defs2 = DF_REF_CHAIN (*def_rec2);
                      if (defs2 && (defs2->next == 0))
                        {
                          rtx mem_insn = DF_REF_INSN (defs2->ref);
                          rtx mem_body = PATTERN (mem_insn);

                          if (BLOCK_FOR_INSN (insn) != BLOCK_FOR_INSN (mem_insn) ||
                              GET_CODE (mem_body) != SET)
                            continue;

                          rtx mem_result = XEXP (mem_body, 0);
                          rtx mem_oprnds = XEXP (mem_body, 1);

                          /* Handle load and store */
                          if (MEM_P (mem_result))
                            {
                              /* memw = r */
                              rtx mem_op0 = XEXP (mem_result, 0);
                              if (mem_op0 != add_result)
                                continue;
                            }
                          else if (MEM_P (mem_oprnds))
                            {
                              /* r = memw */
                              rtx mem_op0 = XEXP (mem_oprnds, 0);
                              if (mem_op0 != add_result)
                                continue;
                            }
                          else
                            {
                              continue;
                            }

                            enum machine_mode mode = GET_MODE (mem_oprnds);
                            switch (mode)
                              {
                              case QImode:
                                /* Range checking */
                                if (CONST_OK_FOR_CONSTRAINT_P (original_offset, 'I', "Is11"))
                                  continue;
                                break;

                              case HImode:
                                /* Range checking */
                                if (CONST_OK_FOR_CONSTRAINT_P (original_offset, 'I', "Is12"))
                                    continue;
                                break;

                              case SImode:
                                /* Range checking */
                                if (CONST_OK_FOR_CONSTRAINT_P (original_offset, 'I', "Is13"))
                                    continue;
                                break;

                              case DImode:
                                /* Range checking */
                                if (CONST_OK_FOR_CONSTRAINT_P (original_offset, 'I', "Is14"))
                                    continue;
                                break;

                              default:
                                gcc_assert (1);
                                break;
                              }

                            /* If flag_anchor is not set */
                            if (!flag_anchor)
                              {
                                if (dump_file)
                                  {
                                    fprintf(dump_file, "\nBEGIN - applying aggregate access optimization\n");
                                    print_inline_rtx (dump_file, insn, 2);
                                    fprintf(dump_file, "\n");
                                    print_inline_rtx (dump_file, add_insn, 2);
                                    fprintf(dump_file, "\n");
                                  }

                                /* Time to generate new insn R = #symbol + offset */
                                new_reg = gen_reg_rtx(SImode);

                                /* Fix alignment */
                                aligned_offset = original_offset & (~(BIGGEST_ALIGNMENT/BITS_PER_UNIT - 1));
                                rtx new_offset = gen_int_mode (aligned_offset, SImode);

                                /* r = const32 (f + new_offset) */
                                rtx const32_insn = gen_movsi_const32 (new_reg, insn_oprnds, new_offset);
                                emit_insn_after (const32_insn, insn);

                                /* Gen up diff offset */
                                rtx diff_offset = gen_int_mode (original_offset-aligned_offset, SImode);

                                /* Replace add_op0 with const32_insn */
                                add_insn = replace_rtx (add_insn, add_op0, new_reg);
                                /* Replace add_op1 with const32_insn */
                                add_insn = replace_rtx (add_insn, add_op1, diff_offset);

                                flag_anchor = true;

                                if (dump_file)
                                  {
                                    fprintf(dump_file, "----------------------------------------------\n");
                                    print_inline_rtx (dump_file, const32_insn, 4);
                                    fprintf(dump_file, "\n");
                                    print_inline_rtx (dump_file, add_insn, 4);
                                    fprintf(dump_file, "\nEND - applying aggregate access optimization\n");
                                  }
                              }
                            else 
                              {
                                gcc_assert (new_reg);
                                /* Gen up diff offset */
                                rtx diff_offset = gen_int_mode (original_offset-aligned_offset, SImode);

                                if (!CONST_OK_FOR_CONSTRAINT_P (INTVAL (diff_offset), 'I', "Is16"))
                                  continue;

                                /* Replace add_op0 with const32_insn */
                                add_insn = replace_rtx (add_insn, add_op0, new_reg);
                                /* Replace add_op1 with const32_insn */
                                add_insn = replace_rtx (add_insn, add_op1, diff_offset);
                              }
                        } /* if only 1 use */
                    } /* if only 1 result - def2 */
                } /* for all uses of result */
            } /* if only 1 result - def */
        } /* for all insns */
    } /* for all bb */

  df_insn_rescan_all ();
  return 0;
}

struct rtl_opt_pass pass_aggregate_access =
{
 {
  RTL_PASS,
  "aggregate",                          /* name */
  gate_handle_aggregate_access,         /* gate */
  rest_of_handle_aggregate_access,      /* execute */
  NULL,                                 /* sub */
  NULL,                                 /* next */
  0,                                    /* static_pass_number */
  TV_AGGREGATE,                         /* tv_id */
  0,                                    /* properties_required */
  0,                                    /* properties_provided */
  0,                                    /* properties_destroyed */
  0,                                    /* todo_flags_start */
  TODO_dump_func | TODO_df_verify |
  TODO_df_finish | TODO_verify_rtl_sharing |
  TODO_ggc_collect,                     /* todo_flags_finish */
 }
};

