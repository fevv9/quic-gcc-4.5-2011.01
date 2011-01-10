/* Tree level target specific cleanup pass for the GNU compiler.
   Copyright (C) 2010
   
 
This file is part of GCC.
   
GCC is free software; you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by the
Free Software Foundation; either version 3, or (at your option) any
later version.
   
GCC is distributed in the hope that it will be useful, but WITHOUT
ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
for more details.
   
You should have received a copy of the GNU General Public License
along with GCC; see the file COPYING3.  If not see
<http://www.gnu.org/licenses/>.  */

/* This is a pass that suppose to be run prior to abandoning SSA 
   notation in tree form. It is generally intended for machine specific 
   transformations at tree level. Currently it is used to undo some 
   tree level optimisations that severily impact expand of some 
   constructs. In the future it could be extended to catch multiple
   scenarios where we know something in trres that later is lost in rtx.
*/ 

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "tm.h"
#include "ggc.h"

#include "hard-reg-set.h"
#include "obstack.h"
#include "basic-block.h"

#include "tree.h"
#include "diagnostic.h"
#include "tree-flow.h"
#include "gimple.h"
#include "tree-dump.h"
#include "tree-pass.h"
#include "timevar.h"
#include "flags.h"
#include "cfgloop.h"

unsigned int tree_ssa_machine_specific_cleanup (void); 

/* Vector indicating an SSA name has already been seen and marked
   as used.  */
static sbitmap processed;


/* Search backward from mult expr in the same BB
   to find dominating type cast. 
   For the current issue this is sufficient and simple. If more general
   solution is needed, we would need full liveness 
   info here. 
 */ 
static inline gimple
find_mult_related_typecast(gimple_stmt_iterator *mult_iter, 
                           tree mult_oprd)
{
  gimple_stmt_iterator gsi;

  for (gsi = *mult_iter; !gsi_end_p (gsi); gsi_prev (&gsi) ) 
    {
      gimple stmt = gsi_stmt (gsi);
      if (is_gimple_assign (stmt) 
          && (gimple_assign_rhs_code (stmt) == NOP_EXPR) // || TREE_CODE (expr) == CONVERT_EXPR) 
          && operand_equal_p(gimple_assign_lhs (stmt), mult_oprd,0))
        {
          return stmt; 
        }
    }
  return NULL; 
}

/* Ok, we have determined that same typecast has already been 
   used for another MULT. This is possibly a combination of 
   unroll and copy prop so we want to undo that optimization 
   since we will have major issues matching that pattern */ 

static inline void
update_mult_statement(gimple stmt,gimple defining_cast,
                      gimple_stmt_iterator *gsi,char op0)
{
  gimple new_stmt = gimple_copy (defining_cast);
  tree new_lhs = NULL_TREE;
  tree var_type = TREE_TYPE (gimple_assign_lhs (defining_cast)); 
  tree tmp = create_tmp_var (var_type, "mul_undo_");
  
  /* 
  fprintf(stderr,"MUL with multiple typecast op%d use:\t",op0); //,gimple_assign_rhs_class(stmt),gimple_num_ops (stmt)); 
  print_gimple_stmt(stderr,stmt,0,0);  
  fprintf(stderr,"\tCast (%s)(%d)->(%s)(%d).\n\t",
		GET_MODE_NAME(TYPE_MODE(TREE_TYPE(gimple_assign_rhs1(defining_cast)))),
		GET_MODE_SIZE(TYPE_MODE(TREE_TYPE(gimple_assign_rhs1(defining_cast)))),
		GET_MODE_NAME(TYPE_MODE(TREE_TYPE(gimple_assign_lhs(defining_cast)))),
		GET_MODE_SIZE(TYPE_MODE(TREE_TYPE(gimple_assign_lhs(defining_cast))))); 
  print_gimple_stmt(stderr,defining_cast,0,0);
  fprintf(stderr,"\tCreating new....\t"); 
  */
  
  add_referenced_var (tmp); 
  new_lhs = make_ssa_name(tmp,new_stmt); 

  gimple_assign_set_lhs (new_stmt,new_lhs);

  if(op0)  gimple_assign_set_rhs2(stmt,new_lhs); 
  else  gimple_assign_set_rhs1(stmt,new_lhs); 

  update_stmt (new_stmt);
  update_stmt (stmt);

  gsi_insert_before (gsi, new_stmt, GSI_NEW_STMT); 
  
  /*  
  print_gimple_stmt(stderr,new_stmt,0,0);
  fprintf(stderr,"\tUpdated stmt:\t"); 
  print_gimple_stmt(stderr,stmt,0,0);  
  */ 

  /* Bump pointer to point to MULT again */ 
  gsi_next (gsi); 
}


unsigned int
tree_ssa_machine_specific_cleanup (void)
{
  basic_block bb;
  unsigned int todoflags = 0;
  bool cfg_changed	= false; 

  /* Used to mark double uses of typecast */ 
  processed = sbitmap_alloc (num_ssa_names + 1);
  sbitmap_zero (processed);

  FOR_EACH_BB (bb)
    {
      gimple_stmt_iterator gsi;

      for (gsi = gsi_start_bb (bb); !gsi_end_p (gsi); gsi_next (&gsi))
        {
          gimple stmt = gsi_stmt (gsi);

          if (is_gimple_assign (stmt) 
              && (gimple_assign_rhs_code (stmt) == MULT_EXPR))
            {		
              tree op0 = gimple_assign_rhs1 (stmt); 
              tree op1 = gimple_assign_rhs2 (stmt);
              gimple defining_cast_0	= find_mult_related_typecast(&gsi,op0); 
              gimple defining_cast_1	= find_mult_related_typecast(&gsi,op1); 

              if(defining_cast_0)
                {
                  tree lhs = gimple_assign_lhs (defining_cast_0);
				  tree rhs1 = gimple_assign_rhs1 (defining_cast_0); 
		
                  if ((TREE_CODE (lhs) == SSA_NAME)
				     &&(GET_MODE_SIZE(TYPE_MODE(TREE_TYPE(rhs1))) < GET_MODE_SIZE(TYPE_MODE(TREE_TYPE(lhs)))))
					 {
                      int ver = SSA_NAME_VERSION(lhs);

                      if (TEST_BIT (processed, ver))
                        update_mult_statement(stmt,defining_cast_0,&gsi,0); 
                      else	
                        SET_BIT (processed, ver); 			
                  }
                }
              if(defining_cast_1)
                {
                  tree lhs = gimple_assign_lhs (defining_cast_1);
				  tree rhs1 = gimple_assign_rhs1 (defining_cast_1); 
				  
                  if ((TREE_CODE (lhs) == SSA_NAME)
				     &&(GET_MODE_SIZE(TYPE_MODE(TREE_TYPE(rhs1))) < GET_MODE_SIZE(TYPE_MODE(TREE_TYPE(lhs)))))
					 {
                      int ver = SSA_NAME_VERSION(lhs);

                      if (TEST_BIT (processed, ver))
                        update_mult_statement(stmt,defining_cast_1,&gsi,1); 
                      else	
                        SET_BIT (processed, ver); 			
                  }
                }
            }	  
        }
    }

  sbitmap_free (processed);

  if (cfg_changed)
    todoflags |= TODO_cleanup_cfg;

  return todoflags;
}

static bool
gate_tree_machine (void)
{
  return flag_tree_machine != 0;
}

struct gimple_opt_pass pass_tree_machine =
{
    {
      GIMPLE_PASS,
      "tree_machine",					/* name */
      gate_tree_machine,				/* gate */
      tree_ssa_machine_specific_cleanup,/* execute */
      NULL,								/* sub */
      NULL,								/* next */
      0,								/* static_pass_number */
      TV_TREE_MACHINE,					/* tv_id */
      PROP_cfg | PROP_ssa,				/* properties_required */
      0,					/* properties_provided */
      0,					/* properties_destroyed */
      0,					/* todo_flags_start */
      TODO_dump_func | TODO_verify_ssa	/* todo_flags_finish */
    }
};
