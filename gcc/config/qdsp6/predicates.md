;; ##################################################################
;; # Copyright (c) $Date$ Qualcomm Innovation Center, Inc..
;; # All Rights Reserved.
;; # Modified by Qualcomm Innovation Center, Inc. on $Date$
;; ##################################################################
;;-----------;;
;; Registers ;;
;;-----------;;

;; general purpose register
(define_predicate "gr_register_operand"
  (match_operand 0 "register_operand")
  {
    unsigned int regno;
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
)

;; predicate register
(define_predicate "pr_register_operand"
  (match_operand 0 "register_operand")
  {
    unsigned int regno;
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
)

;; non-general purpose register
(define_predicate "nongr_register_operand"
  (match_operand 0 "register_operand")
  {
    if(GET_CODE (op) == SUBREG){
      op = SUBREG_REG (op);
    }
    /* ??? Allow (subreg (mem))? */
    return REG_P (op) && !G_REG_P (op);
  }
)

;; vector suitable for splatting
(define_predicate "splattable_vector"
  (match_operand 0 "gr_register_operand")
  {
    int i;
    for(i = 1; i < GET_MODE_NUNITS (mode); i++){
      if(!rtx_equal_p(XVECEXP (op, 0, i), XVECEXP (op, 0, 0))){
        return false;
      }
    }
    return true;
  }
)


;;-------------------;;
;; Memory/References ;;
;;-------------------;;

;; memory with address in register
(define_predicate "indirect_memory_operand"
  (and (match_operand 0 "memory_operand")
       (match_test "REG_P (XEXP (op, 0))"))
)

;; absolute address
(define_predicate "absolute_address_operand"
  (match_code "symbol_ref,const,const_int")
)

;; call target
(define_predicate "call_target_operand"
  (ior (match_code "symbol_ref")
       (match_operand 0 "register_operand"))
)

;; small data reference
(define_predicate "sdata_symbolic_operand"
  (match_code "symbol_ref,const")
  {
    HOST_WIDE_INT offset = 0, size = 0;
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
          tree t;
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
        gcc_unreachable();
    }
  }
)


;;-----------;;
;; Constants ;;
;;-----------;;

;; s16 constant
(define_predicate "s16_const_int_operand"
  (and (match_code "const_int")
       (match_test "IN_RANGE (INTVAL (op), -32768, 32767)"))
)

;; s12 constant
(define_predicate "s12_const_int_operand"
  (and (match_code "const_int")
       (match_test "IN_RANGE (INTVAL (op), -2048, 2047)"))
)

;; s10 constant
(define_predicate "s10_const_int_operand"
  (and (match_code "const_int")
       (match_test "IN_RANGE (INTVAL (op), -512, 511)"))
)

;; s8 constant
(define_predicate "s8_const_int_operand"
  (and (match_code "const_int")
       (match_test "IN_RANGE (INTVAL (op), -128, 127)"))
)

;; u9 constant
(define_predicate "u9_const_int_operand"
  (and (match_code "const_int")
       (match_test "IN_RANGE (INTVAL (op), 0, 511)"))
)

;; u8 constant
(define_predicate "u8_const_int_operand"
  (and (match_code "const_int")
       (match_test "IN_RANGE (INTVAL (op), 0, 255)"))
)

;; u7 constant
(define_predicate "u7_const_int_operand"
  (and (match_code "const_int")
       (match_test "IN_RANGE (INTVAL (op), 0, 127)"))
)

;; u6 constant
(define_predicate "u6_const_int_operand"
  (and (match_code "const_int")
       (match_test "IN_RANGE (INTVAL (op), 0, 63)"))
)

;; u5 constant
(define_predicate "u5_const_int_operand"
  (and (match_code "const_int")
       (match_test "IN_RANGE (INTVAL (op), 0, 31)"))
)

;; u3 constant
(define_predicate "u3_const_int_operand"
  (and (match_code "const_int")
       (match_test "IN_RANGE (INTVAL (op), 0, 7)"))
)

;; u2 constant
(define_predicate "u2_const_int_operand"
  (and (match_code "const_int")
       (match_test "IN_RANGE (INTVAL (op), 0, 3)"))
)

;; u1 constant
(define_predicate "u1_const_int_operand"
  (and (match_code "const_int")
       (match_test "IN_RANGE (INTVAL (op), 0, 1)"))
)

;; u0 constant
(define_predicate "zero_constant"
  (and (match_code "const_int,const_double,const_vector")
       (match_test "op == CONST0_RTX (mode)"))
)

;; m9 signed magnitude constant
(define_predicate "m9_const_int_operand"
  (and (match_code "const_int")
       (match_test "IN_RANGE (INTVAL (op), -255, 255)"))
)

;; constant == 2^N where N is an integer
(define_predicate "power_of_two_operand"
  (and (match_code "const_int")
       (match_test "exact_log2(INTVAL (op)) != -1"))
)

;; constant == 2^N where N is an element of {0, 1, 2, 3, 4, 5, 6, 7}
(define_predicate "addasl_const_int_operand"
  (and (match_code "const_int")
       (match_test "INTVAL (op) == (1 << 0)
                 || INTVAL (op) == (1 << 1)
                 || INTVAL (op) == (1 << 2)
                 || INTVAL (op) == (1 << 3)
                 || INTVAL (op) == (1 << 4)
                 || INTVAL (op) == (1 << 5)
                 || INTVAL (op) == (1 << 6)
                 || INTVAL (op) == (1 << 7)"))
)

;; constant that might not fit in s16
(define_predicate "immediate_not_s16_operand"
  (and (match_code "const_int,const_double,const_vector,const,label_ref,symbol_ref")
       (and (match_operand 0 "immediate_operand")
            (not (match_operand 0 "s16_const_int_operand"))))
)


;;---------------------;;
;; Memory or Registers ;;
;;---------------------;;

;; non-general purpose register or memory
(define_predicate "nongr_reg_or_memory_operand"
  (ior (match_operand 0 "nongr_register_operand")
       (match_operand 0 "memory_operand"))
)

;; conditional move destination
(define_predicate "conditional_dest_operand"
  (if_then_else (match_test "!reload_completed")
                (match_operand 0 "nonimmediate_operand")
                (ior (and (match_operand 0 "memory_operand")
                          (match_test "qdsp6_legitimate_address_p(GET_MODE (op),
                                                                  XEXP (op, 0),
                                                                  true,
                                                                  \"econd\")"))
                     (match_operand 0 "gr_register_operand")))
)


;;------------------------;;
;; Registers or Constants ;;
;;------------------------;;

;; general purpose register or s16 constant
(define_predicate "gr_or_s16_operand"
  (ior (match_operand 0 "gr_register_operand")
       (match_operand 0 "s16_const_int_operand"))
)

;; general purpose register or u6 constant
(define_predicate "gr_or_u6_operand"
  (ior (match_operand 0 "gr_register_operand")
       (match_operand 0 "u6_const_int_operand"))
)

;; general purpose register or m9 constant
(define_predicate "gr_or_m9_operand"
  (ior (match_operand 0 "gr_register_operand")
       (match_operand 0 "m9_const_int_operand"))
)

;; conditional add operand
(define_predicate "conditional_add_operand"
  (if_then_else (match_test "!reload_completed")
                (match_operand 0 "nonmemory_operand")
                (ior (match_operand 0 "gr_register_operand")
                     (ior (and (match_test "TARGET_V4_FEATURES")
                               (match_operand 0 "immediate_operand"))
                          (match_operand 0 "s8_const_int_operand"))))
)


;;---------;;
;; General ;;
;;---------;;

;; conditional move source
(define_predicate "conditional_src_operand"
  (if_then_else (match_test "!reload_completed")
                (match_operand 0 "general_operand")
                (ior (and (match_operand 0 "memory_operand")
                          (match_test "qdsp6_legitimate_address_p(GET_MODE (op),
                                                                  XEXP (op, 0),
                                                                  true,
                                                                  \"econd\")"))
                     (ior (match_operand 0 "gr_register_operand")
                          (and (match_test "GET_MODE (op) != DImode")
                               (ior (and (match_test "TARGET_V4_FEATURES")
                                         (match_operand 0 "immediate_operand"))
                                    (match_operand 0 "s12_const_int_operand"))))))
)


;;-----------;;
;; Operators ;;
;;-----------;;

;; operator used for predication
(define_predicate "predicate_operator"
  (match_code "ne,eq")
)

(define_predicate "gpr_cond_jump_operator"
  (match_code "ne,eq,ge,le")
)


;;---------------;;
;; SDATA sorting ;;
;;---------------;;

(define_predicate "GP_or_reg_operand"
  (match_operand 0 "general_operand")
  {
    return qdsp6_GP_or_reg_operand_c(op, mode);
  }
)

(define_predicate "nonimmediate_operand_with_GP"
  (match_operand 0 "nonimmediate_operand")
  {
    return qdsp6_nonimmediate_operand_with_GP_c(op, mode);
  }
)
