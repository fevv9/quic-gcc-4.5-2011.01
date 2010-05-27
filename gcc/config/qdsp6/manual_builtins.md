(define_constants [
  (UNSPEC_QDSP6_SI_to_SXTHI_asrh 900)
  (UNSPEC_QDSP6_val_for_valignb 901)
])


(define_expand "qdsp6_builtin_SI_to_SXTHI_asrh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (sign_extend:SI (unspec:HI [
           (match_operand:SI 1 "gr_register_operand" "Rg")
           ] UNSPEC_QDSP6_SI_to_SXTHI_asrh))
  )]
  ""
  {
    if(!TARGET_LITERAL_INTRINSICS){
      emit_insn(gen_ashrsi3(operands[0], operands[1], gen_int_mode(16, SImode)));
      DONE;
    }
  }
)

(define_insn "qdsp6_unspec_SI_to_SXTHI_asrh"
  [(set (match_operand:SI 0 "gr_register_operand" "=Rg")
        (sign_extend:SI (unspec:HI [
           (match_operand:SI 1 "gr_register_operand" "Rg")
           ] UNSPEC_QDSP6_SI_to_SXTHI_asrh))
  )]
  ""
  "%0 =asrh(%1)"
  [(set_attr "type" "A")]
)

(define_insn "qdsp6_builtin_val_for_valignb"
  [(set (match_operand:QI 0 "pr_register_operand" "=Rp")
        (unspec:QI [ (mem (match_operand:SI 1 "gr_register_operand" "Rg")) ] UNSPEC_QDSP6_val_for_valignb))]
  ""
  "%0 = %1 // val for valignb"
  [(set_attr "type" "S")]
)

