/* Definitions of QDSP6 target
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


/*-----------------------------------------------------------------------
This target description is used for both GCC 3.4.6 and one of the latest
versions of GCC.  This macro and some includes in the machine description
are used to switch between the two implementations.
-----------------------------------------------------------------------*/

#ifndef GCC_QDSP6_H
#define GCC_QDSP6_H


/*--------------------------------------------------------
For documentation, please see the appropriate section of
the GCC Internals Manual, which can be found at
http://gcc.gnu.org/onlinedocs/gcc-<version.triplet>/gccint
--------------------------------------------------------*/

/*-------------------------------------
Controlling the Compilation Driver, gcc
-------------------------------------*/

/* Make the -mv* options aliases for the corresponding -march= option. */
#define TARGET_OPTION_TRANSLATE_TABLE \
  {"-mv1", "-march=qdsp6v1"}, \
  {"-mv2", "-march=qdsp6v2"}, \
  {"-mv3", "-march=qdsp6v3"}, \
  {"-mv4", "-march=qdsp6v4"}

/* As specified by the ABI, plain bitfields are unsigned.  This is a hack to
   compensate for the lack of a target hook for specifying this aspect of the
   ABI.  For some reason, RMS wants this bit of implementation defined behavior
   to be consistent for GCC across targets unlike everything else commonly
   specified by ABIs. */
#define CC1_SPEC "%{G*:-G%*;:%{mbuilding-multilib:%{mG0lib:-G0}}} -funsigned-bitfields"

#define CC1PLUS_SPEC "%{G*:-G%*;:%{mbuilding-multilib:%{mG0lib:-G0}}} -funsigned-bitfields"


/*---------------------------
Run-time Target Specification
---------------------------*/

/* Define qdsp6 and __QDSP6_<architecture>__ */
#define TARGET_CPU_CPP_BUILTINS() \
  do { \
    switch(qdsp6_arch){ \
      case QDSP6_ARCH_V1: \
        builtin_define_std ("__QDSP6_V1__"); \
        builtin_define_std ("__QDSP6_ARCH__=1"); \
        break; \
      case QDSP6_ARCH_V2: \
        builtin_define_std ("__QDSP6_V2__"); \
        builtin_define_std ("__QDSP6_ARCH__=2"); \
        break; \
      case QDSP6_ARCH_V3: \
        builtin_define_std ("__QDSP6_V3__"); \
        builtin_define_std ("__QDSP6_ARCH__=3"); \
        break; \
      case QDSP6_ARCH_V4: \
        builtin_define_std ("__QDSP6_V4__"); \
        builtin_define_std ("__QDSP6_ARCH__=4"); \
        break; \
      default: \
        abort(); \
    } \
    builtin_define_std ("qdsp6"); \
    builtin_assert ("machine=qdsp6"); \
  }while(0)

/* Append (qdsp6) to the version string. */
#define TARGET_VERSION fprintf(stderr, " (qdsp6)");

#define OVERRIDE_OPTIONS \
  qdsp6_override_options()

#define OPTIMIZATION_OPTIONS(LEVEL, SIZE) \
  qdsp6_optimization_options(LEVEL, SIZE)

#define CAN_DEBUG_WITHOUT_FP 1


/*---------------------------------------------------
Defining data structures for per-function information
---------------------------------------------------*/

#define INIT_EXPANDERS \
  qdsp6_init_expanders()


/*------------
Storage Layout
------------*/

/* QDSP6 is little endian. */
#define BITS_BIG_ENDIAN 0

#define BYTES_BIG_ENDIAN 0

#define WORDS_BIG_ENDIAN 0

/* Bytes (units) are 8 bits on QDSP6. */

/* QDSP6 general purpose registers each hold 4 bytes (32 bits). */
#define UNITS_PER_WORD 4

/* QDSP6 can operate on doubleword vectors, i.e. 8 units. */
#define UNITS_PER_SIMD_WORD(MODE)   \
  (((MODE) == DFmode || (MODE) == SFmode) ? 8 : 8)

/* Pointers on QDSP6 are 32 bits (word sized). */

/* Most QDSP6 instructions operate on words. */
#define PROMOTE_MODE(MODE, UNSIGNEDP, TYPE) \
  if(GET_MODE_CLASS (MODE) == MODE_INT \
     && GET_MODE_SIZE (MODE) < GET_MODE_SIZE (SImode)){ \
      (MODE) = SImode; \
  }

/* As specified by the ABI, all arguments passed on the stack are at least word
   aligned. */
#define PARM_BOUNDARY 32

/* As specified by the ABI, SP should be 8-byte aligned upon function entry. */
#define STACK_BOUNDARY 64

/* Code must be 32-bit aligned. */
#define FUNCTION_BOUNDARY 32

/* No native data types have more than 8-byte alignment by default. */
#define BIGGEST_ALIGNMENT 64

/* GCC uses the following internal structure to represent a 
   pointer-to-member-function:

   struct {
    union {
        void (*fn)();
        ptrdiff_t vtable_index;
    };
    ptrdiff_t delta;
   };

   Generally GCC must use one bit to indicate whether the function that will be
   called through a pointer-to-member-function is virtual. 
   Normally, we assume that the low-order bit of a function pointer must always
   be zero (word aligned). Then, by ensuring that the vtable_index is odd, 
   we can distinguish which variant of the union is in use. But, on some 
   platforms function pointers can be odd, and so this doesn't work. In that 
   case, we use the low-order bit of the delta field, and shift the remainder 
   of the delta field to the left. 
   On QDSP6 use of delta field is not _needed_ but produces a better code for 
   several scenarios. Particularly for an empty class with function 
   definitions:

   (from bug 3711)

   struct S {
       int func(char)      { return 100; }
   } s;

   int main(void)
   {
      int (S::*pfc)(char)    = &S::func;
      (s.*pfc)(0);
   }

   GCC will use default alignment of "char" for 's', but might use memw/mov_si
   to access nonexistent vtable in "front" of s, resulting in potential conflict.

   When delta field is used via TARGET_PTRMEMFUNC_VBIT_LOCATION, compiler is 
   capable to determine that there is _no_ vtable to access in this case, and 
   simply optimizes out the access code. If a vtable does exist, it will be word 
   aligned by definition.
   */  
#define TARGET_PTRMEMFUNC_VBIT_LOCATION ptrmemfunc_vbit_in_delta


/* This is only used for internal sorting during packetization
   and eventually need to be replaced with a linked list or any
   other scalable method of bookkeeping */ 
#define MAX_NUM_EDGES_IN_BB	1024

/* QDSP6 has byte-sized stores. */

#define DATA_ALIGNMENT(TYPE, ALIGN) \
  qdsp6_data_alignment(TYPE, ALIGN)

#define CONSTANT_ALIGNMENT(CONSTANT, ALIGN) \
  qdsp6_constant_alignment(CONSTANT, ALIGN)

#define LOCAL_ALIGNMENT(TYPE, ALIGN) \
  qdsp6_local_alignment(TYPE, ALIGN)

/* Mis-aligned accesses are exceptions. */
#define STRICT_ALIGNMENT 1

/* As specified by the ABI, the type used to declare a bitfield affects the
  alignment of the containing struct as if a member of that type were present.
  Also, bitfields do not cross the alignment boundaries of their type. */
#define PCC_BITFIELD_TYPE_MATTERS 1

/* QDSP6 emulates IEEE floating point. */

/* The prevailing floating point rounding mode is round towards nearest. */


/*----------------------------------
Layout of Source Language Data Types
----------------------------------*/

/* On QDSP6,
   ints         are word sized,
   shorts       are half-word sized,
   longs        are word sized,
   long longs   are doubleword sized,
   chars        are 8 bits,
   bools        are 8 bits,
   floats       are word sized,
   doubles      are doubleword sized, and
   long doubles are doubleword sized. */

/* As specified by the ABI, the "char" type behaves like the "unsigned char"
   type. */
#define DEFAULT_SIGNED_CHAR 0

/* GCC uses the following internal structure to represent a 
   pointer-to-member-function:

   struct {
    union {
        void (*fn)();
        ptrdiff_t vtable_index;
    };
    ptrdiff_t delta;
   };

   Generally GCC must use one bit to indicate whether the function that will be
   called through a pointer-to-member-function is virtual. 
   Normally, we assume that the low-order bit of a function pointer must always
   be zero (word aligned). Then, by ensuring that the vtable_index is odd, 
   we can distinguish which variant of the union is in use. But, on some 
   platforms function pointers can be odd, and so this doesn't work. In that 
   case, we use the low-order bit of the delta field, and shift the remainder 
   of the delta field to the left. 
   On QDSP6 use of delta field is not _needed_ but produces a better code for 
   several scenarios. Particularly for an empty class with function 
   definitions:

   (from bug 3711)

   struct S {
       int func(char)      { return 100; }
   } s;

   int main(void)
   {
      int (S::*pfc)(char)    = &S::func;
      (s.*pfc)(0);
   }

   GCC will use default alignment of "char" for 's', but might use memw/mov_si
   to access nonexistent vtable in "front" of s, resulting in potential conflict.

   When delta field is used via TARGET_PTRMEMFUNC_VBIT_LOCATION, compiler is 
   capable to determine that there is _no_ vtable to access in this case, and 
   simply optimizes out the access code. If a vtable does exist, it will be word 
   aligned by definition.
   */  
#define TARGET_PTRMEMFUNC_VBIT_LOCATION ptrmemfunc_vbit_in_delta


/*--------------------------------
Basic Characteristics of Registers
--------------------------------*/

/* 32 GPRs, 4 predicate regs, 8 CRs (sa0/lc0, sa1/lc1, m0/m1, usr, ugp), and
   fake frame pointer and argument pointer registers */
#define FIRST_PSEUDO_REGISTER (32 + 4 + 8 + 2)

#define FIXED_REGISTERS \
  { \
    0, 0, 0, 0, 0, 0, 0, 0, /*  0 -  7 */ \
    0, 0, 0, 0, 0, 0, 0, 0, /*  8 - 15 */ \
    0, 0, 0, 0, 0, 0, 0, 0, /* 16 - 23 */ \
    0, 0, 0, 0, 0, 1, 1, 0, /* 24 - 31 */ \
    0, 0, 0, 0,             /* p0 - p3 */ \
    1, 1, 1, 1, 1, 1, 1, 1, /* sa0, lc0, sa1, lc1, m0, m1, usr, ugp */ \
    1, 1,                   /* fake _fp and _ap */ \
  }

#define CALL_USED_REGISTERS \
  { \
    1, 1, 1, 1, 1, 1, 1, 1, /*  0 -  7 */ \
    1, 1, 1, 1, 1, 1, 1, 1, /*  8 - 15 */ \
    1, 1, 1, 1, 1, 1, 1, 1, /* 16 - 23 */ \
    0, 0, 0, 0, 1, 1, 1, 1, /* 24 - 31 */ \
    1, 1, 1, 1,             /* p0 - p3 */ \
    1, 1, 1, 1, 1, 1, 1, 1, /* sa0, lc0, sa1, lc1, m0, m1, usr, ugp */ \
    1, 1,                   /* fake _fp and _ap */ \
  }

#define CONDITIONAL_REGISTER_USAGE \
  qdsp6_conditional_register_usage();


/*-------------------------
How Values Fit in Registers
-------------------------*/

/* Values are stored in the smallest number of word sized registers needed to
   fit the mode. */
#define HARD_REGNO_NREGS(REGNO, MODE) \
  (P_REGNO_P (REGNO) ? 1 \
   : ((GET_MODE_SIZE (MODE) + UNITS_PER_WORD - 1) / UNITS_PER_WORD))

/* For QDSP6, register pairs must start on an even numbered register. */
#define HARD_REGNO_MODE_OK(REGNO, MODE) \
  (P_REGNO_P (REGNO) \
   ? ((MODE) == BImode || (MODE) == QImode) \
   : G_REGNO_P(REGNO) \
     ? (GET_MODE_SIZE(MODE) > UNITS_PER_WORD ? (REGNO) % 2 == 0 : 1) \
     : (REGNO) == FRAME_POINTER_REGNUM || (REGNO) == ARG_POINTER_REGNUM \
       ? GET_MODE_CLASS (MODE) == MODE_INT \
       : 0 /* HARD_REGNO_MODE_OK(control-reg) == 0 */)

/* ??? not sure about this one: */
#define MODES_TIEABLE_P(MODE1, MODE2) \
  (GET_MODE_CLASS (MODE1) == GET_MODE_CLASS (MODE2) \
   && (((MODE1) == BImode) == ((MODE2) == BImode)))

/* ??? Does this affect us? */
#define AVOID_CCMODE_COPIES 1


/*---------------------
Handling Leaf Functions
---------------------*/

/* QDSP6 does not have register windows. */


/*-------------------------
Registers That Form a Stack
-------------------------*/

/* QDSP6 does not have any stack-like registers. */


/*--------------
Register Classes
--------------*/

enum reg_class {
  NO_REGS,
  GENERAL_REGS,           /* registers r0 through r31 */
  PREDICATE_REGS,         /* predicates p0 through p3 */
  CONTROL_REGS,           /* sa0, lc0, sa1, lc1, m0, m1, usr, ugp */
  FAKE_REGS,              /* _fp, _ap */
  ALL_REGS,
  LIM_REG_CLASSES
};

#define N_REG_CLASSES ((int) LIM_REG_CLASSES)

#define REG_CLASS_NAMES       \
  {                           \
    "NO_REGS",                \
    "GENERAL_REGS",           \
    "PREDICATE_REGS",         \
    "CONTROL_REGS",           \
    "FAKE_REGS",              \
    "ALL_REGS"                \
  }

#define REG_CLASS_CONTENTS       \
  {                              \
    /* NO_REGS */                \
    {0x00000000, 0x00000},       \
    /* GENERAL_REGS */           \
    {0xffffffff, 0x00000},       \
    /* PREDICATE_REGS */         \
    {0x00000000, 0x0000f},       \
    /* CONTROL_REGS */           \
    {0x00000000, 0x00ff0},       \
    /* FAKE_REGS */              \
    {0x00000000, 0x03000},       \
    /* ALL_REGS */               \
    {0xffffffff, 0x03fff},       \
  }

#define REGNO_REG_CLASS(REGNO) \
  ( (REGNO) <  32 ? GENERAL_REGS \
  : (REGNO) < (32 + 4) ? PREDICATE_REGS \
  : (REGNO) < (32 + 4 + 8) ? CONTROL_REGS \
  : (REGNO) < (32 + 4 + 8 + 2) ? FAKE_REGS \
  : ALL_REGS)

/* In base+offset and base+index addressing, the base must be a general purpose
   register. */
#define BASE_REG_CLASS GENERAL_REGS

/* In base+index addressing, the index must be a general purpose register. */
#define INDEX_REG_CLASS \
  ((TARGET_V4_FEATURES && TARGET_BASE_PLUS_INDEX) ? GENERAL_REGS : NO_REGS)

#define CANNOT_CHANGE_MODE_CLASS(FROM, TO, CLASS) \
  qdsp6_cannot_change_mode_class(FROM, TO, CLASS)

/* The following macro defines cover classes for Integrated Register
   Allocator.  Cover classes is a set of non-intersected register
   classes covering all hard registers used for register allocation
   purpose.  Any move between two registers of a cover class should be
   cheaper than load or store of the registers.  The macro value is
   array of register classes with LIM_REG_CLASSES used as the end
   marker.  */
#define IRA_COVER_CLASSES \
{                 \
  ALL_REGS,       \
  LIM_REG_CLASSES \
}


/* used by CONSTRAINT_LEN
   See REG_CLASS_FROM_CONSTRAINT for meanings. */
#define CONSTRAINT_LEN_FOR_R(CHAR, STR) \
  ( (STR)[1] == 'g' ? 2 \
  : (STR)[1] == 'p' ? 2 \
  : (STR)[1] == 'c' ? 2 \
  : DEFAULT_CONSTRAINT_LEN(CHAR, STR))

/* used by CONSTRAINT_LEN
   See qdsp6_const_ok_for_constraint_p for meanings. */
#define CONSTRAINT_LEN_FOR_I(CHAR, STR) \
  ( (   (STR)[1] == 's' \
     || (STR)[1] == 'u' \
     || (STR)[1] == 'n' \
     || (STR)[1] == 'm') \
    && ISDIGIT ((STR)[2]) ? ISDIGIT ((STR)[3]) ? 4 : 3 \
  : DEFAULT_CONSTRAINT_LEN(CHAR, STR))

/* used by CONSTRAINT_LEN
   See qdsp6_const_ok_for_constraint_p for meanings. */
#define CONSTRAINT_LEN_FOR_J(CHAR, STR) \
  ( (   (STR)[1] == 's' \
     || (STR)[1] == 'u' \
     || (STR)[1] == 'n' \
     || (STR)[1] == 'm') \
    && ISDIGIT ((STR)[2]) \
    && (((STR)[3] == '_' && ISDIGIT ((STR)[4])) \
        || (ISDIGIT ((STR)[3]) && (STR)[4] == '_' && ISDIGIT ((STR)[5]))) \
  ? (STR)[3] == '_' ? 5 : 6 \
  : DEFAULT_CONSTRAINT_LEN(CHAR, STR))

/* does not check the first letter in STR */
#define QDSP6_CONSTRAINT_P(STR, CONSTRAINT) \
  (!strncmp(&(STR)[1], #CONSTRAINT, strlen(#CONSTRAINT)))

/* Gotta love preprocessing. */
#define QDSP6_CONSTRAINT_LEN(STR, CONSTRAINT) \
  QDSP6_CONSTRAINT_P(STR, CONSTRAINT) ? (signed) strlen(#CONSTRAINT) + 1 :

/* See qdsp6_const_ok_for_constraint_p for meanings. */
#define QDSP6_KOOKY_KONSTANT_LENS(STR) \
  QDSP6_CONSTRAINT_LEN(STR, -1) \
  QDSP6_CONSTRAINT_LEN(STR, 01) \
  QDSP6_CONSTRAINT_LEN(STR, 16) \
  QDSP6_CONSTRAINT_LEN(STR, 32) \
  QDSP6_CONSTRAINT_LEN(STR, u7p1) \
  QDSP6_CONSTRAINT_LEN(STR, s8p1) \
  QDSP6_CONSTRAINT_LEN(STR, u5_3p8) \
  QDSP6_CONSTRAINT_LEN(STR, u9p1) \
  QDSP6_CONSTRAINT_LEN(STR, s10p1) \
  QDSP6_CONSTRAINT_LEN(STR, s8s8) \
  QDSP6_CONSTRAINT_LEN(STR, onehot32) \
  QDSP6_CONSTRAINT_LEN(STR, onenot32)

/* used by CONSTRAINT_LEN */
#define CONSTRAINT_LEN_FOR_K(CHAR, STR) \
  (QDSP6_KOOKY_KONSTANT_LENS(STR) DEFAULT_CONSTRAINT_LEN(CHAR, STR))

/* See qdsp6_legitimate_address_p for meanings. */
#define QDSP6_MEM_TYPE_LENS(STR) \
  QDSP6_CONSTRAINT_LEN(STR, noext) \
  QDSP6_CONSTRAINT_LEN(STR, cond) \
  QDSP6_CONSTRAINT_LEN(STR, econd) \
  QDSP6_CONSTRAINT_LEN(STR, si) \
  QDSP6_CONSTRAINT_LEN(STR, csi) \
  QDSP6_CONSTRAINT_LEN(STR, memop) \
  QDSP6_CONSTRAINT_LEN(STR, ememop) \
  QDSP6_CONSTRAINT_LEN(STR, dm3)    \
  QDSP6_CONSTRAINT_LEN(STR, dm4)    \
  QDSP6_CONSTRAINT_LEN(STR, dmsp5)  \
  QDSP6_CONSTRAINT_LEN(STR, dmsp6)

/* used by CONSTRAINT_LEN */
#define CONSTRAINT_LEN_FOR_A(CHAR, STR) \
  (QDSP6_MEM_TYPE_LENS(STR) DEFAULT_CONSTRAINT_LEN(CHAR, STR))

#define CONSTRAINT_LEN(CHAR, STR) \
  ( (CHAR) == 'R' ? CONSTRAINT_LEN_FOR_R(CHAR, STR) \
  : (CHAR) == 'I' ? CONSTRAINT_LEN_FOR_I(CHAR, STR) \
  : (CHAR) == 'J' ? CONSTRAINT_LEN_FOR_J(CHAR, STR) \
  : (CHAR) == 'K' ? CONSTRAINT_LEN_FOR_K(CHAR, STR) \
  : (CHAR) == 'A' ? CONSTRAINT_LEN_FOR_A(CHAR, STR) \
  : DEFAULT_CONSTRAINT_LEN(CHAR, STR))

/* Rg  means general purpose register (r0-r31)
   Rp  means predicate register (p0-p3)
   Rc  means control register (sa0, lc0, sa1, lc1, m0, m1) */
#define REG_CLASS_FROM_CONSTRAINT(CHAR, STR) \
  ( (CHAR) != 'R' ? NO_REGS \
  : (STR)[1] == 'g' ? GENERAL_REGS \
  : (STR)[1] == 'p' ? PREDICATE_REGS \
  : (STR)[1] == 'c' ? CONTROL_REGS \
  : NO_REGS)

/* In base+offset addressing, the base must be a general purpose register. */
#define REGNO_OK_FOR_BASE_P(NUM) ((NUM) < 32)

/* QDSP6 does not have base+index addressing. */
#define REGNO_OK_FOR_INDEX_P(NUM) 0

#define PREFERRED_RELOAD_CLASS(X, CLASS) CLASS

/* ??? maybe try this with predicates? */
/*#define SMALL_REGISTER_CLASSES*/
/*#define CLASS_LIKELY_SPILLED_P(CLASS)*/

#define CLASS_MAX_NREGS(CLASS, MODE) HARD_REGNO_NREGS (0, MODE)

#define CONST_OK_FOR_CONSTRAINT_P(VALUE, C, STR) \
  qdsp6_const_ok_for_constraint_p(VALUE, C, STR)

/* used by CONST_DOUBLE_OK_FOR_LETTER_P */
/* true for 0 */
#define CONST_DOUBLE_OK_FOR_G(VALUE) \
  ((GET_MODE (VALUE) == VOIDmode \
    && CONST_DOUBLE_LOW (VALUE) == 0 \
    && CONST_DOUBLE_HIGH (VALUE) == 0) \
   || ((GET_MODE (VALUE) == SFmode \
        || GET_MODE (VALUE) == DFmode) \
       && (VALUE) == CONST0_RTX (GET_MODE (VALUE))))

/* Only use 'G' and 'H'. */
#define CONST_DOUBLE_OK_FOR_LETTER_P(VALUE, C) \
  ( (C) == 'G' ? CONST_DOUBLE_OK_FOR_G (VALUE) \
  : 0)

/* used by EXTRA_CONSTRAINT */
#define EXTRA_CONSTRAINT_FOR_Q(VALUE) \
  (CONSTANT_P (VALUE))

/* used by EXTRA_CONSTRAINT */
#define EXTRA_CONSTRAINT_FOR_A(VALUE, CONSTRAINT) \
  (GET_CODE (VALUE) == MEM \
   && qdsp6_legitimate_address_p(GET_MODE (VALUE), XEXP (VALUE, 0), \
                                 REG_OK_STRICT_P, #CONSTRAINT))

/* Don't use 'E'-'P' 'V' 'X' 'g' 'i' 'm' 'n' 'o' 'p' 'r' 's' for the initial
   character.

   Q  is for a symbol or label.
   A* is for MEMs with reduced addressing modes.  See qdsp6_legitimate_address_p
      for meanings. */
#define EXTRA_CONSTRAINT_STR(VALUE, C, STR) \
  ( (C) == 'Q' ? EXTRA_CONSTRAINT_FOR_Q(VALUE) \
  : (C) == 'A' ? \
      QDSP6_CONSTRAINT_P (STR, noext)  ? EXTRA_CONSTRAINT_FOR_A(VALUE, noext) \
    : QDSP6_CONSTRAINT_P (STR, cond)   ? EXTRA_CONSTRAINT_FOR_A(VALUE, cond) \
    : QDSP6_CONSTRAINT_P (STR, econd)  ? EXTRA_CONSTRAINT_FOR_A(VALUE, econd) \
    : QDSP6_CONSTRAINT_P (STR, si)     ? EXTRA_CONSTRAINT_FOR_A(VALUE, si) \
    : QDSP6_CONSTRAINT_P (STR, csi)    ? EXTRA_CONSTRAINT_FOR_A(VALUE, csi) \
    : QDSP6_CONSTRAINT_P (STR, memop)  ? EXTRA_CONSTRAINT_FOR_A(VALUE, memop) \
    : QDSP6_CONSTRAINT_P (STR, ememop) ? EXTRA_CONSTRAINT_FOR_A(VALUE, ememop) \
    : QDSP6_CONSTRAINT_P (STR, dm3)     ? EXTRA_CONSTRAINT_FOR_A(VALUE, dm3) \
    : QDSP6_CONSTRAINT_P (STR, dm4)     ? EXTRA_CONSTRAINT_FOR_A(VALUE, dm4) \
    : QDSP6_CONSTRAINT_P (STR, dmsp5)     ? EXTRA_CONSTRAINT_FOR_A(VALUE, dmsp5) \
    : QDSP6_CONSTRAINT_P (STR, dmsp6)     ? EXTRA_CONSTRAINT_FOR_A(VALUE, dmsp6) \
    : 0 \
  : 0)

#define EXTRA_MEMORY_CONSTRAINT(C, STR) \
  ((C) == 'A' \
   && (   QDSP6_CONSTRAINT_P (STR, noext) \
       || QDSP6_CONSTRAINT_P (STR, cond) \
       || QDSP6_CONSTRAINT_P (STR, econd) \
       || QDSP6_CONSTRAINT_P (STR, si) \
       || QDSP6_CONSTRAINT_P (STR, csi) \
       || QDSP6_CONSTRAINT_P (STR, memop) \
       || QDSP6_CONSTRAINT_P (STR, ememop) \
       || QDSP6_CONSTRAINT_P (STR, dm)))


/*----------------
Basic Stack Layout
----------------*/

/* See the comment in qdsp6.c containing "QDSP6 stack frames look like:" for a
   diagram of stack frames on QDSP6. */
#define STACK_GROWS_DOWNWARD 1
#define FRAME_GROWS_DOWNWARD 1

#define TARGET_LIBC_PROVIDES_SSP 1

#define STARTING_FRAME_OFFSET 0

#define FIRST_PARM_OFFSET(FUNDECL) 0

#define RETURN_ADDR_RTX(COUNT, FRAMEADDR) \
  qdsp6_return_addr_rtx(COUNT, FRAMEADDR)

#define INCOMING_RETURN_ADDR_RTX gen_rtx_REG (Pmode, LINK_REGNUM)

#define INCOMING_FRAME_SP_OFFSET 0


/*------------------------
Exception Handling Support
------------------------*/

#define EH_RETURN_DATA_REGNO(N) \
  ((N) < 4 ? (N) + (qdsp6_abi != QDSP6_ABI_1 ? 0 : 20) : INVALID_REGNUM)

#define EH_RETURN_STACKADJ_RTX gen_rtx_REG (Pmode, 28)

#define EH_RETURN_HANDLER_RTX \
  gen_rtx_MEM (Pmode, plus_constant(hard_frame_pointer_rtx, UNITS_PER_WORD))

/* ??? do we want this? */
/*#define ASM_PREFERRED_EH_DATA_FORMAT(CODE, GLOBAL)*/
/*#define ASM_MAYBE_OUTPUT_ENCODED_ADDR_RTX(FILE, ENCODING, SIZE, ADDR, DONE)*/


/*------------------------------------
Registers That Address the Stack Frame
------------------------------------*/

#define STACK_POINTER_REGNUM 29

/* Fake frame pointer register that will always be eliminated */
#define FRAME_POINTER_REGNUM 44

#define HARD_FRAME_POINTER_REGNUM 30

/* Fake argument pointer register that will always be eliminated */
#define ARG_POINTER_REGNUM 45

/* needs to be caller-save and not arg? */
#define STATIC_CHAIN_REGNUM 28

/*#define DWARF_FRAME_REGISTERS*/ /* ??? 14? */

#define DWARF_FRAME_RETURN_COLUMN DWARF_FRAME_REGNUM (LINK_REGNUM)


/* Eliminate the fake frame pointer and argument pointer and use the stack
   pointer instead of the frame pointer whenever possible. */
#define ELIMINABLE_REGS                                \
  {                                                    \
    {ARG_POINTER_REGNUM,   STACK_POINTER_REGNUM},      \
    {FRAME_POINTER_REGNUM, STACK_POINTER_REGNUM},      \
    {HARD_FRAME_POINTER_REGNUM, STACK_POINTER_REGNUM}, \
    {ARG_POINTER_REGNUM,   HARD_FRAME_POINTER_REGNUM}, \
    {FRAME_POINTER_REGNUM, HARD_FRAME_POINTER_REGNUM}  \
  }

#define INITIAL_ELIMINATION_OFFSET(FROM, TO, OFFSET) \
  (OFFSET) = qdsp6_initial_elimination_offset(FROM, TO)


/*-------------------------------------
Passing Function Arguments on the Stack
-------------------------------------*/

/* We allocate stack for all stack-passed arguments in one go instead of pushing
   them. */
#define PUSH_ARGS 0

/* All of the space needed to pass arguments is allocated in the prologue. */
#define ACCUMULATE_OUTGOING_ARGS 1

/* Calls leave the caller's frame alone. */
#define RETURN_POPS_ARGS(FUNDECL, FUNTYPE, STACK_SIZE) 0

#define CALL_POPS_ARGS(CUM) 0


/*----------------------------
Passing Arguments in Registers
----------------------------*/

#define FUNCTION_ARG(CUM, MODE, TYPE, NAMED) \
  qdsp6_function_arg(CUM, MODE, TYPE, NAMED)

/* On the QDSP6 this value is an accumulating count of the number of argument
   registers that have been filled with argument values or skipped. */
#define CUMULATIVE_ARGS int

#define INIT_CUMULATIVE_ARGS(CUM, FNTYPE, LIBNAME, INDIRECT, N_NAMED_ARGS) \
  (CUM) = 0

#define FUNCTION_ARG_ADVANCE(CUM, MODE, TYPE, NAMED) \
  (CUM) = qdsp6_function_arg_advance(CUM, MODE, TYPE, NAMED)

/* Align stack arguments to the minimum of PARM_BOUNDARY and the alignment of
   the type. */
#define FUNCTION_ARG_BOUNDARY(MODE, TYPE) \
  ((TYPE) \
   ? ((TYPE_ALIGN (TYPE) <= PARM_BOUNDARY) \
      ? PARM_BOUNDARY \
      : TYPE_ALIGN (TYPE)) \
   : ((GET_MODE_ALIGNMENT (MODE) <= PARM_BOUNDARY) \
      ? PARM_BOUNDARY \
      : GET_MODE_ALIGNMENT (MODE)))

#define FUNCTION_ARG_REGNO_P(REGNO) \
  (IN_RANGE ((REGNO), FIRST_ARG_REGNUM, \
                      FIRST_ARG_REGNUM + QDSP6_NUM_ARG_REGS - 1))


/*-------------------------------------
How Scalar Function Values Are Returned
-------------------------------------*/

#define LIBCALL_VALUE(MODE) gen_rtx_REG (MODE, RETURN_VALUE_REGNUM)

#define FUNCTION_VALUE_REGNO_P(REGNO) ((REGNO) == RETURN_VALUE_REGNUM)


/*---------------------------
How Large Values Are Returned
---------------------------*/

/* Structs that fit in a register or register pair should be returned in one. */
#define DEFAULT_PCC_STRUCT_RETURN 0


/*----------------------------
How big is the largest possible alignment 
due to a declaration could be
----------------------------*/ 
#define DEFAULT_LARGEST_ALIGNMENT 1024

/*---------------------
Function Entry and Exit
---------------------*/

/* ??? maybe? */
/*#define EXIT_IGNORE_STACK*/

#define TRAMPOLINE_SIZE 0

/* The link regsiter is live across leaf functions that do not use
   allocframe. */
#define EPILOGUE_USES(REGNO) ((REGNO) == LINK_REGNUM)

/* ??? maybe? */
/*#define EH_USES(REGNO)*/


/*---------------------------
Generating Code for Profiling
---------------------------*/

#define FUNCTION_PROFILER(FILE, LABELNO) fprintf(FILE, "\tcall mcount\n");

/* ??? dunno */
#define NO_PROFILE_COUNTERS 1


/*--------------
Addressing Modes
--------------*/

#define HAVE_PRE_INCREMENT 0

#define HAVE_PRE_DECREMENT 0

#define HAVE_POST_INCREMENT 1

#define HAVE_POST_DECREMENT 1

#define HAVE_PRE_MODIFY_DISP 0

#define HAVE_POST_MODIFY_DISP 1

#define HAVE_PRE_MODIFY_REG 0

#define HAVE_POST_MODIFY_REG 0

/* ??? What happens if I change this to CONSTANT_P (X)? */
/*#define CONSTANT_ADDRESS_P(X) (GET_CODE (X) == LABEL_REF)*/
#define CONSTANT_ADDRESS_P(X) CONSTANT_P (X)

/* QDSP6 V4 and later has base + index addressing. */
#define MAX_REGS_PER_ADDRESS 2

#ifdef REG_OK_STRICT
#define REG_OK_STRICT_P true
#else
#define REG_OK_STRICT_P false
#endif

#define GO_IF_LEGITIMATE_ADDRESS(MODE, X, LABEL) \
  if(qdsp6_legitimate_address_p(MODE, X, REG_OK_STRICT_P, "m")){ \
    goto LABEL; \
  }

extern int symbol_mentioned_p (rtx x);
extern int label_mentioned_p (rtx x);

#define PIC_OFFSET_TABLE_REGNUM (flag_pic ? 24 : INVALID_REGNUM)

#define LEGITIMATE_PIC_OPERAND_P(X)   \
  qdsp6_legitimate_pic_operand_p(X)

#define GO_IF_MODE_DEPENDENT_ADDRESS(ADDR, LABEL) \
  if(GET_CODE (ADDR) == POST_INC || GET_CODE (ADDR) == POST_DEC){ \
    goto LABEL; \
  }

#define LEGITIMATE_CONSTANT_P(X) 1


/*----------------
Anchored Addresses
----------------*/

/* ??? maybe? */


/*-------------------------------------
Describing Relative Costs of Operations
-------------------------------------*/

/* Non general purpose transfers have slot restrictions. */
#define REGISTER_MOVE_COST(MODE, FROM, TO)               \
  ( FROM == GENERAL_REGS   ? ( TO == GENERAL_REGS   ? 2  \
                             : TO == PREDICATE_REGS ? 3  \
                             :     /*CONTROL_REGS*/   3) \
  : FROM == PREDICATE_REGS ? ( TO == GENERAL_REGS   ? 3  \
                             : TO == PREDICATE_REGS ? 6  \
                             :     /*CONTROL_REGS*/   6) \
  :       /*CONTROL_REGS*/   ( TO == GENERAL_REGS   ? 3  \
                             : TO == PREDICATE_REGS ? 6  \
                             :     /*CONTROL_REGS*/   6))

/* Loads and stores are cheap on QDSP6.  Yay, IMT. */
#define MEMORY_MOVE_COST(MODE, CLASS, IN) 4

/* Branches are very cheap on QDSP6, but they restrict scheduling. */
#define BRANCH_COST(speed_p, predictable_p) (speed_p ? (predictable_p ? 1 : 3) : (predictable_p ? 1 : 3))

/* Load and store cycles are independent of access size. */
#define SLOW_BYTE_ACCESS 1

/* V4's store-immediate instructions allow efficient copying of constant
   strings. */
#define STORE_BY_PIECES_P(SIZE, ALIGNMENT) \
  qdsp6_store_by_pieces_p(SIZE, ALIGNMENT)

/* Direct calls can be executed on more slots than indirect calls. */
#define NO_FUNCTION_CSE 1


/*--------------------------------------------------
Dividing the Output into Sections (Texts, Data, ...)
--------------------------------------------------*/

#define TEXT_SECTION_ASM_OP "\t.text"

#define DATA_SECTION_ASM_OP "\t.data"

#define SDATA_SECTION_ASM_OP "\t.section .sdata"

#define BSS_SECTION_ASM_OP "\t.section .bss"

#define SBSS_SECTION_ASM_OP "\t.section .sbss"


/*----------------------------------------
The Overall Framework of an Assembler File
----------------------------------------*/

#define ASM_COMMENT_START "//"

#define ASM_APP_ON "//APP\n"

#define ASM_APP_OFF "//NO_APP\n"


/*-------------------------------
Output of Uninitialized Variables
-------------------------------*/

#define ASM_OUTPUT_ALIGNED_DECL_COMMON(STREAM, DECL, NAME, SIZE, ALIGNMENT) \
  qdsp6_asm_output_aligned_decl_common(STREAM, DECL, NAME, SIZE, ALIGNMENT)

#define ASM_OUTPUT_ALIGNED_DECL_LOCAL(STREAM, DECL, NAME, SIZE, ALIGNMENT) \
  qdsp6_asm_output_aligned_decl_local(STREAM, DECL, NAME, SIZE, ALIGNMENT)


/*-----------------------------
Output and Generation of Labels
-----------------------------*/

/* used by the default version of TARGET_ASM_GLOBALIZE_LABEL */
#define GLOBAL_ASM_OP "\t.globl "


/*------------------------------
Output of Assembler Instructions
------------------------------*/

#define REGISTER_NAMES                                      \
  { /* general purpose registers */                         \
     "r0",  "r1",  "r2",  "r3",  "r4",  "r5",  "r6",  "r7", \
     "r8",  "r9", "r10", "r11", "r12", "r13", "r14", "r15", \
    "r16", "r17", "r18", "r19", "r20", "r21", "r22", "r23", \
    "r24", "r25", "r26", "r27", "r28", "r29", "r30", "r31", \
    /* predicate registers */                               \
    "p0", "p1", "p2", "p3",                                 \
    /* control registers */                                 \
    "sa0", "lc0", "sa1", "lc1", "m0", "m1", "usr", "ugp",   \
    /* fake frame pointer and argument pointer */           \
    "_fp", "_ap"                                            \
  }

#define ADDITIONAL_REGISTER_NAMES \
  { \
    {"sp", 29}, \
    {"fp", 30}, \
    {"lr", 31}, \
  }

#define ASM_OUTPUT_OPCODE(STREAM, PTR) \
   (PTR) = qdsp6_asm_output_opcode(STREAM, PTR)

#define FINAL_PRESCAN_INSN(INSN, OPVEC, NOPERANDS) \
  qdsp6_final_prescan_insn(INSN, OPVEC, NOPERANDS)

#define PRINT_OPERAND(STREAM, X, CODE) \
  qdsp6_print_operand(STREAM, X, CODE)

#define PRINT_OPERAND_ADDRESS(STREAM, X) \
  qdsp6_print_operand_address(STREAM, X)


/*-----------------------
Output of Dispatch Tables
-----------------------*/

#define ASM_OUTPUT_ADDR_DIFF_ELT(STREAM, BODY, VALUE, REL) \
  fprintf(STREAM, "\t.word .L%d-.L%d\n", VALUE, REL)

#define ASM_OUTPUT_ADDR_VEC_ELT(STREAM, VALUE) \
  fprintf(STREAM, "\t.word .L%d\n", VALUE)


/*------------------------------
Assembler Commands for Alignment
------------------------------*/

#define ASM_OUTPUT_ALIGN(STREAM, POWER) \
  fprintf((STREAM), "\t.p2align %d\n", (POWER))

#define ASM_OUTPUT_MAX_SKIP_ALIGN(STREAM, POWER, MAX_SKIP) \
  fprintf((STREAM), "\t.p2align %d,,%d\n", (POWER), (MAX_SKIP))

#define ASM_OUTPUT_SUBSECTION(STREAM, POWER) \
  fprintf((STREAM), "\t.subsection -%d\n", (POWER))

/*----------------------
Miscellaneous Parameters
----------------------*/

#define CASE_VECTOR_MODE Pmode

/* ??? smaller? */
/*#define CASE_VALUES_THRESHOLD*/

#define WORD_REGISTER_OPERATIONS 1

/* ??? maybe? */
/*#define SHORT_IMMEDIATES_SIGN_EXTEND*/

#define MOVE_MAX 8

#define TRULY_NOOP_TRUNCATION(OUTPREC, INPREC) 1

/* ??? const1_rtx? */
/*#define VECTOR_STORE_FLAG_VALUE(MODE)*/

#define CLZ_DEFINED_VALUE_AT_ZERO(MODE, VALUE) ((VALUE) = 32)

#define CTZ_DEFINED_VALUE_AT_ZERO(MODE, VALUE) ((VALUE) = 32)

#define Pmode SImode

#define FUNCTION_MODE HImode

/* ??? play with this? */
/*#define MAX_CONDITIONAL_EXECUTE*/

/* Allow querying the cpu units */
#define CPU_UNITS_QUERY 1


/*------------
QDSP6 specific
------------*/

/* Don't include this section in code that is not part of GCC. */
#ifndef USED_FOR_TARGET

/* wrapper for QDSP6 specific changes outside the back-end */
#define TARGET_QDSP6

/* option handling code */
enum qdsp6_architecture {
  QDSP6_ARCH_V1,
  QDSP6_ARCH_V2,
  QDSP6_ARCH_V3,
  QDSP6_ARCH_V4,
  NUM_QDSP6_ARCH,
  QDSP6_ARCH_UNSPECIFIED
};

extern enum qdsp6_architecture qdsp6_arch;

#define QDSP6_FEAT_V1 (1 << QDSP6_ARCH_V1)
#define QDSP6_FEAT_V2 (1 << QDSP6_ARCH_V2)
#define QDSP6_FEAT_V3 (1 << QDSP6_ARCH_V3)
#define QDSP6_FEAT_V4 (1 << QDSP6_ARCH_V4)

extern int qdsp6_features;

#define TARGET_V1_FEATURES ((qdsp6_features & QDSP6_FEAT_V1) != 0)
#define TARGET_V2_FEATURES ((qdsp6_features & QDSP6_FEAT_V2) != 0)
#define TARGET_V3_FEATURES ((qdsp6_features & QDSP6_FEAT_V3) != 0)
#define TARGET_V4_FEATURES ((qdsp6_features & QDSP6_FEAT_V4) != 0)

struct qdsp6_arch_table_entry {
  const char *const name;
  const enum qdsp6_architecture arch;
  const int features;
};

#define QDSP6_ARCH_TABLE_INITIALIZER \
  { \
    {"qdsp6v1", QDSP6_ARCH_V1,   QDSP6_FEAT_V1}, \
    {"qdsp6v2", QDSP6_ARCH_V2,   QDSP6_FEAT_V1 \
                               | QDSP6_FEAT_V2}, \
    {"qdsp6v3", QDSP6_ARCH_V3,   QDSP6_FEAT_V1 \
                               | QDSP6_FEAT_V2 \
                               | QDSP6_FEAT_V3}, \
    {"qdsp6v4", QDSP6_ARCH_V4,   QDSP6_FEAT_V1 \
                               | QDSP6_FEAT_V2 \
                               | QDSP6_FEAT_V3 \
                               | QDSP6_FEAT_V4} \
  }

#define QDSP6_ARCH_TABLE_DEFAULT_INDEX QDSP6_ARCH_V2

enum qdsp6_abi {
  QDSP6_ABI_1,
  QDSP6_ABI_2,
  QDSP6_ABI_LINUX,
  NUM_QDSP6_ABI,
  QDSP6_ABI_UNSPECIFIED
};

extern enum qdsp6_abi qdsp6_abi;

struct qdsp6_abi_table_entry {
  const char *const name;
  const enum qdsp6_abi abi;
};

#define QDSP6_ABI_TABLE_INITIALIZER \
  { \
    {"abi1", QDSP6_ABI_1}, \
    {"abi2", QDSP6_ABI_2}, \
    {"linux", QDSP6_ABI_LINUX} \
  }

#define QDSP6_ABI_TABLE_DEFAULT_INDEX \
  (TARGET_V3_FEATURES ? QDSP6_ABI_2 : QDSP6_ABI_1)

enum qdsp6_falign {
  QDSP6_NO_FALIGN,
  QDSP6_FALIGN_LOOPS,
  QDSP6_FALIGN_LABELS,
  QDSP6_FALIGN_ALL,
  QDSP6_FALIGN_UNSPECIFIED
};

extern bool qdsp6_dual_memory_accesses;

#define TARGET_CONST32 (TARGET_LITERAL_POOL && g_switch_value >= 4)
#define TARGET_CONST64 (TARGET_LITERAL_POOL && g_switch_value >= 8)

#define TARGET_PACKET_OPTIMIZATIONS (TARGET_PULLUP || TARGET_NEW_VALUE_JUMP)

/* ranges for the various kinds of registers */
#define G_REGNO_P(REGNO) (IN_RANGE ((REGNO), 0, 31))
#define P_REGNO_P(REGNO) (IN_RANGE ((REGNO), 32, 35))
#define C_REGNO_P(REGNO) (IN_RANGE ((REGNO), 36, 43))

#define G_REG_P(RTX) (REG_P (RTX) && G_REGNO_P (REGNO (RTX)))
#define P_REG_P(RTX) (REG_P (RTX) && P_REGNO_P (REGNO (RTX)))
#define C_REG_P(RTX) (REG_P (RTX) && C_REGNO_P (REGNO (RTX)))

#define G_REG(REGNO) ((REGNO) + 0)
#define P_REG(REGNO) ((REGNO) + 32)

/* Fixed register assignments: */

/* The register that contains the result of a function call. */
#define RETURN_VALUE_REGNUM 0

/* The first register that can contain the arguments to a function. */
#define FIRST_ARG_REGNUM 0

/* The number of register assigned to holding function arguments. */
#define QDSP6_NUM_ARG_REGS 6

/* The maximum number of instructions allowed in a packet */
#define QDSP6_MAX_INSNS_PER_PACKET 6

/* If cross-compiling, don't require stdio.h etc to build libgcc.a. */
#if defined CROSS_COMPILE && ! defined inhibit_libc
#define inhibit_libc
#endif

enum qdsp6_builtins {
#define BUILTIN_INFO(TAG, TYPE, NARGS) QDSP6_BUILTIN_##TAG,
#define BUILTIN_INFO_NONCONST(TAG, TYPE, NARGS) QDSP6_BUILTIN_##TAG,
#include "builtins.def"
#include "manual_builtins.def"
#undef BUILTIN_INFO
#undef BUILTIN_INFO_NONCONST
  QDSP6_BUILTIN_NONEXISTANT_THING_TO_SHUT_UP_GCC_WARNING
};

/* Structure to be filled in by qdsp6_compute_frame_info() with sizes of various
   parts of the stack frame and which registers need to be saved in the prologue
   and restored in the epilogue for the current function. */
struct GTY(()) qdsp6_frame_info {
  unsigned HOST_WIDE_INT total_size; /* # bytes in the entire frame */
  unsigned HOST_WIDE_INT frame_size; /* # bytes in the frame excluding LR:FP */
  unsigned HOST_WIDE_INT var_size;   /* # bytes for locals and spills */
  unsigned HOST_WIDE_INT args_size;  /* # bytes for outgoing arguments */
  unsigned HOST_WIDE_INT reg_size;   /* # bytes for callee save registers */
  unsigned HOST_WIDE_INT lrfp_size;  /* # bytes for LR:FP */
  unsigned int saved_pairs[FIRST_PSEUDO_REGISTER / 2];
  unsigned int num_saved_pairs;
  unsigned int saved_singles[FIRST_PSEUDO_REGISTER];
  unsigned int num_saved_singles;
  /* whether to use the allocframe instruction */
  bool use_allocframe;
  /* argument to allocframe */
  unsigned HOST_WIDE_INT allocframe_size;
  /* # bytes to decrement SP after or instead of using allocframe */
  unsigned HOST_WIDE_INT sp_adjustment;
  /* insn to emit for allocframe that possibly saves registers in parallel */
  int allocframe_insn;
  /* insn to emit for allocating stack that possibly saves registers in
     parallel */
  int allocate_stack_insn;
  /* register used to address the callee-save register save of the frame */
  rtx base_reg;
  /* offset from base_reg to the callee-save register area of the frame */
  HOST_WIDE_INT offset;
  /* function to implement a common prologue sequence */
  int prologue_function;
  /* number of callee-save register pairs saved by that function */
  unsigned int num_function_saved_pairs;
  /* function to implement a common epilogue sequence */
  int epilogue_function;
  /* number of callee-save register pairs restored by that function */
  unsigned int num_function_restored_pairs;
  /* function to implement a common sibcall epilogue sequence */
  int sibcall_epilogue_function;
  /* number of callee-save register pairs restored by that function */
  unsigned int num_sibcall_function_restored_pairs;
  /* number of callee-save register pairs saved in some special manner */
  unsigned int num_specially_saved_pairs;
  /* number of unpaired callee-save registers saved in some special manner */
  unsigned int num_specially_saved_singles;
  bool computed;  /* true if frame info has already been computed */
};

struct GTY(()) qdsp6_final_info {
  /* the operands of the current instruction */
  rtx * GTY ((skip)) insn_ops;
  /* whether the current insn starts a packet */
  bool start_packet;
  /* whether the current insn ends a packet */
  bool end_packet;
  /* whether the current insn should be indented */
  bool indent_insn;
  /* whether the current insn should be printed */
  bool print_insn;
  /* whether the current insn is an endloop0 */
  bool print_endloop0;
  /* whether the current insn is an endloop1 */
  bool print_endloop1;
  /* whether to falign the following packet */
  bool print_falign;
  /* whether the current packet ends an inner hardware loop */
  bool endloop0;
  /* the label at the start of a hardware loop */
  rtx endloop_label;
  bool dot_new_predicate_p;
  bool dot_new_gpr_p;
  bool duplex;
};

struct GTY(()) machine_function {
  struct qdsp6_frame_info frame_info;
  struct qdsp6_final_info final_info;
  rtx compare_op0;
  rtx compare_op1;
  int calls_builtin_return_address;
  int has_hardware_loops;
};

struct GTY((chain_next ("%h.next"))) qdsp6_reg_access {
  rtx reg;
  unsigned int regno;
  int flags;
  struct qdsp6_reg_access *next;
};

struct GTY((chain_next ("%h.next"))) qdsp6_mem_access {
  rtx mem;
  int flags;
  struct qdsp6_mem_access *next;
};

struct GTY((chain_next ("%h.stack"))) qdsp6_insn_info {
  rtx insn;
  struct qdsp6_reg_access *reg_reads;
  struct qdsp6_reg_access *reg_writes;
  struct qdsp6_mem_access *loads;
  struct qdsp6_mem_access *stores;
  int flags;
  struct qdsp6_insn_info *stack;
  struct qdsp6_packet_info *transformed_at_packet;
};

struct GTY((chain_prev ("%h.prev"), chain_next ("%h.next"))) qdsp6_packet_info {
  struct qdsp6_insn_info *insns[QDSP6_MAX_INSNS_PER_PACKET];
  int num_insns;
  rtx location;
  struct qdsp6_packet_info *prev;
  struct qdsp6_packet_info *next;
};

#include "hard-reg-set.h"


struct qdsp6_bb_aux_info {
  HARD_REG_SET live_out;
  struct qdsp6_packet_info *head_packet;
  struct qdsp6_packet_info *end_packet;
  struct qdsp6_bb_aux_info *next;
};

#define QDSP6_BB_AUX(BB) ((struct qdsp6_bb_aux_info *) (BB->aux))
#define BB_LIVE_OUT(BB) (QDSP6_BB_AUX (BB)->live_out)
#define BB_HEAD_PACKET(BB) (QDSP6_BB_AUX (BB)->head_packet)
#define BB_END_PACKET(BB) (QDSP6_BB_AUX (BB)->end_packet)

enum qdsp6_dependence_type {
  QDSP6_DEP_REGISTER,
  QDSP6_DEP_MEMORY,
  QDSP6_DEP_CONTROL,
  QDSP6_DEP_VOLATILE
};

struct GTY((chain_next ("%h.next"))) qdsp6_dependence {
  enum qdsp6_dependence_type type;
  rtx set;
  rtx use;
  struct qdsp6_dependence *next;
};




#define QDSP6_MASK(WIDTH, LOW) (((1 << (WIDTH)) - 1) << (LOW))

#define QDSP6_PREDICATE_MASK QDSP6_MASK(2, 0)
#define QDSP6_IF_TRUE        QDSP6_MASK(1, 2)
#define QDSP6_IF_FALSE       QDSP6_MASK(1, 3)
#define QDSP6_GPR_CONDITION  QDSP6_MASK(1, 4)
#define QDSP6_SENSE_MASK     (QDSP6_IF_TRUE | QDSP6_IF_FALSE)
#define QDSP6_UNCONDITIONAL  QDSP6_SENSE_MASK
#define QDSP6_CONDITION_MASK \
  (QDSP6_GPR_CONDITION | QDSP6_SENSE_MASK | QDSP6_PREDICATE_MASK)

#define QDSP6_DIRECT_JUMP    QDSP6_MASK(1, 5)
#define QDSP6_INDIRECT_JUMP  QDSP6_MASK(1, 6)
#define QDSP6_ENDLOOP        QDSP6_MASK(1, 7)
#define QDSP6_DIRECT_CALL    QDSP6_MASK(1, 8)
#define QDSP6_INDIRECT_CALL  QDSP6_MASK(1, 9)
#define QDSP6_EMULATION_CALL QDSP6_MASK(1, 10)
#define QDSP6_JUMP \
  (QDSP6_DIRECT_JUMP | QDSP6_INDIRECT_JUMP | QDSP6_ENDLOOP)
#define QDSP6_CALL           (QDSP6_DIRECT_CALL | QDSP6_INDIRECT_CALL)
#define QDSP6_CONTROL        (QDSP6_CALL | QDSP6_JUMP)

#define QDSP6_MEM            QDSP6_MASK(1, 11)
#define QDSP6_VOLATILE       QDSP6_MASK(1, 12)
#define QDSP6_NEW_PREDICATE  QDSP6_MASK(1, 13)
#define QDSP6_NEW_GPR        QDSP6_MASK(1, 14)

#define QDSP6_MOVED          QDSP6_MASK(1, 15)

#define QDSP6_CONDITION(INSN)       ((INSN)->flags & QDSP6_CONDITION_MASK)
#define QDSP6_PREDICATE(INSN)       ((INSN)->flags & QDSP6_PREDICATE_MASK)
#define QDSP6_SENSE(INSN)           ((INSN)->flags & QDSP6_SENSE_MASK)
#define QDSP6_GPR_CONDITION_P(INSN) (((INSN)->flags & QDSP6_GPR_CONDITION) != 0)
#define QDSP6_CONFLICT_P(ACCESS0, ACCESS1) \
  (QDSP6_SENSE (ACCESS0) & QDSP6_SENSE (ACCESS1) \
   || QDSP6_PREDICATE (ACCESS0) != QDSP6_PREDICATE (ACCESS1))
#define QDSP6_CONDITIONAL_P(INSN) \
  (QDSP6_SENSE (INSN) != QDSP6_UNCONDITIONAL || QDSP6_GPR_CONDITION_P (INSN))

#define QDSP6_DIRECT_JUMP_P(INSN)    (((INSN)->flags & QDSP6_DIRECT_JUMP) != 0)
#define QDSP6_INDIRECT_JUMP_P(INSN)  (((INSN)->flags & QDSP6_INDIRECT_JUMP) != 0)
#define QDSP6_ENDLOOP_P(INSN)        (((INSN)->flags & QDSP6_ENDLOOP) != 0)
#define QDSP6_DIRECT_CALL_P(INSN)    (((INSN)->flags & QDSP6_DIRECT_CALL) != 0)
#define QDSP6_INDIRECT_CALL_P(INSN)  (((INSN)->flags & QDSP6_INDIRECT_CALL) != 0)
#define QDSP6_EMULATION_CALL_P(INSN) (((INSN)->flags & QDSP6_EMULATION_CALL) != 0)
#define QDSP6_JUMP_P(INSN)           (((INSN)->flags & QDSP6_JUMP) != 0)
#define QDSP6_CALL_P(INSN)           (((INSN)->flags & QDSP6_CALL) != 0)
#define QDSP6_CONTROL_P(INSN)        (((INSN)->flags & QDSP6_CONTROL) != 0)

#define QDSP6_MEM_P(INSN)           (((INSN)->flags & QDSP6_MEM) != 0)
#define QDSP6_VOLATILE_P(INSN)      (((INSN)->flags & QDSP6_VOLATILE) != 0)
#define QDSP6_NEW_PREDICATE_P(INSN) (((INSN)->flags & QDSP6_NEW_PREDICATE) != 0)
#define QDSP6_NEW_GPR_P(INSN)       (((INSN)->flags & QDSP6_NEW_GPR) != 0)

#define QDSP6_MOVED_P(INSN)  (((INSN)->flags & QDSP6_MOVED) != 0)

#endif /* !USED_FOR_TARGET */

#endif /* !GCC_QDSP6_H */
