/*****************************************************************
# Copyright (c) $Date$ Qualcomm Innovation Center, Inc..
# All Rights Reserved.
# Modified by Qualcomm Innovation Center, Inc. on $Date$
*****************************************************************/
/* libgcc routines for the QDSP6.
   Copyright (C) 1998, 1999 Free Software Foundation, Inc.

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify it
under the terms of the GNU General Public License as published by the
Free Software Foundation; either version 2, or (at your option) any
later version.

In addition to the permissions in the GNU General Public License, the
Free Software Foundation gives you unlimited permission to link the
compiled version of this file into combinations with other programs,
and to distribute those combinations without any restriction coming
from the use of this file.  (The General Public License restrictions
do apply in other respects; for example, they cover modification of
the file, and distribution when not linked into a combine
executable.)

This file is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program; see the file COPYING.  If not, write to
the Free Software Foundation, 59 Temple Place - Suite 330,
Boston, MA 02111-1307, USA.  */

	.macro FUNC_START name
	.text
	.p2align 5
	.globl __\name
	.type  __\name, @function
__\name:
	.endm

	.macro FUNC_END name
	.size  __\name, . - __\name
	.endm

	.macro FALLTHROUGH_TAIL_CALL name0 name1
	.size  __\name0, . - __\name0
	.globl __\name1
	.type  __\name1, @function
__\name1:
	.endm

#ifdef L_udivmodsi4
FUNC_START udivmodsi4
	{
		r2 = cl0(r0)
		r3 = cl0(r1)
		r5:4 = combine(#1,#0)
		p0 = cmp.gtu(r1,r0)
	}
	{
		r6 = sub(r3,r2)
		r4 = r1
		r1:0 = combine(r0,r4)
		if (p0) jumpr r31
	}
	{
		r3:2 = vlslw(r5:4,r6)
		loop0(1f,r6)
		p0 = cmp.eq(r6,#0)
		if (p0.new) r4 = #0
	}
	.falign
1:
	{
		p0 = cmp.gtu(r2,r1)
		if (!p0.new) r1 = sub(r1,r2)
		if (!p0.new) r0 = add(r0,r3)
		r3:2 = vlsrw(r3:2,#1)
	}:endloop0
	{
		p0 = cmp.gtu(r2,r1)
		if (!p0.new) r1 = sub(r1,r4)
		if (!p0.new) r0 = add(r0,r3)
		jumpr r31
	}
FUNC_END udivmodsi4
#endif /* L_udivmodsi4 */

#ifdef L_udivsi3
FUNC_START udivsi3
	{
		r2 = cl0(r0)
		r3 = cl0(r1)
		r5:4 = combine(#1,#0)
		p0 = cmp.gtu(r1,r0)
	}
	{
		r6 = sub(r3,r2)
		r4 = r1
		r1:0 = combine(r0,r4)
		if (p0) jumpr r31
	}
	{
		r3:2 = vlslw(r5:4,r6)
		loop0(1f,r6)
	}
	.falign
1:
	{
		p0 = cmp.gtu(r2,r1)
		if (!p0.new) r1 = sub(r1,r2)
		if (!p0.new) r0 = add(r0,r3)
		r3:2 = vlsrw(r3:2,#1)
	}:endloop0
	{
		p0 = cmp.gtu(r2,r1)
		if (!p0.new) r0 = add(r0,r3)
		jumpr r31
	}
FUNC_END udivsi3
#endif /* L_udivsi3 */

#ifdef L_umodsi3
FUNC_START umodsi3
	{
		r2 = cl0(r0)
		r3 = cl0(r1)
		p0 = cmp.gtu(r1,r0)
	}
	{
		r2 = sub(r3,r2)
		if (p0) jumpr r31
	}
	{
		loop0(1f,r2)
		p1 = cmp.eq(r2,#0)
		r2 = lsl(r1,r2)
	}
	.falign
1:
	{
		p0 = cmp.gtu(r2,r0)
		if (!p0.new) r0 = sub(r0,r2)
		r2 = lsr(r2,#1)
		if (p1) r1 = #0
	}:endloop0
	{
		p0 = cmp.gtu(r2,r0)
		if (!p0.new) r0 = sub(r0,r1)
		jumpr r31
	}
FUNC_END umodsi3
#endif /* L_umodsi3 */

#ifdef L_divsi3
FUNC_START divsi3
	{
		p0 = cmp.ge(r0,#0)
		p1 = cmp.ge(r1,#0)
		r1 = abs(r0)
		r2 = abs(r1)
	}
	{
		r3 = cl0(r1)
		r4 = cl0(r2)
		r5 = sub(r1,r2)
		p2 = cmp.gtu(r2,r1)
	}
	{
		r0 = #0
		if (p2) jumpr r31
		p1 = xor(p0,p1)
		p0 = cmp.gtu(r2,r5)
	}
	{
		r0 = mux(p1,#-1,#1)
		if (p0) jumpr r31
		r4 = sub(r4,r3)
		r3 = #1
	}
	{
		r0 = #0
		r3:2 = vlslw(r3:2,r4)
		loop0(1f,r4)
	}
	.falign
1:
	{
		p0 = cmp.gtu(r2,r1)
		if (!p0.new) r1 = sub(r1,r2)
		if (!p0.new) r0 = add(r0,r3)
		r3:2 = vlsrw(r3:2,#1)
	}:endloop0
	{
		p0 = cmp.gtu(r2,r1)
		if (!p0.new) r0 = add(r0,r3)
		if (!p1) jumpr r31
	}
	{
		r0 = neg(r0)
		jumpr r31
	}
FUNC_END divsi3
#endif /* L_divsi3 */

#ifdef L_modsi3
FUNC_START modsi3
	{
		p2 = cmp.ge(r0,#0)
		r2 = abs(r0)
		r1 = abs(r1)
	}
	{
		r3 = cl0(r2)
		r4 = cl0(r1)
		p0 = cmp.gtu(r1,r2)
	}
	{
		r3 = sub(r4,r3)
		if (p0) jumpr r31
	}
	{
		p1 = cmp.eq(r3,#0)
		loop0(1f,r3)
		r0 = r2
		r2 = lsl(r1,r3)
	}
	.falign
1:
	{
		p0 = cmp.gtu(r2,r0)
		if (!p0.new) r0 = sub(r0,r2)
		r2 = lsr(r2,#1)
		if (p1) r1 = #0
	}:endloop0
	{
		p0 = cmp.gtu(r2,r0)
		if (!p0.new) r0 = sub(r0,r1)
		if (p2) jumpr r31
	}
	{
		r0 = neg(r0)
		jumpr r31
	}
FUNC_END modsi3
#endif /* L_modsi3 */

#ifdef L_udivmoddi4
FUNC_START udivmoddi4
	{
		r6 = cl0(r1:0)              // count leading 0's of dividend (numerator)
		r7 = cl0(r3:2)              // count leading 0's of divisor (denominator)
		r5:4 = r3:2                 // divisor moved into working registers
		r3:2 = r1:0                 // dividend is the initial remainder, r3:2 contains remainder
	}
	{
		r10 = sub(r7,r6)            // left shift count for bit & divisor
		r1:0 = #0                   // initialize quotient to 0
		r15:14 = #1                 // initialize bit to 1
	}
	{
		r11 = add(r10,#1)           // loop count is 1 more than shift count
		r13:12 = lsl(r5:4,r10)      // shift divisor msb into same bit position as dividend msb
		r15:14 = lsl(r15:14,r10)    // shift the bit left by same amount as divisor
	}
	{
		p0 = cmp.gtu(r5:4,r3:2)     // check if divisor > dividend
		loop0(1f,r11)               // register loop

	}
		if (p0) jumpr r31           // if divisor > dividend, we're done, so return

	.falign
1:
	{
		p0 = cmp.gtu(r13:12,r3:2)   // set predicate reg if shifted divisor > current remainder
	}
	{
		r7:6 = sub(r3:2, r13:12)    // subtract shifted divisor from current remainder
		r9:8 = add(r1:0, r15:14)    // save current quotient to temp (r9:8)
	}
	{
		r1:0 = vmux(p0, r1:0, r9:8) // choose either current quotient or new quotient (r9:8)
		r3:2 = vmux(p0, r3:2, r7:6) // choose either current remainder or new remainder (r7:6)
	}
	{
		r15:14 = lsr(r15:14, #1)    // shift bit right by 1 for next iteration
		r13:12 = lsr(r13:12, #1)    // shift "shifted divisor" right by 1 for next iteration
	}:endloop0
		jumpr r31                   // return
FUNC_END udivmoddi4
#endif /* L_udivmoddi4 */

#ifdef L_udivdi3
FUNC_START udivdi3
	{
		r6 = cl0(r1:0)              // count leading 0's of dividend (numerator)
		r7 = cl0(r3:2)              // count leading 0's of divisor (denominator)
		r5:4 = r3:2                 // divisor moved into working registers
		r3:2 = r1:0                 // dividend is the initial remainder, r3:2 contains remainder
	}
	{
		r10 = sub(r7,r6)            // left shift count for bit & divisor
		r1:0 = #0                   // initialize quotient to 0
		r15:14 = #1                 // initialize bit to 1
	}
	{
		r11 = add(r10,#1)           // loop count is 1 more than shift count
		r13:12 = lsl(r5:4,r10)      // shift divisor msb into same bit position as dividend msb
		r15:14 = lsl(r15:14,r10)    // shift the bit left by same amount as divisor
	}
	{
		p0 = cmp.gtu(r5:4,r3:2)     // check if divisor > dividend
		loop0(1f,r11)               // register loop

	}
		if (p0) jumpr r31           // if divisor > dividend, we're done, so return

	.falign
1:
	{
		p0 = cmp.gtu(r13:12,r3:2)   // set predicate reg if shifted divisor > current remainder
	}
	{
		r7:6 = sub(r3:2, r13:12)    // subtract shifted divisor from current remainder
		r9:8 = add(r1:0, r15:14)    // save current quotient to temp (r9:8)
	}
	{
		r1:0 = vmux(p0, r1:0, r9:8) // choose either current quotient or new quotient (r9:8)
		r3:2 = vmux(p0, r3:2, r7:6) // choose either current remainder or new remainder (r7:6)
	}
	{
		r15:14 = lsr(r15:14, #1)    // shift bit right by 1 for next iteration
		r13:12 = lsr(r13:12, #1)    // shift "shifted divisor" right by 1 for next iteration
	}:endloop0
		jumpr r31                   // return
FUNC_END udivdi3
#endif /* L_udivdi3 */

#ifdef L_umoddi3
FUNC_START umoddi3
	{
		r6 = cl0(r1:0)              // count leading 0's of dividend (numerator)
		r7 = cl0(r3:2)              // count leading 0's of divisor (denominator)
		r5:4 = r3:2                 // divisor moved into working registers
		r3:2 = r1:0                 // dividend is the initial remainder, r3:2 contains remainder
	}
	{
		r10 = sub(r7,r6)            // left shift count for bit & divisor
		r1:0 = #0                   // initialize quotient to 0
		r15:14 = #1                 // initialize bit to 1
	}
	{
		r11 = add(r10,#1)           // loop count is 1 more than shift count
		r13:12 = lsl(r5:4,r10)      // shift divisor msb into same bit position as dividend msb
		r15:14 = lsl(r15:14,r10)    // shift the bit left by same amount as divisor
	}
	{
		p0 = cmp.gtu(r5:4,r3:2)     // check if divisor > dividend
		loop0(1f,r11)               // register loop

	}
		if (p0) jump .qdsp_umoddi3_return           // if divisor > dividend, we're done, so return

	.falign
1:
	{
		p0 = cmp.gtu(r13:12,r3:2)   // set predicate reg if shifted divisor > current remainder
	}
	{
		r7:6 = sub(r3:2, r13:12)    // subtract shifted divisor from current remainder
		r9:8 = add(r1:0, r15:14)    // save current quotient to temp (r9:8)
	}
	{
		r1:0 = vmux(p0, r1:0, r9:8) // choose either current quotient or new quotient (r9:8)
		r3:2 = vmux(p0, r3:2, r7:6) // choose either current remainder or new remainder (r7:6)
	}
	{
		r15:14 = lsr(r15:14, #1)    // shift bit right by 1 for next iteration
		r13:12 = lsr(r13:12, #1)    // shift "shifted divisor" right by 1 for next iteration
	}:endloop0

.qdsp_umoddi3_return:
	{
		r1:0 = r3:2
		jumpr r31
	}
FUNC_END umoddi3
#endif /* L_umoddi3 */

#ifdef L_divdi3
FUNC_START divdi3
		r5:4 = #0
	{
		p2 = cmp.gt(r5:4,r1:0)
		p3 = cmp.gt(r5:4,r3:2)
	}
	{
		p2 = not(p2)
		p3 = not(p3)
	}
	{
		r1:0 = abs(r1:0)
		r3:2 = abs(r3:2)
	}
	{
		r6 = cl0(r1:0)              // count leading 0's of dividend (numerator)
		r7 = cl0(r3:2)              // count leading 0's of divisor (denominator)
		r5:4 = r3:2                 // divisor moved into working registers
		r3:2 = r1:0                 // dividend is the initial remainder, r3:2 contains remainder
	}
	{
		p3 = xor(p2,p3)
		r10 = sub(r7,r6)            // left shift count for bit & divisor
		r1:0 = #0                   // initialize quotient to 0
		r15:14 = #1                 // initialize bit to 1
	}
	{
		r11 = add(r10,#1)           // loop count is 1 more than shift count
		r13:12 = lsl(r5:4,r10)      // shift divisor msb into same bit position as dividend msb
		r15:14 = lsl(r15:14,r10)    // shift the bit left by same amount as divisor
	}
	{
		p0 = cmp.gtu(r5:4,r3:2)     // check if divisor > dividend
		loop0(1f,r11)               // register loop

	}
		if (p0) jump .qdsp_divdi3_return          // if divisor > dividend, we're done, so return

	.falign
1:
	{
		p0 = cmp.gtu(r13:12,r3:2)   // set predicate reg if shifted divisor > current remainder
	}
	{
		r7:6 = sub(r3:2, r13:12)    // subtract shifted divisor from current remainder
		r9:8 = add(r1:0, r15:14)    // save current quotient to temp (r9:8)
	}
	{
		r1:0 = vmux(p0, r1:0, r9:8) // choose either current quotient or new quotient (r9:8)
		r3:2 = vmux(p0, r3:2, r7:6) // choose either current remainder or new remainder (r7:6)
	}
	{
		r15:14 = lsr(r15:14, #1)    // shift bit right by 1 for next iteration
		r13:12 = lsr(r13:12, #1)    // shift "shifted divisor" right by 1 for next iteration
	}:endloop0

.qdsp_divdi3_return:
		r3:2 = neg(r1:0)
	{
		r1:0 = vmux(p3,r3:2,r1:0)
		jumpr r31
	}
FUNC_END divdi3
#endif /* L_divdi3 */

#ifdef L_moddi3
FUNC_START moddi3
	{
		r5:4 = #0
	}
		p3 = cmp.gt(r5:4,r1:0)
	{
		r1:0 = abs(r1:0)
		r3:2 = abs(r3:2)
	}
	{
		r6 = cl0(r1:0)              // count leading 0's of dividend (numerator)
		r7 = cl0(r3:2)              // count leading 0's of divisor (denominator)
		r5:4 = r3:2                 // divisor moved into working registers
		r3:2 = r1:0                 // dividend is the initial remainder, r3:2 contains remainder
	}
	{
		p3 = not(p3)
		r10 = sub(r7,r6)            // left shift count for bit & divisor
		r1:0 = #0                   // initialize quotient to 0
		r15:14 = #1                 // initialize bit to 1
	}
	{
		r11 = add(r10,#1)           // loop count is 1 more than shift count
		r13:12 = lsl(r5:4,r10)      // shift divisor msb into same bit position as dividend msb
		r15:14 = lsl(r15:14,r10)    // shift the bit left by same amount as divisor
	}
	{
		p0 = cmp.gtu(r5:4,r3:2)     // check if divisor > dividend
		loop0(1f,r11)               // register loop

	}
		if (p0) jump .qdsp_moddi3_return          // if divisor > dividend, we're done, so return

	.falign
1:
	{
		p0 = cmp.gtu(r13:12,r3:2)   // set predicate reg if shifted divisor > current remainder
	}
	{
		r7:6 = sub(r3:2, r13:12)    // subtract shifted divisor from current remainder
		r9:8 = add(r1:0, r15:14)    // save current quotient to temp (r9:8)
	}
	{
		r1:0 = vmux(p0, r1:0, r9:8) // choose either current quotient or new quotient (r9:8)
		r3:2 = vmux(p0, r3:2, r7:6) // choose either current remainder or new remainder (r7:6)
	}
	{
		r15:14 = lsr(r15:14, #1)    // shift bit right by 1 for next iteration
		r13:12 = lsr(r13:12, #1)    // shift "shifted divisor" right by 1 for next iteration
	}:endloop0

.qdsp_moddi3_return:
		r1:0 = neg(r3:2)
	{
		r1:0 = vmux(p3,r3:2,r1:0)
		jumpr r31
	}
FUNC_END moddi3
#endif /* L_moddi3 */




/* Functions that implement common sequences in function prologues and epilogues
   used to save code size

   Save r27:26 at fp+#-8, r25:24 at fp+#-16, r23:22 at fp+#-24, and r21:20 at
   fp+#-32. */


#ifdef L_common_prologue_epilogue
/* The compiler knows that the __save_* functions clobber LR.  No other
   registers should be used without informing the compiler. */

/* Since we can only issue one store per packet, we don't hurt performance by
   simply jumping to the right point in this sequence of stores. */

FUNC_START save_r27_through_r16
		memd(fp+#-48) = r17:16
FALLTHROUGH_TAIL_CALL save_r27_through_r16 save_r27_through_r18
		memd(fp+#-40) = r19:18
FALLTHROUGH_TAIL_CALL save_r27_through_r18 save_r27_through_r20
		memd(fp+#-32) = r21:20
FALLTHROUGH_TAIL_CALL save_r27_through_r20 save_r27_through_r22
		memd(fp+#-24) = r23:22
FALLTHROUGH_TAIL_CALL save_r27_through_r22 save_r27_through_r24
		memd(fp+#-16) = r25:24
	{
		memd(fp+#-8) = r27:26
		jumpr lr
	}
FUNC_END save_r27_through_r24


/* For each of the *_before_sibcall functions, jumpr lr is executed in parallel
   with deallocframe.  That way, the return gets the old value of lr, which is
   where these functions need to return, and at the same time, lr gets the value
   it needs going into the sibcall. */

FUNC_START restore_r27_through_r20_and_deallocframe_before_sibcall
	{
		r21:20 = memd(fp+#-32)
		jump __restore_r27_through_r22_and_deallocframe_before_sibcall
	}
FUNC_END restore_r27_through_r20_and_deallocframe_before_sibcall


FUNC_START restore_r27_through_r24_and_deallocframe_before_sibcall
	{
		r25:24 = memd(fp+#-16)
		jump __restore_r27_through_r26_and_deallocframe_before_sibcall
	}
FUNC_END restore_r27_through_r24_and_deallocframe_before_sibcall


FUNC_START restore_r27_through_r16_and_deallocframe_before_sibcall
		r17:16 = memd(fp+#-48)
FALLTHROUGH_TAIL_CALL restore_r27_through_r16_and_deallocframe_before_sibcall restore_r27_through_r18_and_deallocframe_before_sibcall
	{
		r19:18 = memd(fp+#-40)
		r21:20 = memd(fp+#-32)
	}
FALLTHROUGH_TAIL_CALL restore_r27_through_r18_and_deallocframe_before_sibcall restore_r27_through_r22_and_deallocframe_before_sibcall
	{
		r23:22 = memd(fp+#-24)
		r25:24 = memd(fp+#-16)
	}
FALLTHROUGH_TAIL_CALL restore_r27_through_r22_and_deallocframe_before_sibcall restore_r27_through_r26_and_deallocframe_before_sibcall
	{
		r27:26 = memd(fp+#-8)
		deallocframe
		jumpr lr
	}
FUNC_END restore_r27_through_r26_and_deallocframe_before_sibcall


/* Here we use the extra load bandwidth to restore LR early, allowing the return
   to occur in parallel with the deallocframe. */

FUNC_START restore_r27_through_r16_and_deallocframe
	{
		r17:16 = memd(fp+#-48)
		r19:18 = memd(fp+#-40)
	}
FALLTHROUGH_TAIL_CALL restore_r27_through_r16_and_deallocframe restore_r27_through_r20_and_deallocframe
	{
		r21:20 = memd(fp+#-32)
		r23:22 = memd(fp+#-24)
	}
FALLTHROUGH_TAIL_CALL restore_r27_through_r20_and_deallocframe restore_r27_through_r24_and_deallocframe
	{
		lr = memw(fp+#4)
		r25:24 = memd(fp+#-16)
	}
	{
		r27:26 = memd(fp+#-8)
		deallocframe
		jumpr lr
	}
FUNC_END restore_r27_through_r24_and_deallocframe


/* Here the load bandwidth is maximized for all three functions. */

FUNC_START restore_r27_through_r18_and_deallocframe
	{
		r19:18 = memd(fp+#-40)
		r21:20 = memd(fp+#-32)
	}
FALLTHROUGH_TAIL_CALL restore_r27_through_r18_and_deallocframe restore_r27_through_r22_and_deallocframe
	{
		r23:22 = memd(fp+#-24)
		r25:24 = memd(fp+#-16)
	}
FALLTHROUGH_TAIL_CALL restore_r27_through_r22_and_deallocframe restore_r27_through_r26_and_deallocframe
	{
		r27:26 = memd(fp+#-8)
		deallocframe
	}
		jumpr lr
FUNC_END restore_r27_through_r26_and_deallocframe


FUNC_START deallocframe
		deallocframe
		jumpr lr
FUNC_END deallocframe
#endif /* L_common_prologue_epilogue */
