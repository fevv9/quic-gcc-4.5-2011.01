/* { dg-options "-O2 -mrelax-pic-calls -mno-shared" } */
/* { dg-final { scan-assembler "\\.reloc\t1f,R_MIPS_JALR,g\n1:\tjalr\t" } } */

__attribute__ ((visibility ("hidden"))) void g ();

NOMIPS16 f ()
{
  g ();
  return 1;
}