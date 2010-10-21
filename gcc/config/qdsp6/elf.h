
/*-------------------------------------
Controlling the Compilation Driver, gcc
-------------------------------------*/

#undef SWITCH_TAKES_ARG
#define SWITCH_TAKES_ARG(CHAR) \
  (DEFAULT_SWITCH_TAKES_ARG (CHAR) || (CHAR) == 'G')

/* Pass -v, -march=, and -G on to the assembler. */
#undef ASM_SPEC
#define ASM_SPEC "%{v} %{march=*} %{G*:-G%*;:%{mbuilding-multilib:%{mG0lib:-G0}}}"

/* Copied from config/svr4.h and modified to forward the -G option's argument
   and to not forward the -b option to the linker. */
#undef	LINK_SPEC
#ifdef CROSS_COMPILE
#define LINK_SPEC "%{h*} %{v:-V} \
		   %{static:-dn -Bstatic} \
		   %{shared:-G -dy -z text} \
		   %{symbolic:-Bsymbolic -G -dy -z text} \
		   %{G*:-G%*;:%{mbuilding-multilib:%{mG0lib:-G0}}} \
		   %{YP,*} \
		   %{Qy:} %{!Qn:-Qy}"
#else /* !CROSS_COMPILE */
#define LINK_SPEC "%{h*} %{v:-V} \
		   %{static:-dn -Bstatic} \
		   %{shared:-G -dy -z text} \
		   %{symbolic:-Bsymbolic -G -dy -z text} \
		   %{G*:-G%*;:%{mbuilding-multilib:%{mG0lib:-G0}}} \
		   %{YP,*} \
		   %{!YP,*:%{p:-Y P,/usr/ccs/lib/libp:/usr/lib/libp:/usr/ccs/lib:/usr/lib} \
		    %{!p:-Y P,/usr/ccs/lib:/usr/lib}} \
		   %{Qy:} %{!Qn:-Qy}"
#endif /* !CROSS_COMPILE */


/*------------
Storage Layout
------------*/

/* ??? Is this right? */
#undef MAX_OFILE_ALIGNMENT
#define MAX_OFILE_ALIGNMENT ((1 << 16) * BITS_PER_UNIT)
