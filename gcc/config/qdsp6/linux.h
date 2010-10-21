/*-------------------------------------
Controlling the Compilation Driver, gcc
-------------------------------------*/

/* Copied from config/svr4.h and modified to add the -e _start option, forward
   the -G option's argument, and not forward the -b option to the linker. */
#undef	LINK_SPEC
#ifdef CROSS_COMPILE
#define LINK_SPEC "-e _start \
                   %{h*} %{v:-V} \
		   %{static:-dn -Bstatic} \
		   %{shared:-G -dy -z text} \
		   %{symbolic:-Bsymbolic -G -dy -z text} \
		   %{G*:-G%*;:%{mbuilding-multilib:%{mG0lib:-G0}}} \
		   %{YP,*} \
		   %{Qy:} %{!Qn:-Qy}"
#else /* !CROSS_COMPILE */
#define LINK_SPEC "-e _start \
                   %{h*} %{v:-V} \
		   %{static:-dn -Bstatic} \
		   %{shared:-G -dy -z text} \
		   %{symbolic:-Bsymbolic -G -dy -z text} \
		   %{G*:-G%*;:%{mbuilding-multilib:%{mG0lib:-G0}}} \
		   %{YP,*} \
		   %{!YP,*:%{p:-Y P,/usr/ccs/lib/libp:/usr/lib/libp:/usr/ccs/lib:/usr/lib} \
		    %{!p:-Y P,/usr/ccs/lib:/usr/lib}} \
		   %{Qy:} %{!Qn:-Qy}"
#endif /* !CROSS_COMPILE */

#undef STARTFILE_SPEC
/* Define linux startfiles */
#define STARTFILE_SPEC \
  "%{msys-crt0=*: %*} %{!msys-crt0=*:%{!shared:crt1%O%s}} \
   %{msys-crt0=: %eYou need a C startup file for -msys-crt0=} \
   %{!shared:crti%\O%s} %{!shared:crtbegin%O%s}"

#undef ENDFILE_SPEC
#define ENDFILE_SPEC \
 "%{!shared:crtend%O%s crtn%O%s}"

#undef LIB_SPEC
#define LIB_SPEC "-lc"
