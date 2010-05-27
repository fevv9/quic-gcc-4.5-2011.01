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
		   %{G*} \
		   %{YP,*} \
		   %{Qy:} %{!Qn:-Qy}"
#else /* !CROSS_COMPILE */
#define LINK_SPEC "-e _start \
                   %{h*} %{v:-V} \
		   %{static:-dn -Bstatic} \
		   %{shared:-G -dy -z text} \
		   %{symbolic:-Bsymbolic -G -dy -z text} \
		   %{G*} \
		   %{YP,*} \
		   %{!YP,*:%{p:-Y P,/usr/ccs/lib/libp:/usr/lib/libp:/usr/ccs/lib:/usr/lib} \
		    %{!p:-Y P,/usr/ccs/lib:/usr/lib}} \
		   %{Qy:} %{!Qn:-Qy}"
#endif /* !CROSS_COMPILE */

/* Copied from config/linux.h and modified to remove crti.o. */

#undef	STARTFILE_SPEC
#define STARTFILE_SPEC \
  "%{!shared: %{pg|p|profile:gcrt1.o%s;:crt1.o%s}} \
   %{static:crtbeginT.o%s;shared|pie:crtbeginS.o%s;:crtbegin.o%s}"

/* Copied from config/linux.h and modified to remove crtn.o. */

#undef	ENDFILE_SPEC
#define ENDFILE_SPEC \
  "%{shared|pie:crtendS.o%s;:crtend.o%s}"


/*---------------------------
Run-time Target Specification
---------------------------*/

#define TARGET_OS_CPP_BUILTINS() LINUX_TARGET_OS_CPP_BUILTINS()


/*----------------------------------------
The Overall Framework of an Assembler File
----------------------------------------*/

#undef ASM_APP_ON
#define ASM_APP_ON "//APP\n"

#undef ASM_APP_OFF
#define ASM_APP_OFF "//NO_APP\n"


/*------------
QDSP6 specific
------------*/

#undef QDSP6_ABI_TABLE_DEFAULT_INDEX
#define QDSP6_ABI_TABLE_DEFAULT_INDEX QDSP6_ABI_LINUX
