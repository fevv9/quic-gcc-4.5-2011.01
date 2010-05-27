/*-------------------------------------
Controlling the Compilation Driver, gcc
-------------------------------------*/

/* Link crt0 first. */
#undef STARTFILE_SPEC
#define STARTFILE_SPEC "%{moslib=standalone:crt0_standalone.o%s} %{!moslib=*:crt0_standalone.o%s} crt0.o%s init.o%s"

#undef ENDFILE_SPEC
#define ENDFILE_SPEC "fini.o%s"

#undef LINK_GCC_C_SEQUENCE_SPEC
#define LINK_GCC_C_SEQUENCE_SPEC \
  "--start-group %{moslib=*:-l%*; :-lstandalone} %L %G --end-group"


/*----------------------
Miscellaneous Parameters
----------------------*/

#define NO_IMPLICIT_EXTERN_C 1


/*------------
QDSP6 specific
------------*/

#define QDSP6_DINKUMWARE 1
