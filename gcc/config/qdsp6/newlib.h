/*-------------------------------------
Controlling the Compilation Driver, gcc
-------------------------------------*/

/* Link crt0 first. */
#undef STARTFILE_SPEC
#define STARTFILE_SPEC "crt0.o%s crti.o%s crtbegin.o%s"
