/* syntax.h  syntax header file for vasm */
/* (c) in 2024 by 'Naoto' */

/* macros to recognize identifiers */
int isidstart(char);
int isidchar(char);
#define ISIDSTART(x) isidstart(x)
#define ISIDCHAR(x) isidchar(x)
#define ISBADID(p,l) ((l)==1&&(*(p)=='.'||*(p)=='@'||*(p)=='_'))
#define ISEOL(p) (*(p)=='\0' || *(p)==commentchar)
#ifdef VASM_CPU_M68K
char *chkidend(char *,char *);
#define CHKIDEND(s,e) chkidend((s),(e))
#endif

/* result of a boolean operation */
#define BOOLEAN(x) -(x)

/* we have a special skip() function for expressions, called exp_skip() */
char *exp_skip(char *);
#define EXPSKIP() s=exp_skip(s)

/* support for broken negative hex-constants: $-hex */
#define BROKEN_HEXCONST

/* operator separation characters */
#ifndef OPERSEP_COMMA
#define OPERSEP_COMMA 1
#endif
#ifndef OPERSEP_BLANK
#define OPERSEP_BLANK 0
#endif

/* ignore operand field, when the instruction has no operands */
#define IGNORE_FIRST_EXTRA_OP 1

/* symbol which contains the number of macro arguments */
#define NARGSYM "=NARG"

/* symbol which contains the number of the macro argument shift amount */
#define CARGSYM "=SHIFTN"

/* symbol which contains the current rept-endr iteration count */
#define REPTNSYM "=REPTN"

/* overwrite macro defaults */
#define MAXMACPARAMS 64
char *my_skip_macro_arg(char *);
#define SKIP_MACRO_ARGNAME(p) my_skip_macro_arg(p)
void my_exec_macro(source *);
#define EXEC_MACRO(s) my_exec_macro(s)

char get_comment_char();