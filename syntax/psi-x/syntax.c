/* syntax.c  syntax module for vasm */
/* by 'Naoto' 2025 */

#include <math.h>
#include <time.h>
#include "vasm.h"
#include "osdep.h"

/* The syntax module parses the input (read_next_line), handles
   assembly-directives (section, data-storage etc.) and parses
   mnemonics. Assembly instructions are split up in mnemonic name,
   qualifiers and operands. new_inst returns a matching instruction,
   if one exists.
   Routines for creating sections and adding atoms to sections will
   be provided by the main module.
*/

const char *syntax_copyright="vasm 'psi-x' syntax module v1.3.1-pre by 'Naoto'";

/* This syntax module was made to combine elements of other default syntax 
   modules into one that I find provides me with the best developer experience 
   possible. I've grown used to PSY-Q's family of assemblers as well as the 
   AS Macro Assembler, so my goal was to imitate their syntax and directive sets
   as closely as possible with the understanding that I cannot achieve full
   compatibility with either of them. As such, I make no promises that this 
   syntax module will be compatible out-of-the box with a project built around 
   the PSY-Q or AS assemblers. Instead, my hope is that it will be much easier
   to migrate away from those assemblers if desired, without the burden of having
   to weigh the pros and cons of all the default syntax modules.
   - Naoto
*/

/* TODO: add back 'macro_arg_opts()' for the purposes of setting default argument values on macros. */

hashtable *dirhash;
char commentchar = ';';
int blockcomment = 0;
int dotdirs;

/* default sections */
static char code_name[] = "CODE",code_type[] = "acrx";
static char data_name[] = "DATA",data_type[] = "adrw";
static char bss_name[] = "BSS",bss_type[] = "aurw";
static char rs_name[] = "=RS";

static struct namelen macro_dirlist[] = {
  { 5,"macro" }, { 6,"macros" }, { 0,0 }
};
static struct namelen endm_dirlist[] = {
  { 4,"endm" }, { 0,0 }
};

static struct namelen rept_dirlist[] = {
  { 4,"rept" }, { 3,"irp" }, { 4,"irpc" }, { 0,0 }
};
static struct namelen endr_dirlist[] = {
  { 4,"endr" }, { 0,0 }
};
static struct namelen comend_dirlist[] = {
  { 6,"comend" }, { 0,0 }
};

static struct namelen while_dirlist[] = {
  { 5,"while" }, { 0,0 }
};
static struct namelen endw_dirlist[] = {
  { 4,"endw" }, { 0,0 }
};
static struct namelen do_dirlist[] = {
  { 2,"do" }, { 0,0 }
};
static struct namelen until_dirlist[] = {
  { 5,"until" }, { 0,0 }
};

static int parse_end = 0;

/* options */
static int dot_idchar;

static struct options {
  int ae;   /* AE - Automatic Even */
  int an;   /* AN - Alternate Numeric */
  int  c;    /* C - Case Sensitivity */
  char l;   /* L - Local Label Signifier */
  int w;    /* W - Print warning messages */
  int ws;   /* WS - Allow white spaces */
} options = {
  1,      /* AE - Automatic Even */
  0,      /* AN - Alternate Numeric */
  0,      /* C - Case Sensitivity */
  '@',    /* L - Local Label Signifier */
  1,      /* W - Print Warning Messages */
  0,      /* WS - Allow White Spaces */
};

#define OPT_STACK_SIZE 100
static struct options options_stack[OPT_STACK_SIZE];
static int options_stack_index = 0;

/* function parameters */
#define MAX_FUNC_ARGS 32

static struct funcargs {
  char* arg[MAX_FUNC_ARGS];
} funcargs;

static char *labname;  /* current label field for assignment directives */
static unsigned anon_labno;
static char current_pc_str[2];

static int radix_base = 10;
static int public_status = 0;
static int data_size = 8;

/* special constants */
static char year_name[] = "_year";
static char month_name[] = "_month";
static char day_name[] = "_day";
static char weekday_name[] = "_weekday";
static char hours_name[] = "_hours";
static char minutes_name[] = "_minutes";
static char seconds_name[] = "_seconds";

/* isolated local labels block */
#define INLSTACKSIZE 100
#define INLLABFMT "=%06d"
static int inline_stack[INLSTACKSIZE];
static int inline_stack_index = 0;
static const char *saved_last_global_label;
static char inl_lab_name[8];

/* pushp/popp string stack */
#define STRSTACKSIZE 100
static char *string_stack[STRSTACKSIZE];
static int string_stack_index = 0;

int isidstart(char c)
{
  if (isalpha((unsigned char)c) || c==options.l || c=='_' || c=='@')
    return 1;
  if (dot_idchar && c=='.')
    return 1;
  return 0;
}

int isidchar(char c)
{
  if (isalnum((unsigned char)c) || c=='_' || c=='?')
    return 1;
  if (dot_idchar && c=='.')
    return 1;
  return 0;
}

#if defined(VASM_CPU_M68K)
char *chkidend(char *start,char *end)
{
  if ((end-start)>2 && *(end-2)=='.') {
    char c = tolower((unsigned char)*(end-1));

    if (c=='b' || c=='w' || c=='l')
      return end - 2;  /* .b/.w/.l extension is not part of identifier */
  }
  return end;
}
#endif

char *skip(char *s)
{
  while (isspace((unsigned char )*s))
    s++;
  return s;
}

/* check for end of line, issue error, if not */
void eol(char *s)
{
  if (options.ws) {
    s = skip(s);
    if (!ISEOL(s))
      syntax_error(6);
  }
  else {
    if (!ISEOL(s) && !isspace((unsigned char)*s))
      syntax_error(6);
  }
}

char *exp_skip(char *s)
{
  if (options.ws) {
    char *start = s;

    s = skip(start);
    if (*s == commentchar)
      *s = '\0';  /* rest of operand is ignored */
    else if (!strnicmp(s,"#||",3)) {
      blockcomment = 1;
      *s = '\0';  /* rest of operand is ignored */
    }

  }
  else if (isspace((unsigned char)*s) || *s==commentchar)
    *s = '\0';  /* rest of operand is ignored */
  else if (!strnicmp(s,"#||",3)) {
    blockcomment = 1;
    *s = '\0';  /* rest of operand is ignored */
  }
  return s;
}

char *skip_operand(char *s)
{
#if defined(VASM_CPU_Z80)
  unsigned char lastuc = 0;
#endif
  int par_cnt = 0;
  char c = 0;

  for (;;) {
#if defined(VASM_CPU_Z80)
    s = exp_skip(s);  /* @@@ why do we need that? */
    if (c)
      lastuc = toupper((unsigned char)*(s-1));
#endif
    c = *s;

    if (START_PARENTH(c)) {
      par_cnt++;
    }
    else if (END_PARENTH(c)) {
      if (par_cnt > 0)
        par_cnt--;
      else
        syntax_error(3);  /* too many closing parentheses */
    }
    #if defined(VASM_CPU_Z80)
    /* For the Z80 ignore ' behind a letter, as it may be a register */
    else if ((c=='\'' && (lastuc<'A' || lastuc>'Z')) || c=='\"')
    #else
    else if (c=='\'' || c=='\"')
    #endif
      s = skip_string(s,c,NULL) - 1;
    else if (!c || (par_cnt==0 && (c==',' || c==commentchar)))
      break;
    else if (!strnicmp(s,"#||",3)) {
      blockcomment = 1;
      *s = '\0';  /* rest of operand is ignored */
      break;
    }

    s++;
  }

  if (par_cnt != 0)
    syntax_error(4);  /* missing closing parentheses */
  return s;
}

char *my_skip_macro_arg(char *s)
{
  if (*s == '\\')
    s++;  /* leading \ in argument list is optional */
  return skip_identifier(s);
}

static int intel_suffix(char *s)
/* check for constants with h, d, o, q or b suffix */
{
  int base,lastbase;
  char c;
  
  base = 2;
  while (isxdigit((unsigned char)*s)) {
    lastbase = base;
    switch (base) {
      case 2:
        if (*s <= '1') break;
        base = 8;
      case 8:
        if (*s <= '7') break;
        base = 10;
      case 10:
        if (*s <= '9') break;
        base = 16;
    }
    s++;
  }

  c = tolower((unsigned char)*s);
  if (c == 'h')
    return 16;
  if ((c=='o' || c=='q') && base<=8)
    return 8;

  c = tolower((unsigned char)*(s-1));
  if (c=='d' && lastbase<=10)
    return 10;
  if (c=='b' && lastbase<=2)
    return 2;

  return 0;
}

char *const_prefix(char *s,int *base)
{
  if (isdigit((unsigned char)*s)) {
    if (options.an && (radix_base <= 10) && (*base = intel_suffix(s)))
      return s;
    if (*s == '0') {
      if (s[1]=='x' || s[1]=='X'){
        *base = 16;
        return s+2;
      }
      if (s[1]=='b' || s[1]=='B'){
        *base = 2;
        return s+2;
      }    
      if (s[1]=='q' || s[1]=='Q'){
        *base = 8;
        return s+2;
      }    
    } 
    else if (s[1]=='_' && *s>='2' && *s<='9') {
      *base = *s & 0xf;
      return s+2;
    }
    *base = radix_base;
    return s;
  }

  if (*s=='$' && isxdigit((unsigned char)s[1])) {
    *base = 16;
    return s+1;
  }
#if defined(VASM_CPU_Z80)
  if ((*s=='&' || *s=='#') && isxdigit((unsigned char)s[1])) {
    *base = 16;
    return s+1;
  }
#endif
  if (*s=='@') {
#if defined(VASM_CPU_Z80)
    *base = 2;
#else
    *base = 8;
#endif
    return s+1;
  }
  if (*s == '%') {
    *base = 2;
    return s+1;
  }
  *base = 0;
  return s;
}

char *const_suffix(char *start,char *end)
{
  if (intel_suffix(start))
    return end+1;

  return end;
}

static char *skip_local(char *p)
{
  char *s;

  if (ISIDSTART(*p) || isdigit((unsigned char)*p)) {  /* may start with digit */
    s = p++;
    while (ISIDCHAR(*p))
      p++;
    p = CHKIDEND(s,p);
  }
  else
    p = NULL;

  return p;
}

strbuf *get_local_label(int n,char **start)
/* Local labels start with a '.' or end with '$': "1234$", ".1" */
{
  char *s,*p;
  strbuf *name;

  name = NULL;
  s = *start;
  p = skip_local(s);

  if (p!=NULL && (*p==':' || *p=='.') && ISIDSTART(*s) && *s!=options.l && *(p-1)!='$') {
    /* skip local part of global.local label */
    s = p + 1;

    if (p = skip_local(s)) {
      char c = tolower((unsigned char)*s);
      
      if ((p-s == 1) && (c == 'b' || c == 'w' || c == 'l'))
        return NULL;
      
      name = make_local_label(n,*start,(s-1)-*start,s,*(p-1)=='$'?(p-1)-s:p-s);
      *start = skip(p);
    }
    else
      return NULL;
  }
  else if (p!=NULL && p>(s+1) && *s==options.l) {  /* .label */
    s++;
    name = make_local_label(n,NULL,0,s,p-s);
    *start = skip(p);
  }
  else if (p!=NULL && p>s && *p=='$') { /* label$ */
    p++;
    name = make_local_label(n,NULL,0,s,(p-1)-s);
    *start = skip(p);
  }
  else if (*s++ == ':') {
    /* anonymous label reference */
    if (*s=='+' || *s=='-') {
      unsigned refno = (*s++=='+')?anon_labno+1:anon_labno;
      char refnostr[16];

      while (*s=='+' || *s=='-') {
        if (*s++ == '+')
          refno++;  /* next anonynmous label */
        else
          refno--;  /* previous anonymous label */
      }
      name = make_local_label(n,":",1,refnostr,sprintf(refnostr,"%u",refno));
      *start = skip(s);
    }
  }

  return name;
}

/* attempts to find an return the name of a declared local macro variable */
char *find_macvar(source *src,char *name,size_t len)
{
  struct macarg *macvar;

  if ((src->macro != NULL) || (src->varnames != NULL)) {
    for (macvar = src->varnames; macvar != NULL ; macvar = macvar->argnext) {
      /* @@@ case-sensitive comparison? */
      if (macvar->arglen == len && strncmp(macvar->argname,name,len) == 0) {
        return macvar->argname;
      }
    }
  }
  return NULL;
}

/*
 *  Reserve Symbol Directives
 */
static void handle_rsreset(char *s)
{
  new_abs(rs_name,number_expr(0));
}

static void handle_rsset(char *s)
{
  new_abs(rs_name,parse_expr_tmplab(&s));
}

/* make the given struct- or frame-offset symbol dividable my the next
   multiple of "align" (must be a power of 2!) */
static void setoffset_align(char *symname,int dir,utaddr align)
{
  symbol *sym;
  expr *new;

  sym = internal_abs(symname);
  --align;  /* @@@ check it */
  new = make_expr(BAND,
                  make_expr(dir>0?ADD:SUB,sym->expr,number_expr(align)),
                  number_expr(~align));
  simplify_expr(new);
  sym->expr = new;
}

static void handle_rseven(char *s)
{
  setoffset_align(rs_name,1,2);
}

/* assign value of current struct- or frame-offset symbol to an abs-symbol,
   or just increment/decrement when equname is NULL */
static symbol *new_setoffset_size(char *equname,char *symname,
                                  char **s,int dir,taddr size)
{
  symbol *sym,*equsym;
  expr *new,*old;
  taddr result;

  /* get current offset symbol expression, then increment or decrement it */
  sym = internal_abs(symname);

  if (!ISEOL(*s)) {
    /* Make a new expression out of the parsed expression multiplied by size
       and add to or subtract it from the current symbol's expression.
       Perform even alignment when requested. */
    new = make_expr(MUL,parse_expr_tmplab(s),number_expr(size));
    simplify_expr(new);

    if ((options.ae) && size>1) {
      /* align the current offset symbol first */
      utaddr dalign = DATA_ALIGN((int)size*8) - 1;

      old = make_expr(BAND,
                      make_expr(dir>0?ADD:SUB,sym->expr,number_expr(dalign)),
                      number_expr(~dalign));
      simplify_expr(old);
    }
    else
      old = sym->expr;

    new = make_expr(dir>0?ADD:SUB,old,new);
  }
  else {
    new = old = sym->expr;
  }

  /* assign expression to equ-symbol and change exp. of the offset-symbol */
  if (equname)
    equsym = new_equate(equname,dir>0 ? copy_tree(old) : copy_tree(new));
  else
    equsym = NULL;

  eval_expr(new,&result,NULL,0);
  sym->expr = number_expr(result);
  return equsym;
}

/* assign value of current struct- or frame-offset symbol to an abs-symbol,
   determine operation size from directive extension first */
static symbol *new_setoffset(char *equname,char **s,char *symname,int dir)
{
  taddr size = 1;
  char *start = *s;
  char ext;

#if defined(VASM_CPU_M68K)
  /* get extension character and proceed to operand */
  if (*(start+2) == '.') {
    ext = tolower((unsigned char)*(start+3));
    *s = skip(start+4);
    switch (ext) {
      case 'b':
        break;
      case 'w':
        size = 2;
        break;
      case 'l':
        size = 4;
        break;
      default:
        syntax_error(1);  /* invalid extension */
        break;
    }
  }
  else {
    size = 2;  /* defaults to 'w' extension when missing */
    *s = skip(start+2);
  }
#else
  if (isalnum((unsigned char)*(start+2))) {
    ext = tolower((unsigned char)*(start+2));
    *s = skip(start+3);
    switch (ext) {
      case 'b':
        break;
      case 'w':
        size = 2;
        break;
      case 'l':
        size = 4;
        break;
      default:
        syntax_error(1);  /* invalid extension */
        break;
    }
  }
  else {
    size = 1;  /* defaults to 'b' extension when missing */
    *s = skip(start+2);
  }
#endif

  return new_setoffset_size(equname,symname,s,dir,size);
}

static void handle_rs8(char *s)
{
  new_setoffset_size(NULL,rs_name,&s,1,1);
}

static void handle_rs16(char *s)
{
  new_setoffset_size(NULL,rs_name,&s,1,2);
}

static void handle_rs32(char *s)
{
  new_setoffset_size(NULL,rs_name,&s,1,4);
}

/*
 *  Declare Constant Directives
 */
static void handle_datadef(char *s,int size)
{
  /* size is negative for floating point data! */
  for (;;) {
    char *opstart = s;
    operand *op;
    dblock *db = NULL;

    if (OPSZ_BITS(size)==8 && (*s=='\"' || *s=='\'')) {
      if (db = parse_string(&opstart,*s,8)) {
        add_atom(0,new_data_atom(db,1));
        s = opstart;
      }
    }
    if (!db) {
      op = new_operand();
      s = skip_operand(s);
      if (parse_operand(opstart,s-opstart,op,DATA_OPERAND(size))) {
        atom *a;

        a = new_datadef_atom(OPSZ_BITS(size),op);
        if (!options.ae)
          a->align = 1;
        add_atom(0,a);
      }
      else
        syntax_error(8);  /* invalid data operand */
    }

    s = skip(s);
    if (*s == ',')
      s = skip(s+1);
    else {
      eol(s);
      break;
    }
  }
}

static void handle_d8(char *s)
{
  handle_datadef(s,8);
}

static void handle_d16(char *s)
{
  handle_datadef(s,16);
}

static void handle_d32(char *s)
{
  handle_datadef(s,32);
}

/*
 *  Define Storage Directives
 */
static atom *do_space(int size,expr *cnt,expr *fill)
{
  atom *a;

  a = new_space_atom(cnt,size>>3,fill);
  a->align = options.ae ? DATA_ALIGN(size) : 1;
  add_atom(0,a);
  return a;
}

static void handle_space(char *s,int size)
{
  do_space(size,parse_expr_tmplab(&s),0);
  eol(s);
}

static void handle_spc8(char *s)
{
  handle_space(s,8);
}

static void handle_spc16(char *s)
{
  handle_space(s,16);
}

static void handle_spc32(char *s)
{
  handle_space(s,32);
}

/*
 *  Declare Constant Block Directives
 */
static void handle_block(char *s,int size)
{
  expr *cnt,*fill=0;

  cnt = parse_expr_tmplab(&s);
  s = skip(s);
  if (*s == ',') {
    s = skip(s+1);
    fill = parse_expr_tmplab(&s);
  }
  do_space(size,cnt,fill);
}

static void handle_blk8(char *s)
{
  handle_block(s,8);
}

static void handle_blk16(char *s)
{
  handle_block(s,16);
}

static void handle_blk32(char *s)
{
  handle_block(s,32);
}

/*
 *  Additional Data Directives
 */
static void handle_datasize(char *s)
{
  int size, base = radix_base;

  radix_base = 10;
  size = parse_constexpr(&s);

  if ((size < 1) || (size > 16))
    syntax_error(25,size);  /* invalid data size value */
  else
    data_size = (size<<3);

  radix_base = base;
  eol(s);
}

static void handle_data(char *s)
{
  handle_datadef(s,data_size);
}

static void handle_hex(char *s)
{
  dblock *db = NULL;

  s = skip(s);

  if (db = parse_hexstream(&s))
    add_atom(0,new_data_atom(db,1));

  s = skip(s);
  eol(s);
}

#if FLOAT_PARSER
static void handle_single(char *s){ handle_datadef(s,OPSZ_FLOAT|32); }
static void handle_double(char *s){ handle_datadef(s,OPSZ_FLOAT|64); }
#endif

/*
 *  Program Control Directives
 */
static void handle_org(char *s)
{
  if (current_section!=NULL &&
      (!(current_section->flags & ABSOLUTE) ||
        (current_section->flags & IN_RORG)))
    start_rorg(parse_constexpr(&s));
  else
    set_section(new_org(parse_constexpr(&s)));
}

static void handle_obj(char *s)
{
  start_rorg(parse_constexpr(&s));
}
  
static void handle_objend(char *s)
{
  if (end_rorg())
    eol(s);
}

/*
 *  Padding and Alignment Directives
 */
static void do_alignment(taddr align,expr *offset,size_t pad,expr *fill)
{
  atom *a = new_space_atom(offset,pad,fill);

  a->align = align;
  add_atom(0,a);
}

static void handle_cnop(char *s)
{
  expr *offset;
  taddr align = 1;

  offset = parse_expr_tmplab(&s);
  s = skip(s);
  if (*s == ',') {
    s = skip(s + 1);
    align = parse_constexpr(&s);
  }
  else
    syntax_error(13);  /* , expected */
  do_alignment(align,offset,1,NULL);
}

static void handle_even(char *s)
{
  do_alignment(2,number_expr(0),1,NULL);
}

static void handle_align(char *s)
{
  int align = parse_constexpr(&s);
  expr *fill = 0;

  s = skip(s);
  if (*s == ',') {
    s = skip(s + 1);
    fill = parse_expr_tmplab(&s);
  }

  do_alignment(align,number_expr(0),1,fill);
}

/*
 *  Include File Directives
 */
static void handle_incdir(char *s)
{
  strbuf *name;

  if (name = parse_name(0,&s))
    new_include_path(name->str);
  eol(s);
}

static void handle_include(char *s)
{
  strbuf *name;

  if (name = parse_name(0,&s)) {
    eol(s);
    include_source(name->str);
  }
}

static void handle_incbin(char *s)
{
  strbuf *name;
  taddr offs = 0;
  taddr length = 0;

  if (name = parse_name(0,&s)) {
    s = skip(s);
    if (*s == ',') {
      /* We have an offset */
      s = skip(s + 1);
      offs = parse_constexpr(&s);
      s = skip(s);
      if (*s == ',') {
        /* We have a length */
        s = skip(s + 1);
        length = parse_constexpr(&s);
      }
    }
    eol(s);
    include_binary_file(name->str,offs,length);
  }
}

/*
 *  Conditional Directives
 */
static void ifdef(char *s,int b)
{
  char *name = s;
  symbol *sym;
  int result = 0;

  if (s = skip_identifier(s)) {
    result = find_macro(name,s-name) != NULL;
  }
  else {
    syntax_error(10);  /*identifier expected */
  }

  if (sym = find_symbol(name)) {
    result = sym->type != IMPORT;
  }

  cond_if(result == b);
}

static void handle_ifd(char *s)
{
  ifdef(s,1);
}

static void handle_ifnd(char *s)
{
  ifdef(s,0);
}

static void ifc(char *s,int b)
{
  strbuf *str1,*str2;
  int result;

  str1 = parse_name(0,&s);
  if (str1!=NULL && *s==',') {
    s = skip(s+1);
    if (str2 = parse_name(1,&s)) {
      result = strcmp(str1->str,str2->str) == 0;
      cond_if(result == b);
      return;
    }
  }
  syntax_error(5);  /* missing operand */
}

static void handle_ifc(char *s)
{
  ifc(s,1);
}

static void handle_ifnc(char *s)
{
  ifc(s,0);
}

static void handle_ifb(char *s)
{
  s = skip(s);
  cond_if(ISEOL(s));
}

static void handle_ifnb(char *s)
{
  s = skip(s);
  cond_if(!ISEOL(s));
}

static int eval_ifexp(char **s,int c)
{
  expr *condexp = parse_expr_tmplab(s);
  taddr val;
  int b = 0;

  if (eval_expr(condexp,&val,NULL,0)) {
    switch (c) {
      case 0: b = val == 0; break;
      case 1: b = val != 0; break;
      case 2: b = val > 0; break;
      case 3: b = val >= 0; break;
      case 4: b = val < 0; break;
      case 5: b = val <= 0; break;
      default: ierror(0); break;
    }
  }
  else
    syntax_error(47);  /* expression must evaluate */
  free_expr(condexp);
  return b;
}

static void ifexp(char *s,int c)
{
  cond_if(eval_ifexp(&s,c));
}

static void handle_ifeq(char *s)
{
  ifexp(s,0);
}

static void handle_ifne(char *s)
{
  ifexp(s,1);
}

static void handle_ifgt(char *s)
{
  ifexp(s,2);
}

static void handle_ifge(char *s)
{
  ifexp(s,3);
}

static void handle_iflt(char *s)
{
  ifexp(s,4);
}

static void handle_ifle(char *s)
{
  ifexp(s,5);
}

static void handle_else(char *s)
{
  cond_skipelse();
}

static void handle_elseif(char *s)
{
  cond_skipelse();
}

static void handle_endif(char *s)
{
  cond_endif();
}

/* Move line_ptr to the end of the string if the parsing should stop,
   otherwise move line_ptr after the iif directive and the expression
   so the parsing can continue and return the new line_ptr.
   The string is never modified. */
static char *handle_iif(char *line_ptr)
{
  if (strnicmp(line_ptr,"iif",3) == 0 &&
      isspace((unsigned char)line_ptr[3])) {
    char *expr_copy,*expr_end;
    int condition;
    size_t expr_len;

    line_ptr += 3;

    /* Move the line ptr to the beginning of the iif expression. */
    line_ptr = skip(line_ptr);

    /* As eval_ifexp() may modify the input string, duplicate
       it for the case when the parsing should continue. */
    expr_copy = mystrdup(line_ptr);
    expr_end = expr_copy;
    condition = eval_ifexp(&expr_end,1);
    expr_len = expr_end - expr_copy;
    myfree(expr_copy);

    if (condition) {
      /* Parsing should continue after the expression, from the next field. */
      line_ptr += expr_len;
      line_ptr = skip(line_ptr);
    } else {
      /* Parsing should stop, move ptr to the end of the line. */
      line_ptr += strlen(line_ptr);
    }
  }
  return line_ptr;
}

static void handle_switch(char *s)
{
  expr *condexp = parse_expr_tmplab(&s);
  taddr val;

  if (eval_expr(condexp,&val,NULL,0))
    cond_switch(val);
  else
    syntax_error(47);  /* expression must evaluate */
  
  free_expr(condexp);
}

static int eval_case(char *s)
{
  taddr val;
  int b = 0;

  s = skip(s);
  for (;;) {
    if (!eval_expr(parse_expr_tmplab(&s),&val,NULL,0)) {
      syntax_error(47);  /* expression must evaluate */
      break;
    }

    if (cond_match(val)) {
      b = 1;
      break;
    }

    s = skip(s);
    if (*s != ',')
      break;
    s = skip(s+1);
  }

  return b;
}

static void handle_case(char *s)
{
  cond_skipelse();
}

/*
 *  Multiline Comment Block Directives
 */
static void handle_comment(char *s)
{
  new_repeat(0,NULL,NULL,NULL,comend_dirlist);
}

static void handle_comend(char *s)
{
  syntax_error(12,"comend","comment");  /* unexpected comend without comment */
}

/*
 *  Struct Directives
 */
static void handle_endstruct(char *s)
{
  section *structsec = current_section;
  section *prevsec;
  symbol *szlabel;

  if (end_structure(&prevsec)) {
    /* create the structure name as label defining the structure size */
    structsec->flags &= ~LABELS_ARE_LOCAL;
    szlabel = new_labsym(0,structsec->name);
    /* end structure declaration by switching to previous section */
    set_section(prevsec);
    /* avoid that this label is moved into prevsec in set_section() */
    add_atom(structsec,new_label_atom(szlabel));
  }
  eol(s);
}

/*
 *  Module Directives
 */
static void handle_module(char *s)
{
  static int id;
  const char *last;

  if (inline_stack_index < INLSTACKSIZE) {
    sprintf(inl_lab_name,INLLABFMT,id);
    last = set_last_global_label(inl_lab_name);
    if (inline_stack_index == 0)
      saved_last_global_label = last;
    inline_stack[inline_stack_index++] = id++;
  }
  else
    syntax_error(14,INLSTACKSIZE);  /* maximum module nesting depth exceeded */
  eol(s);
}

static void handle_endmodule(char *s)
{
  if (inline_stack_index > 0 ) {
    if (--inline_stack_index == 0) {
      set_last_global_label(saved_last_global_label);
      saved_last_global_label = NULL;
    }
    else {
      sprintf(inl_lab_name,INLLABFMT,inline_stack[inline_stack_index-1]);
      set_last_global_label(inl_lab_name);
    }
  }
  else
    syntax_error(12,"modend","module");  /* unexpected modend without module */
  eol(s);
}

/*
 *  String Stack Directives
 */
static void handle_pushp(char *s)
{
  strbuf *buf;
  symbol *sym;
  char *text;

  s = skip(s);

  if ((buf = get_local_label(0,&s)) || (buf = parse_identifier(0,&s))) {
    if ((sym = find_symbol(buf->str)) && sym->type == STRSYM)
      text = mystrdup(sym->text);
    else {
      syntax_error(27,buf->str); /* string symbol not found */
      return;
    }
  }
  else if (buf = parse_name(0,&s)) {
    text = mystrdup(buf->str);
  }
  else {
    syntax_error(28); /* quoted string or string symbol expected in operand */
    return;
  }

  if (string_stack_index < STRSTACKSIZE)
    string_stack[string_stack_index++] = text;
  else {
    myfree(text);
    syntax_error(32,STRSTACKSIZE);  /* string stack capacity reached */
  }
  eol(s);
}

static void handle_popp(char *s)
{
  strbuf *buf;
  symbol *sym;

  s = skip(s);

  if (string_stack_index > 0 ) {
    if ((buf = get_local_label(0,&s)) || (buf = parse_identifier(0,&s))) {
      if ((sym = find_symbol(buf->str)) && sym->type == STRSYM) {     
        new_strsym(buf->str,string_stack[--string_stack_index]);
        myfree(string_stack[string_stack_index]);
      }
      else {
        syntax_error(27,buf->str); /* string symbol not found */
      }
    }
    else {
      syntax_error(10);  /* identifier expected */
    }
  }
  else {
    syntax_error(33);  /* string stack empty */
  }
  eol(s);
}

/*
 *  Repetition Directives
 */
static void do_irp(int type,char *s)
{
  strbuf *name;

  if(!(name=parse_identifier(0,&s))){
    syntax_error(10);  /* identifier expected */
    return;
  }
  s = skip(s);
  if (*s == ',')
    s = skip(s + 1);
  new_repeat(type,name->str,mystrdup(s),rept_dirlist,endr_dirlist);
}

static void handle_irp(char *s)
{
  do_irp(REPT_IRP,s);
}

static void handle_irpc(char *s)
{
  do_irp(REPT_IRPC,s);
}

static void handle_rept(char *s)
{
  expr *condexp = parse_expr_tmplab(&s);
  taddr cnt;

  if (eval_expr(condexp,&cnt,NULL,0))
    new_repeat(cnt<0?0:(int)cnt,NULL,NULL,rept_dirlist,endr_dirlist);
  else {
    syntax_error(47);  /* expression must evaluate */
    new_repeat(0,NULL,NULL,NULL,endr_dirlist);
  }
  
  free_expr(condexp);
}

static void handle_endr(char *s)
{
  syntax_error(12,"endr","rept");  /* unexpected endr without rept */
}

/*
 *  Conditional Loop Directives
 */
static void handle_while(char *s)
{
  expr *condexp;
  taddr val;
  char *t = skip(s);
  s = t;

  if (ISEOL(t)) {
    general_error(93);
    new_repeat(0,NULL,NULL,NULL,endw_dirlist);
    return;
  }

  condexp = parse_expr_tmplab(&t);

  if (eval_expr(condexp,&val,NULL,0))
    if (val)
      new_repeat(LOOP_WHILE,mystrdup(s),NULL,while_dirlist,endw_dirlist);
    else
      new_repeat(0,NULL,NULL,NULL,endw_dirlist);
  else {
    syntax_error(47);  /* expression must evaluate */
    new_repeat(0,NULL,NULL,NULL,endw_dirlist);
  }

  free_expr(condexp);
}

static void handle_endw(char *s)
{
  syntax_error(12,"endw","while");  /* unexpected endw without while */
}

static void handle_do(char *s)
{
  new_repeat(LOOP_DOUNTIL,NULL,NULL,do_dirlist,until_dirlist);
  eol(s);
}

static void handle_until(char *s)
{
  syntax_error(12,"until","do");  /* unexpected until without do */
}

/*
 *  Macro Directives
 */
static void handle_purge(char *s)
{
  strbuf *name;

  while (name = parse_identifier(0,&s)) {
    undef_macro(name->str);
    s = skip(s);
    if (*s != ',')
      break;
    s = skip(s+1);
  }
}

static void handle_shift(char *s)
{
  symbol *shift = internal_abs(CARGSYM);
  source *src = cur_src;
  int mac_found = 0;

  while (src->parent != NULL) {
    if (src->macro != NULL) {
      mac_found = 1;
      break;
    }
    src = src->parent;
  }

  if (mac_found) {
    if (shift->expr->c.val < maxmacparams)
      shift->expr->c.val++;
  }
  else
    syntax_error(7,"shift");  /* unexpected use of "shift" outside a macro */
  eol(s);
}

static void handle_local(char *s)
{
  source *src = cur_src;

  if (src->macro != NULL) {
    strbuf *name;
    char *found;
  
    while (name = parse_identifier(0,&s)) {
      found = find_macvar(src,name->str,name->len);

      if (found == NULL)
        addmacarg(&src->varnames,name->str,name->str+name->len);
      else
        syntax_error(26,name->str);  /* local macro variable already declared */

      s = skip(s);
      if (*s != ',')
        break;
      s = skip(s+1);
    }
  }
  else
    syntax_error(7,"local");  /* unexpected use of "local" outside a macro */
}

static void handle_mexit(char *s)
{
  leave_macro();
}

static void handle_endm(char *s)
{
  syntax_error(12,"endm","macro");  /* unexpected endm without macro */
}

/*
 *  Section Directives
 */
static void handle_section(char *s)
{
  char *name,*attr=NULL;
  strbuf *buf;

  if (buf = parse_name(0,&s))
    name = buf->str;
  else
    return;

  s = skip(s);
  if (*s == ',') {
    strbuf *attrbuf;

    s = skip(s+1);
    if (attrbuf = get_raw_string(&s,'\"')) {
      attr = attrbuf->str;
      s = skip(s);
    }
  }
  if (attr == NULL) {
    if (!stricmp(name,"code") || !stricmp(name,"text")) {
      attr = code_type;
      name = code_name;
    }
    else if (!strcmp(name,"data")) {
      attr = data_type;
      name = data_name;
    }
    else if (!strcmp(name,"bss")) {
      attr = bss_type;
      name = bss_name;
    }
    else attr = defsecttype;
  }

  set_section(new_section(name,attr,1));
  eol(s);
}

static void handle_pushsect(char *s)
{
  push_section();
  eol(s);
}

static void handle_popsect(char *s)
{
  pop_section();
  eol(s);
}

/*
 *  Linker-Related Directives
 */
static void do_bind(char *s,unsigned bind)
{
  symbol *sym;
  strbuf *name;

  while(1) {
    if(!(name=parse_identifier(0,&s))){
      syntax_error(10);  /* identifier expected */
      return;
    }
    sym = new_import(name->str);
    if (sym->flags & (EXPORT|WEAK|LOCAL) != 0 &&
        sym->flags & (EXPORT|WEAK|LOCAL) != bind) {
      general_error(62,sym->name,get_bind_name(sym)); /* binding already set */
    }
    else {
      sym->flags |= bind;
      if ((bind & XREF)!=0 && sym->type!=IMPORT)
        general_error(85,sym->name);  /* xref must not be defined already */
  }
  s = skip(s);
  if(*s != ',')
      break;
  s = skip(s + 1);
  }
  eol(s);
}

static void handle_global(char *s)
{
  do_bind(s,EXPORT);
}

static void handle_xref(char *s)
{
  do_bind(s,EXPORT|XREF);
}

static void handle_xdef(char *s)
{
  do_bind(s,EXPORT|XDEF);
}

static void handle_public(char *s)
{
  s = skip(s);

  if (!strnicmp(s,"on",2) &&
        (isspace((unsigned char)*(s+2)) || *(s+2)=='\0'
          || *(s+2)==commentchar) || (!strnicmp(s+2,"#||",3))) {
    s = skip(s+2);
    if (!strnicmp(s,"#||",3)) {
      blockcomment = 1;
      *s = '\0';
    }
    public_status = 1;
  }
  else if (!strnicmp(s,"off",3) &&
            (isspace((unsigned char)*(s+3)) || *(s+3)=='\0'
              || *(s+3)==commentchar) || (!strnicmp(s+3,"#||",3))) {
    s = skip(s+3);
    if (!strnicmp(s,"#||",3)) {
      blockcomment = 1;
      *s = '\0';
    }
    public_status = 0;
  }
  else
    syntax_error(24);  /* invalid public parameter */

  eol(s);
}

/*
 *  Miscellaneous Directives
 */
static void handle_radix(char *s)
{
  int base;
  
  radix_base = 10;
  base = parse_constexpr(&s);

  if ((base < 2) || (base > 16))
    syntax_error(9,base);  /* invalid radix base value */
  else
    radix_base = base;
  eol(s);
}

static void handle_disable(char *s)
{
  strbuf *name;

  if (!(name = parse_identifier(0,&s))) {
    syntax_error(10);  /* identifier expected */
    return;
  }

  undef_internal_sym(name->str,nocase);
  eol(s);
}

static void handle_inform(char *s)
{
  int severity = parse_constexpr(&s);
  strbuf *txt;
  s = skip(s);
  
  if (*s != ',') {
    syntax_error(5);  /* missing operand */
    return;
  }
  s = skip(s+1);
  
  if (txt = parse_name(0,&s)) {
    switch (severity) {
    
    case 0:  /* message */
      syntax_error(16,txt->str);  
      break;

    case 1:  /* warning */
      syntax_error(17,txt->str);
      break;

    case 2:  /* error */
      syntax_error(18,txt->str);
      break;

    case 3:  /* fatal error */
      syntax_error(19,txt->str);
      parse_end = 1;
      break;
  
    default: /* invalid message severity */
      syntax_error(15);
      break;
    }
  }
  eol(s);
}

static void handle_list(char *s)
{
  set_listing(1);
  eol(s);
}

static void handle_nolist(char *s)
{
  set_listing(0);
  eol(s);
}

static void handle_fail(char *s)
{
  syntax_error(11);
  parse_end = 1;
}

static void handle_end(char *s)
{
  parse_end = 1;
}

/*
 *  Options Directives
 */
int read_opt_arg(char *s) {
  switch (*s) {
    case '+': return 1;
    case '-': return 0;
    default: return -1;
  }
}

static void handle_opt(char *s)
{
  int arg;

  s = skip(s);
  for (;;) {
    /* check for syntax options */
    if (!strnicmp(s,"ae",2)) {
      s += 2;
      if ((arg = read_opt_arg(s)) != -1)
        options.ae = arg;
      else
        syntax_error(34,*s);
      s++;
    }
    else if (!strnicmp(s,"an",2)) {
      s += 2;
      if ((arg = read_opt_arg(s)) != -1)
        options.an = arg;
      else
        syntax_error(34,*s);
      s++;
    }
    else if (!strnicmp(s,"ws",2)) {
      s += 2;
      if ((arg = read_opt_arg(s)) != -1)
        options.ws = arg;
      else
        syntax_error(34,*s);
      s++;
    }
    else if (!strnicmp(s,"c",1)) {
      s++;
      if ((arg = read_opt_arg(s)) != -1)
        nocase = (options.c = arg) ? 0 : 1;
      else
        syntax_error(34,*s);
      s++;
    }
    else if (!strnicmp(s,"w",1)) {
      s++;
      if ((arg = read_opt_arg(s)) != -1)
        no_warn = (options.w = arg) ? 0 : 1;
      else
        syntax_error(34,*s);
      s++;
    }
    else if (!strnicmp(s,"l",1)) {
      s++;
      if ((arg = read_opt_arg(s)) >= 0) {
        options.l = (arg) ? '.' : '@';
      }
      else
        options.l = *s;
      s++;
    }
    else {
      syntax_error(35);
    }

    s = skip(s);
    if (*s != ',')
      break;
    s = skip(s+1);
  }
  eol(s);
}

static void handle_pusho(char *s)
{
  s = skip(s);

  if (options_stack_index < OPT_STACK_SIZE) {
    options_stack[options_stack_index++] = options;
  }
  else {
    syntax_error(36,OPT_STACK_SIZE);  /* options stack capacity reached */
  }
  eol(s);
}

static void handle_popo(char *s)
{
  s = skip(s);

  if (options_stack_index > 0 ) {
    options = options_stack[--options_stack_index];
    no_warn = (options.w) ? 0 : 1;
    nocase = (options.c) ? 0 : 1;
  }
  else {
    syntax_error(37);  /* options stack is empty */
  }
  eol(s);
}

/*
 *  Directives That Require a Leading Identifier
 */
static void handle_absentid(char *s)
{
  syntax_error(10);  /* identifier expected */
  eol(s);
}

struct {
  const char *name;
  void (*func)(char *);
} directives[] = {
  "=",handle_absentid,
  "==",handle_absentid,
  "alias",handle_absentid,
  "equ",handle_absentid,
  "equs",handle_absentid,
  "func",handle_absentid,
  "macro",handle_absentid,
  "macros",handle_absentid,
#if !defined(VASM_CPU_Z80)
  "set",handle_absentid,
#endif
  "struct",handle_absentid,
  "substr",handle_absentid,

  "rsset",handle_rsset,  
  "rsreset",handle_rsreset,
  "rseven",handle_rseven,

#if defined(VASM_CPU_M68K)
  "rs",handle_rs16,
  "rs.b",handle_rs8,
  "rs.w",handle_rs16,
  "rs.l",handle_rs32,

  "dc",handle_d16,
  "dc.b",handle_d8,
  "dc.w",handle_d16,
  "dc.l",handle_d32,

  "dcb",handle_blk16,
  "dcb.b",handle_blk8,
  "dcb.w",handle_blk16,
  "dcb.l",handle_blk32,

  "ds",handle_spc16,
  "ds.b",handle_spc8,
  "ds.w",handle_spc16,
  "ds.l",handle_spc32,

  "data",handle_data,
  "datasize",handle_datasize,
#else
  "rs",handle_rs8,
  "rsb",handle_rs8,
  "rsw",handle_rs16,
  "rsl",handle_rs32,

  "db",handle_d8,
  "dw",handle_d16,
  "dl",handle_d32,

  "dcb",handle_blk8,
  "dcw",handle_blk16,
  "dcl",handle_blk32,

  "ds",handle_spc8,
  "dsb",handle_spc8,
  "dsw",handle_spc16,
  "dsl",handle_spc32,
#endif

#if FLOAT_PARSER
  "ieee32",handle_single,
  "ieee64",handle_double,
#endif

  "org",handle_org,
  "obj",handle_obj,
  "objend",handle_objend,
  "hex",handle_hex,
  "cnop",handle_cnop,
  "even",handle_even,
  "align",handle_align,

  "incdir",handle_incdir,
  "include",handle_include,
  "incbin",handle_incbin,

  "if",handle_ifne,
  "else",handle_else,
  "elseif",handle_elseif,
  "endif",handle_endif,

  "switch",handle_switch,
  "case",handle_case,
  "default",handle_else,
  "endc",handle_endif,

  "ifb",handle_ifb,
  "ifnb",handle_ifnb,
  "ifc",handle_ifc,
  "ifnc",handle_ifnc,  
  "ifd",handle_ifd,
  "ifnd",handle_ifnd,

  "ifeq",handle_ifeq,
  "ifne",handle_ifne,
  "ifgt",handle_ifgt,
  "ifge",handle_ifge,
  "iflt",handle_iflt,
  "ifle",handle_ifle,

  "module",handle_module,
  "modend",handle_endmodule,
  "comment",handle_comment,
  "comend",handle_comend,
  "ends",handle_endstruct,
  "pushp",handle_pushp,
  "popp",handle_popp,

  "rept",handle_rept,
  "irp",handle_irp,
  "irpc",handle_irpc,
  "endr",handle_endr,
  
  "while",handle_while,
  "endw",handle_endw,
  "do",handle_do,
  "until",handle_until,

  "purge",handle_purge,
  "shift",handle_shift,
  "local",handle_local,
  "mexit",handle_mexit,
  "endm",handle_endm,
  
  "section",handle_section,
  "pushs",handle_pushsect,
  "pops",handle_popsect,

  "global",handle_global,
  "xref",handle_xref,
  "xdef",handle_xdef,
  "public",handle_public,

  "opt",handle_opt,
  "pusho",handle_pusho,
  "popo",handle_popo,
  "radix",handle_radix,
  "disable",handle_disable,
  "inform",handle_inform,
  "list",handle_list,
  "nolist",handle_nolist,
  "fail",handle_fail,
  "end",handle_end,
};

size_t dir_cnt = sizeof(directives) / sizeof(directives[0]);

/* checks for a valid directive, and return index when found, -1 otherwise */
static int check_directive(char **line)
{
  char *s,*name;
  hashdata data;

  s = skip(*line);
  if (!ISIDSTART(*s))
    return -1;
  name = s++;
  while (ISIDCHAR(*s) || *s=='.')
    s++;
  if (!find_namelen_nc(dirhash,name,s-name,&data))
    return -1;
  *line = s;
  return data.idx;
}

/* Handles assembly directives; returns non-zero if the line
   was a directive. */
static int handle_directive(char *line)
{
  int idx = check_directive(&line);

  if (idx >= 0) {
    directives[idx].func(skip(line));
    return 1;
  }
  return 0;
}


static int offs_directive(char *s,char *name)
{
  int len = strlen(name);
  char *d = s + len;

#if defined(VASM_CPU_M68K)
  return !strnicmp(s,name,len) &&
         ((isspace((unsigned char)*d) || ISEOL(d)) ||
          (*d=='.' && (isspace((unsigned char)*(d+2))||ISEOL(d+2))));
#else
  return !strnicmp(s,name,len) && (tolower((unsigned char)*(d))!='t' && (isspace((unsigned char)*(d+1))||ISEOL(d+1)));
#endif
}


static int oplen(char *e,char *s)
{
  while (s!=e && isspace((unsigned char)e[-1]))
    e--;
  return e-s;
}

/* When a structure with this name exists, insert its atoms and either
   initialize with new values or accept its default values. */
static int execute_struct(char *name,int name_len,char *s)
{
  section *str;
  atom *p;

  str = find_structure(name,name_len);
  if (str == NULL)
    return 0;

  for (p=str->first; p; p=p->next) {
    atom *new;
    char *opp;
    int opl;

    if (p->type==DATA || p->type==SPACE || p->type==DATADEF) {
      opp = s = skip(s);
      s = skip_operand(s);
      opl = s - opp;

      if (opl > 0) {
        /* initialize this atom with a new expression */

        if (p->type == DATADEF) {
          /* parse a new data operand of the declared bitsize */
          operand *op;

          op = new_operand();
          if (parse_operand(opp,opl,op,
                            DATA_OPERAND(p->content.defb->bitsize))) {
            new = new_datadef_atom(p->content.defb->bitsize,op);
            new->align = p->align;
            add_atom(0,new);
          }
          else
            syntax_error(8);  /* invalid data operand */
        }
        else if (p->type == SPACE) {
          /* parse the fill expression for this space */
          new = clone_atom(p);
          new->content.sb = new_sblock(p->content.sb->space_exp,
                                       p->content.sb->size,
                                       parse_expr_tmplab(&opp));
          new->content.sb->space = p->content.sb->space;
          add_atom(0,new);
        }
        else {
          /* parse constant data - probably a string, or a single constant */
          dblock *db;

          db = new_dblock();
          db->size = p->content.db->size;
          db->data = db->size ? mycalloc(db->size) : NULL;
          if (db->data) {
            if (*opp=='\"' || *opp=='\'') {
              dblock *strdb;

              strdb = parse_string(&opp,*opp,8);
              if (strdb->size) {
                if (strdb->size > db->size)
                  syntax_error(21,strdb->size-db->size);  /* cut last chars */
                memcpy(db->data,strdb->data,
                       strdb->size > db->size ? db->size : strdb->size);
                myfree(strdb->data);
              }
              myfree(strdb);
            }
            else {
              taddr val = parse_constexpr(&opp);
              void *p;

              if (db->size > sizeof(taddr) && BIGENDIAN)
                p = db->data + db->size - sizeof(taddr);
              else
                p = db->data;
              setval(BIGENDIAN,p,sizeof(taddr),val);
            }
          }
          add_atom(0,new_data_atom(db,p->align));
        }
      }
      else {
        /* empty: use default values from original atom */
        add_atom(0,clone_atom(p));
      }

      s = skip(s);
      if (*s == ',')
        s++;
    }
    else if (p->type == INSTRUCTION)
      syntax_error(20);  /* skipping instruction in struct init */

    /* other atoms are silently ignored */
  }

  return 1;
}

static char *parse_label_or_pc(char **start)
{
  char *s,*name;

  s = *start;
  if (*s == ':') {
    /* anonymous label definition */
    strbuf *buf;
    char num[16];

    buf = make_local_label(0,":",1,num,sprintf(num,"%u",++anon_labno));
    name = buf->str;
    s = skip(s+1);
  }
  else {
    int lvalid;

    if (isspace((unsigned char )*s)) {
      s = skip(s);
      lvalid = 0;  /* colon required, when label doesn't start at 1st column */
    }
    else lvalid = 1;

    if (name = parse_symbol(&s)) {
      s = skip(s);
      if (*s == ':') {
        s++;
        if (*s=='+' || *s=='-')
          return NULL;  /* likely an operand with anonymous label reference */
      }
      else if (!lvalid)
        return NULL;
    }
  }

  if (name==NULL && *s==current_pc_char && !ISIDCHAR(*(s+1))) {
    name = current_pc_str;
    s = skip(s+1);
  }

  if (name)
    *start = s;
  return name;
}


void parse(void)
{
  char *s,*line,*inst,*labname,*callname;
  char *ext[MAX_QUALIFIERS?MAX_QUALIFIERS:1];
  char *op[MAX_OPERANDS];
  int ext_len[MAX_QUALIFIERS?MAX_QUALIFIERS:1];
  int op_len[MAX_OPERANDS];
  int ext_cnt,op_cnt,inst_len;
  int comm_invoked = 0;
  instruction *ip;

  while (line = read_next_line()) {
    if (parse_end)
      continue;
    
    comm_invoked = 0;
    s = line;

    if (!blockcomment) {
      if (!cond_state()) {
        /* skip source until ELSE or ENDIF */
        int idx;

        /* skip label, when present */
        if (labname = parse_label_or_pc(&s)) {
          if (*s == ':')
            s++;  /* skip double-colon */
        }

        /* advance to directive */
        idx = check_directive(&s);
        if (idx >= 0) {
          if (!cond_type()) {
            if (!strncmp(directives[idx].name,"if",2))
              cond_skipif();
            else if (directives[idx].func == handle_switch)
              cond_skipif();
            else if (directives[idx].func == handle_case)
              cond_skipelse();
            else if (directives[idx].func == handle_else)
              cond_else();
            else if (directives[idx].func == handle_endif)
              cond_endif();
            else if (directives[idx].func == handle_elseif) {
              s = skip(s);
              cond_elseif(eval_ifexp(&s,1));
            }
          }
          else {
            if (!strncmp(directives[idx].name,"if",2))
              cond_skipif();
            else if (directives[idx].func == handle_switch)
              cond_skipif();
            else if (directives[idx].func == handle_case)
              cond_elseif(eval_case(s));
            else if (directives[idx].func == handle_else)
              cond_else();
            else if (directives[idx].func == handle_endif)
              cond_endif();
            else if (directives[idx].func == handle_elseif)
              cond_skipelse();
          }
        }
        continue;
      }

      if (labname = parse_label_or_pc(&s)) {
        /* we have found a global or local label, or current-pc character */
        uint32_t symflags = 0;
        symbol *label;

        if (*s == ':') {
          /* double colon automatically declares label as exported */
          symflags |= EXPORT|XDEF;
          s++;
        }

        if (public_status)
          label->flags |= EXPORT|XDEF;

        s = skip(s);

        s = handle_iif(s);

        if (!strnicmp(s,"equ",3) && isspace((unsigned char)*(s+3))) {
          s = skip(s+3);
          label = new_equate(labname,parse_expr_tmplab(&s));
          label->flags |= symflags;
        }
      #if !defined(VASM_CPU_Z80)
        else if (!strnicmp(s,"set",3) && isspace((unsigned char)*(s+3))) {
          /* set allows redefinitions */
          s = skip(s+3);
          label = new_abs(labname,parse_expr_tmplab(&s));
        } 
      #endif
        else if (*s=='=') {
          s++;
          if (*s=='=') {
            /* '==' is shorthand for equ */
            s++;
            s = skip(s);
            label = new_equate(labname,parse_expr_tmplab(&s));
            label->flags |= symflags;
          } 
        else {
          /* '=' is shorthand for set */
          s = skip(s);
          label = new_abs(labname,parse_expr_tmplab(&s));
          }
        }
        else if (!strnicmp(s,"equs",4) && isspace((unsigned char)*(s+4))) {
          strbuf *buf;
          symbol *sym;

          s = skip(s+4);

          if ((buf = get_local_label(1,&s)) || (buf = parse_identifier(1,&s))) {
            if ((sym = find_symbol(buf->str)) && sym->type == STRSYM)
              new_strsym(labname,sym->text);
            else
              syntax_error(27,buf->str); /* string symbol not found */
          }
          else if (buf = parse_name(1,&s)) {
            new_strsym(labname,buf->str);
          }
          else {
            syntax_error(28); /* quoted string or string symbol expected in operand */
          }

          eol(s);
          continue;
        }
        else if (!strnicmp(s,"func",4) && isspace((unsigned char)*(s+4))) {
          static strbuf funcdef;
          strbuf *buf;
          symbol *sym;
          int nargs = 0;
          int i, defined;

          s = skip(s+4);

          while (buf = parse_identifier(1,&s)) {
            if (nargs == MAX_FUNC_ARGS) {
              syntax_error(38,MAX_FUNC_ARGS);
              goto _ERROR_; /* this breaks out of the current loop, frees the memory use by args, and continues the line reading loop */
            }

            if (nargs) {
              for (i=0; i<nargs; i++) {
                if (strlen(funcargs.arg[i])==strlen(buf->str)) {
                  if ((nocase && (!strnicmp(funcargs.arg[i],buf->str,strlen(buf->str)))) || (!strncmp(funcargs.arg[i],buf->str,strlen(buf->str)))) {
                    syntax_error(44,buf->str);
                    goto _ERROR_;
                  }
                }
              }
            }

            funcargs.arg[nargs] = mystrdup(buf->str);
            nargs++;

            s = skip(s);
            if (*s != ',')
              break;
            s = skip(s+1);
          }

          if (nargs == 0) {
            syntax_error(39);
            continue;
          }

          if (*s != '{') {
            syntax_error(40,'{');
            
            _ERROR_:
            if (nargs) {
              for (i=0; i<nargs; i++)
                myfree(funcargs.arg[i]);
            }

            continue;
          }

          s = skip(s+1);
            
          /* initialize the function definition buffer */
          strbuf_alloc(&funcdef,0x100);
          funcdef.str[0] = '\0';
          funcdef.len = 0;

          /* loop through the whole function definition, tokenizing arguments as we go */
          while (*s != '}')  {
            char *end;
            defined = 1;

            if (ISEOL(s)) {
              syntax_error(40,'}');
              goto _ERROR_;
            } 
            else if (*s == '\\') {
              s++;

              if ((end = skip_identifier(s)) != NULL) {
                size_t len = (end-s);
                char *id = cnvstr(s,len);
                int found = 0;

                for (i=0; i<nargs; i++) {
                  if (strlen(funcargs.arg[i])==len) {
                    if ((nocase && (!strnicmp(funcargs.arg[i],id,len))) || (!strncmp(funcargs.arg[i],id,len))) {
                      found = 1;
                      break;
                    }
                  }
                }

                /* if the identifier we read matches the name of an argument, tokenize it in the function definition */
                if (found) {
                  appendchar(&funcdef,'{');
                  appendchar(&funcdef,(i+'0'));
                  appendchar(&funcdef,'}');
                }
                else
                  appendstr(&funcdef,id);

                s = end;

                /* skip terminating '\' if present */
                if (*s == '\\')
                  s++;

                myfree(id);
              }
              else
                appendchar(&funcdef,'\\');
            }
            else if ((end = skip_identifier(s)) != NULL) {
              size_t len = (end-s);
              char *id = cnvstr(s,len);
              int found = 0;

              for (i=0; i<nargs; i++) {
                if (strlen(funcargs.arg[i])==len) {
                  if ((nocase && (!strnicmp(funcargs.arg[i],id,len))) || (!strncmp(funcargs.arg[i],id,len))) {
                    found = 1;
                    break;
                  }
                }
              }

              /* if the identifier we read matches the name of an argument, tokenize it in the function definition */
              if (found) {
                appendchar(&funcdef,'{');
                appendchar(&funcdef,(i+'0'));
                appendchar(&funcdef,'}');
              }
              else
                appendstr(&funcdef,id);

              s = end;
              myfree(id);
            }
            else {
              appendchar(&funcdef,*s);
              s++;
            }
          }

          new_function(labname,funcdef.str,nargs);

          /* free all of the memory used for the function arguments */
          if (nargs) {
            for (i=0; i<nargs; i++)
              myfree(funcargs.arg[i]);
          }

          s = skip(s+1);
          eol(s);
          continue;
        }
        else if (!strnicmp(s,"alias",5) && isspace((unsigned char)*(s+5))) {
          strbuf *buf;
          symbol *sym;

          s = skip(s+5);

          if (!(buf = parse_identifier(1,&s))) {
            syntax_error(10);  /* identifier expected */
            continue;        
          }

          if (!(sym = find_symbol(buf->str)) || !(sym->flags & VASMINTERN)) {
            general_error(90,buf->str);  /* internal symbol not found */
            continue;
          }

          refer_symbol(sym,mystrdup(labname));
          eol(s);
          continue;
        }
        else if (!strnicmp(s,"macros",6) &&
                  (isspace((unsigned char)*(s+6)) || *(s+6)=='\0'
                  || *(s+6)==commentchar) || (!strnicmp(s+6,"#||",3))) {
          char *params = skip(s+6);
          strbuf *buf;

          if (!strnicmp(params,"#||",3)) {
            blockcomment = 1;
            *params = '\0';
          }

          if(ISEOL(params))
            params = NULL;

          s = line;
          if (!(buf = parse_identifier(0,&s)))
            ierror(0);
          new_macro(buf->str,macro_dirlist,NULL,params);
          continue;
        }
        else if (!strnicmp(s,"macro",5) &&
                  (isspace((unsigned char)*(s+5)) || *(s+5)=='\0'
                  || *(s+5)==commentchar) || (!strnicmp(s+5,"#||",3))) {
          char *params = skip(s+5);
          strbuf *buf;
          
          if (!strnicmp(params,"#||",3)) {
            blockcomment = 1;
            *params = '\0';
          }

          if(ISEOL(params))
            params = NULL;

          s = line;
          if (!(buf = parse_identifier(0,&s)))
            ierror(0);
          new_macro(buf->str,macro_dirlist,endm_dirlist,params);
          continue;
        }
        else if (!strnicmp(s,"struct",6) &&
                  (isspace((unsigned char)*(s+6)) || *(s+6)=='\0'
                  || *(s+6)==commentchar) || (!strnicmp(s+6,"#||",3))) {
          strbuf *buf;

          s = line;
          if (!(buf = parse_identifier(0,&s)))
            ierror(0);
          if (new_structure(buf->str))
            current_section->flags |= LABELS_ARE_LOCAL;
          continue;
        }
        else if (!strnicmp(s,"substr",6) && isspace((unsigned char)*(s+6))) {
          strbuf *buf;
          symbol *sym;
          char *text, substr[256];
          int start, end, len;
          char backup;

          s = skip(s+6);

          /* parse start index parameter */
          if (*s == ',') {
            start = 0;
          }
          else {
            start = (parse_constexpr(&s)) - 1;
            if (start < 0) {
              syntax_error(29); /* substring index must be positive */
              continue;
            }
          }
          
          s = skip(s);
          if (*s != ',') {
            syntax_error(5); /* missing operand */
            continue;
          }
          s = skip(s+1);
          
          /* parse end index parameter */
          if (*s == ',') {
            end = -1;
          }
          else {
            end = parse_constexpr(&s);
            if (end < 0) {
              syntax_error(29); /* substring index must be positive */
              continue;
            }
            else if (end <= start) {
              syntax_error(30); /* substring ending index greater than the starting index */
              continue;
            }
          }
          
          s = skip(s);
          if (*s != ',') {
            syntax_error(5); /* missing operand */
            continue;
          }
          s = skip(s+1);
          
          text = s;

          /* duplicate the string data */
          if ((buf = get_local_label(1,&text)) || (buf = parse_identifier(1,&text))) {
            s = text;
            
            if (!(sym = find_symbol(buf->str)) && !(sym->type == STRSYM)) {
              syntax_error(27,buf->str); /* string symbol not found */
              eol(s);
              continue;
            }

            text = mystrdup(sym->text);
          }
          else if (((*s == '\"') && (buf = get_raw_string(&s,'\"'))) || ((*s == '\'') && (buf = get_raw_string(&s,'\'')))) {
            text = mystrdup(buf->str);
          }
          else {
            syntax_error(28); /* quoted string or string symbol expected in operand */
            eol(s);
            continue;
          }

          /* get the copy length and set the ending position if necessary */
          if (end < 0)
            end = strlen(text);
          else if (end > strlen(text)) {
            syntax_error(31); /* substring ending index greater length of string */
            myfree(text);
            eol(s);
            continue;
          }

          len = end - start;

          /* create the substring and assign it to the symbol */
          strncpy(substr,&text[start],len);
          substr[len] = '\0';
          new_strsym(labname,substr);

          /* free the memory containing duplicate string data and continue parsing */
          myfree(text);
          eol(s);
          continue;
        }
        else if (offs_directive(s,"rs")) {
          label = new_setoffset(labname,&s,rs_name,1);
        }

      #ifdef PARSE_CPU_LABEL
        else if (!PARSE_CPU_LABEL(labname,&s)) {
      #else
        else {
      #endif

          strbuf *buf;
          macro *mac;
          char *t = skip(s);

          /* check if there is a macro called on this line that takes a label as an input argument */
          if ((buf = parse_identifier(1,&t)) && (mac = find_macro(buf->str,buf->len)) && (mac->labelarg)) {
            callname = labname;
          }
          else {
            callname = NULL;

            /* add this as a regular label */
            label = new_labsym(0,labname);
            label->flags |= symflags;
            add_atom(0,new_label_atom(label));
          }
        }
      }
    }

    /* check for directives */
    s = skip(s);
    
    /* invoke block comment */
    if (!strnicmp(s,"#||",3)) {
      blockcomment = 1;
      s = skip(s+3);

      if (ISEOL(s)) {
        continue;
      }
    }
    
    /* handle block comment */
    if (blockcomment) {
      char *t = strstr(s,"||#");

      /* if terminating string found, end the block comment */
      if (t) {
        blockcomment = 0;
        s = skip(t+3);

        if (ISEOL(s)) {
          continue;
        }
      }
      else {
        continue; /* otherwise, move on and parse the next line */
      }
    }

    if (*s==commentchar)
      continue;

    s = handle_iif(s);

    s = parse_cpu_special(s);
    if (ISEOL(s))
      continue;

    if (handle_directive(s))
      continue;
  
    s = skip(s);
    if (ISEOL(s))
      continue;

    /* read mnemonic name */
    inst = s;
    ext_cnt = 0;
    if (!ISIDSTART(*s)) {
      syntax_error(10);  /* identifier expected */
      continue;
    }
#if MAX_QUALIFIERS==0
    if (*s && !isspace((unsigned char)*s)) {
      char c = *s;
      if (ISIDSTART(c))
        s++;
    }
    while (*s && !isspace((unsigned char)*s)) {
      char c = *s;
      if (!ISIDCHAR(c))
        break;
      s++;
    }
    inst_len = s - inst;
#else
    s = parse_instruction(s,&inst_len,ext,ext_len,&ext_cnt);
#endif
    if (!isspace((unsigned char)*s) && *s!='\0') {
      /* invoke block comment */
      if (!strnicmp(s,"#||",3)) {
        blockcomment = 1;
        comm_invoked = 1;
        s = skip(s+3);
      }
      else if (*s==commentchar)
        comm_invoked = 1;
      else
        syntax_error(2);  /* no space before operands */
    }
    s = skip(s);

    if (execute_macro(inst,inst_len,ext,ext_len,ext_cnt,s,callname))
      continue;
    if (execute_struct(inst,inst_len,s))
      continue;

    /* read operands, terminated by comma or blank (unless in parentheses) */
    op_cnt = 0;
    if (!comm_invoked) {
      while (!ISEOL(s) && op_cnt<MAX_OPERANDS) {
        op[op_cnt] = s;
        s = skip_operand(s);
        op_len[op_cnt] = oplen(s,op[op_cnt]);
      #if !ALLOW_EMPTY_OPS
        if (op_len[op_cnt] <= 0)
          syntax_error(5);  /* missing operand */
        else
      #endif
        op_cnt++;
        
        if (options.ws) {
          s = skip(s);
          if (*s != ',')
            break;
          else
            s = skip(s+1);
        }
        else {
          if (*s != ',')
            break;
          s++;
        }
      }
    }
    eol(s);

    ip = new_inst(inst,inst_len,op_cnt,op,op_len);

#if MAX_QUALIFIERS>0
    if (ip) {
      int i;

      for (i=0; i<ext_cnt; i++)
        ip->qualifiers[i] = cnvstr(ext[i],ext_len[i]);
      for(; i<MAX_QUALIFIERS; i++)
        ip->qualifiers[i] = NULL;
    }
#endif

    if (ip) {
#if MAX_OPERANDS>0
      if (options.ws && ip->op[0]==NULL && op_cnt!=0)
        syntax_error(6);  /* mnemonic without operands has tokens in op.field */
#endif
      add_atom(0,new_inst_atom(ip));
    }
  }

  cond_check();  /* check for open conditional blocks */
}

/* src is the new macro source, cur_src is still the parent source */
void my_exec_macro(source *src)
{
  symbol *sym;

  /* reset the macro argument shift amount to 0, selecting the first macro parameter */
  sym = internal_abs(CARGSYM);
  cur_src->cargexp = sym->expr;  /* remember last argument shift amount */
  sym->expr = number_expr(0);

  /* set the argument count for the current macro call */
  sym = internal_abs(NARGSYM);
  cur_src->nargexp = sym->expr;  /* remember last argument count */
  sym->expr->c.val = src->num_params;
}

/* parse next macro argument */
char *parse_macro_arg(struct macro *m,char *s,
                      struct namelen *param,struct namelen *arg)
{
  arg->len = 0;  /* cannot select specific named arguments */
  param->name = s;
  
  if (*s == '{') {
    /* macro argument enclosed in { ... } */
    param->name++;
    while (*++s != '\0') {
      if (*s == '}') {
        param->len = s - param->name;
        return s + 1;
      }
    }
    syntax_error(23); /* enclosed macro argument missing } */
    return NULL;
  }
  s = skip_operand(s);
  param->len = s - param->name;
  return s;
}

/* write 0 to buffer when macro argument is missing or empty, 1 otherwise */
static int macro_arg_defined(source *src,char *argstart,char *argend,char *d,int type)
{
  symbol *shift = internal_abs(CARGSYM);
  int n;

  if (type) {
    n = find_macarg_name(src,argstart,argend-argstart);
  }
  else {
    n = *(argstart) - '0';

    if (n == 0) {
#if MAX_QUALIFIERS > 0
      *d++ = ((src->qual_len[0] > 0) ? '1' : '0');
#else
      *d++ = '0';
#endif
       return 1;    
    } 
    else {
      n--;
    }
  }

  n += shift->expr->c.val;

  if (n >= 0) {
    /* valid argument name */
    *d++ = (n<src->num_params && n<maxmacparams && src->param_len[n]>0) ?
           '1' : '0';
    return 1;
  }
  return 0;
}

/* expands arguments and special escape codes into macro context */
int expand_macro(source *src,char **line,char *d,int dlen)
{
  symbol *shift = internal_abs(CARGSYM);
  int nc = 0;
  int n;
  char *s = *line;
  char *end;

  if (*s == '\\') {
    /* possible macro expansion detected */
    s++;

    if (*s == '@') {
      /* \@: insert a unique id */
      if (dlen > 7) {
        nc += sprintf(d,"_%lu",src->id);
        s++;
      }
      else {
        nc = -1;
      }
    }
    else if (*s == '*') {
      /* \*: insert the label from the line this macro was called on */
      if (src->callname) {
        nc = sprintf(d,"%s",src->callname);
        s++;
      }
      else {
        s--;
        return 0;
      }
    }
    else if (*s == '_') {
      /* \_: insert the full list of arguments passed to this macro call */
      if (src->callargs) {
        nc = sprintf(d,"%s",src->callargs);
        s++;
      }
      else {
        s--;
        return 0;
      }
    }
    else if (*s=='?' && dlen>=1) {
      /* \?n : check if numeric parameter is defined */
      if (isdigit((unsigned char)*(s+1)) && dlen > 3) {
        if ((nc = macro_arg_defined(src,s+1,s+2,d,0)) >= 0)
          s += 2;
      }
      else if ((end = skip_identifier(s+1)) != NULL) {
        /* \?argname : check if named parameter is defined */
        if ((nc = macro_arg_defined(src,s+1,end,d,1)) >= 0)
          s = end;
      }
      else {
        nc = -1;
      }
    }
    else if (isdigit((unsigned char)*s)) {
      /* \0..\9 : insert macro parameter 0..9 */
      if (*s == '0')
        nc = copy_macro_qual(src,0,d,dlen);
      else
        nc = copy_macro_param(src,(*s-'1'+shift->expr->c.val),d,dlen);
      s++;
    }
    else if ((end = skip_identifier(s)) != NULL) {
      char *varname;

      if ((n = find_macarg_name(src,s,end-s)) >= 0) {
        /* \argname: insert named macro parameter n */
        nc = copy_macro_param(src,(n+shift->expr->c.val),d,dlen);
        s = end;
      }
      else if ((varname = find_macvar(src,s,end-s)) != NULL) {
        /* \varname: insert local macro variable and handle string symbol expansion */
        symbol *sym;
        char *t = d;
        source *parent = src;

        while (parent) {
          if (parent->macro)
            break;
          parent = parent->parent;
        }

        nc = sprintf(d,"%s_%lu$",varname,parent->id);

        if (varname = parse_symbol(&t)) {
          if ((sym = find_symbol(varname)) && sym->type == STRSYM) {
            nc = sprintf(d,sym->text);
          }
        }

        s = end;
      }
    }
    else {
      s--;
      return 0;
    }

    /* skip terminating '\' if present */
    if (*s == '\\')
      s++;

    if (nc >= dlen)
      nc = -1;
    else if (nc >= 0)
      *line = s;  /* update line pointer when expansion took place */
  }
  else if (*s == '{') {
  /* possible local macro string variable expansion detected */
    s++;

    if ((end = skip_identifier(s)) != NULL) {
      char *varname;

      if ((varname = find_macvar(src,s,end-s)) != NULL) {
        symbol *sym;
        char *t = d + 1;
        source *parent = src;

        while (parent) {
          if (parent->macro)
            break;
          parent = parent->parent;
        }

        if (*end == '}') {
          nc = sprintf(d,"{%s_%lu$}",varname,parent->id);
          s = end + 1;
        }
        else {
          nc = sprintf(d,"{%s_%lu$",varname,parent->id);
          s = end;
        }

        if (varname = parse_symbol(&t)) {
          if ((*end == '}') && (sym = find_symbol(varname)) && sym->type == STRSYM) {
            nc = sprintf(d,sym->text);
            s = end + 1;
          }
        }
      }
    }
    else {
      s--;
      return 0;
    }

    if (nc >= dlen)
      nc = -1;
    else if (nc >= 0)
     *line = s;  /* update line pointer when expansion took place */
  }
  else if ((end = skip_identifier(s)) != NULL) {
  /* possible named macro argument or variable expansion detected (without leading '\') */
    char *varname;

    if ((n = find_macarg_name(src,s,end-s)) >= 0) {
      /* argname: insert named macro parameter n */
      nc = copy_macro_param(src,(n+shift->expr->c.val),d,dlen);
      s = end;
    }
    else if ((varname = find_macvar(src,s,end-s)) != NULL) {
      /* varname: insert local macro variable */
      source *parent = src;

      while (parent) {
        if (parent->macro)
          break;
        parent = parent->parent;
      }

      nc = sprintf(d,"%s_%lu$",varname,parent->id);
      s = end;
    }
    else {
      strbuf *name = parse_identifier(0,&s);

      nc = sprintf(d,"%s",name->str);
      s = end;
    }

    if (nc >= dlen)
      nc = -1;
    else if (nc >= 0)
     *line = s;  /* update line pointer when expansion took place */
  }

  return nc;  /* number of chars written to line buffer, -1: out of space */
}

int expand_ctrlparams(source *src,char **line,char *d,int dlen)
{
  symbol *sym, *shift = internal_abs(CARGSYM);
  int nc = 0;
  int n;
  char *s = *line;
  char *name, *end;

  if (*s == '\\') {
    /* possible control character or symbolic expansion detected */
    s++;

    /* \^<ctrl_char>: insert control character according to carrot notation */
    /*
    if (*s == '^') {
      char ctrl = 0x20;
      s++;

      if ((*s >= '@' && *s <= 'z') && *s != '`')
        ctrl = *s & 0x1F;
      else if (*s == '?')
        ctrl = 0x7F;

      if (ctrl != 0x20)
        nc = sprintf(d,"%c",ctrl);
      else
        nc = 0;
    }
    */
    if (*s == '#' || *s == '$') {
      /* \# or \$ : insert absolute unsigned symbol value (decimal or hex) */
      const char *fmt;
      taddr val;

      fmt = (*s == '$') ? "%lX" : "%lu";
      s++;
      
      /* check if we're numerically expanding a local macro variable */
      if ((src->macro != NULL) && ((end = skip_identifier(s)) != NULL) && ((name = find_macvar(src,s,end-s)) != NULL)) {
        char *t = d;
        nc = sprintf(d,"%s_%lu$",name,src->id);

        if (name = parse_symbol(&t)) {
          if ((sym = find_symbol(name)) && ((sym->type == EXPRESSION) || (sym->type == STRSYM))) {
            if (eval_expr(sym->expr,&val,NULL,0)) {
              if (dlen > 9) {
                nc = sprintf(d,fmt,(unsigned long)(uint32_t)val);
                s = end;
              }
              else
                nc = -1;
            }
          }
          if (nc <= 0) {
            syntax_error(22);  /* invalid numeric expansion */
            return 0;
          }
        }
      }
      else if (name = parse_symbol(&s)) {
        if ((sym = find_symbol(name)) && ((sym->type == EXPRESSION) || (sym->type == STRSYM))) {
          if (eval_expr(sym->expr,&val,NULL,0)) {
            if (dlen > 9)
              nc = sprintf(d,fmt,(unsigned long)(uint32_t)val);
            else
              nc = -1;
          }
        }
        if (nc <= 0) {
          syntax_error(22);  /* invalid numeric expansion */
          return 0;
        }
      }
      else {
        syntax_error(10);  /* identifier expected */
        return 0;
      }

    }
    else if (name = parse_symbol(&s)) {
      if ((sym = find_symbol(name)) && sym->type == STRSYM) {
        nc = sprintf(d,sym->text);
      }
    }
    else {
      s--;
      return 0;
    }

    /* skip terminating '\' if present */
    if (*s == '\\')
      s++;

    if (nc >= dlen)
      nc = -1;
    else if (nc >= 0)
      *line = s;  /* update line pointer when expansion took place */
  }
  else if (*s == '{') {
    /* possible string symbol expansion detected */
    s++;

    if (name = parse_symbol(&s)) {
      if ((*s == '}') && (sym = find_symbol(name)) && (sym->type == STRSYM)) {
        nc = sprintf(d,sym->text);
        s++;
      }
    }
    else {
      s--;
      return 0;
    }

    if (nc >= dlen)
      nc = -1;
    else if (nc >= 0)
      *line = s;  /* update line pointer when expansion took place */
  }

  return nc;  /* number of chars written to line buffer, -1: out of space */
}

int find_function_in_line(char *s)
{
  symbol *sym;
  char *name, *t;
  char *commend = strstr(s,"||#");

  /* if we're inside a block comment, don't look for functions *unless* it ends on this line,
     whichcase we start searching for functions after the block comment is closed */
  if (commend) {
    s = skip(commend+3);
  }

  if (blockcomment) {
    if (!commend)
      return 0;
  }

  while (!ISEOL(s)) {
  
    /* skip block comments that appear on this line */
    if ((strlen(s) >= 3) && (!strnicmp(s,"#||",3))) {
      s = skip(s+3);
      
      if ((strlen(s) >= 3) && (commend = strstr(s,"||#"))) {
        s = skip(commend+3);

        if (ISEOL(s)) {
          break;
        }
      }
      else {
        break;
      }
    }

    t = s;

    if ((!ISIDSTART(*(t-1))) && (!ISIDCHAR(*(t-1)))
        && ((name = parse_symbol(&t)) && (*t == '('))
        && ((sym = find_symbol(name)) && (sym->type == FUNCTION)))
      return 1;

    s++;
  }

  return 0;
}

char get_comment_char()
{
  return commentchar;
}

char *skip_function_call_args(char *s) {
  while (!ISEOL(s)) {
    int parenthDepth = 0;  /* depth of the current set of parenthesis */

    if (*s == '(')
      parenthDepth++;      
    else if (*s == ')') {
      if (parenthDepth == 0) {
        break;
      }
      parenthDepth--;
    }

    s = skip(s+1);
  }

  if (ISEOL(s))
    syntax_error(41); /* unexpected EOL */
  else
    s++;
  
  return s;
}

int expand_function(source *src,char **line,char *d,int dlen)
{
  static strbuf expansion;
  symbol *sym;
  int nc = 0;
  char *s = *line;
  char *name;

  if ((!ISIDSTART(*(s-1))) && (!ISIDCHAR(*(s-1))) && ((name = parse_symbol(&s)) && (*s == '(')))
  { 
    if ((nocase && (!strnicmp(name,"def",3))) || (!strncmp(name,"def",3))) {
      int result = 0;
      char *args;

      s = skip(s+1);
      args = s;

      if (name = parse_symbol(&s)) {
        if (sym = find_symbol(name))
          result = (sym->type != IMPORT);
      }
      else {
        syntax_error(10);  /* identifier expected */
        
        s = skip_function_call_args(args);
        nc = sprintf(d,"(0)");
        goto _EXIT_;
      }
      
      s = skip(s);

      if (*s == ')') {
        nc = sprintf(d,"(%d)",BOOLEAN(result));
        s++;
      }
      else {
        syntax_error(43); /* generic error in function call */
        
        s = skip_function_call_args(s);        
        nc = sprintf(d,"(0)");
      }
    }
    else if ((nocase && (!strnicmp(name,"ref",3))) || (!strncmp(name,"ref",3))) {
      int result = 0;
      char *args;

      s = skip(s+1);
      args = s;

      if (name = parse_symbol(&s)) {
        if (sym = find_symbol(name))
          result = (sym->type == IMPORT);
        else
          result = 1;
      }
      else {
        syntax_error(10);  /* identifier expected */
        
        s = skip_function_call_args(args);
        nc = sprintf(d,"(0)");
        goto _EXIT_;
      }
      
      s = skip(s);

      if (*s == ')') {
        nc = sprintf(d,"(%d)",BOOLEAN(result));
        s++;
      }
      else {
        syntax_error(43); /* generic error in function call */
        
        s = skip_function_call_args(s);        
        nc = sprintf(d,"(0)");
      }
    }
    else if ((nocase && (!strnicmp(name,"strlen",6))) || (!strncmp(name,"strlen",6))) {
      int result = 0;
      strbuf *buf;
      char *args;

      s = skip(s+1);
      args = s;

      if (((*s == '\"') && (buf = get_raw_string(&s,'\"'))) || ((*s == '\'') && (buf = get_raw_string(&s,'\'')))) {
        result = buf->len;
      }
      else {
        syntax_error(28); /* quoted string or string symbol expected in operand */
        
        s = skip_function_call_args(args);
        nc = sprintf(d,"(0)");
        goto _EXIT_;
      }
      
      s = skip(s);

      if (*s == ')') {
        nc = sprintf(d,"(%d)",result);
        s++;
      }
      else {
        syntax_error(43); /* generic error in function call */
        
        s = skip_function_call_args(args);        
        nc = sprintf(d,"(0)");
      }
    }
    else if ((nocase && (!strnicmp(name,"strcmp",6))) || (!strncmp(name,"strcmp",6))) {
      int result = 0;
      strbuf *buf;
      char *args, *texta;

      s = skip(s+1);
      args = s;

      /* text a */
      if (((*s == '\"') && (buf = get_raw_string(&s,'\"'))) || ((*s == '\'') && (buf = get_raw_string(&s,'\'')))) {
        texta = mystrdup(buf->str);
      }
      else {
        syntax_error(28); /* quoted string or string symbol expected in operand */
        
        s = skip_function_call_args(args);
        nc = sprintf(d,"(0)");
        goto _EXIT_;
      }
      
      s = skip(s);

      if (*s != ',') {
        syntax_error(42,2,1); /* too few arguments */
        
        s = skip_function_call_args(args);        
        nc = sprintf(d,"(0)");
        myfree(texta);
        goto _EXIT_;
      }

      s = skip(s+1);

      /* text b */
      if (((*s == '\"') && (buf = get_raw_string(&s,'\"'))) || ((*s == '\'') && (buf = get_raw_string(&s,'\'')))) {
        if (!strcmp(texta,buf->str))
          result = -1;
        else
          result = 0;
      }
      else {
        syntax_error(28); /* quoted string or string symbol expected in operand */
        
        s = skip_function_call_args(args);
        nc = sprintf(d,"(0)");
        myfree(texta);
        goto _EXIT_;
      }

      s = skip(s);

      if (*s == ')') {
        nc = sprintf(d,"(%d)",result);
        s++;
      }
      else {
        syntax_error(43); /* generic error in function call */
        
        s = skip_function_call_args(args);        
        nc = sprintf(d,"(0)");
        myfree(texta);
      }
    }
    else if ((nocase && (!strnicmp(name,"stricmp",7))) || (!strncmp(name,"stricmp",7))) {
      int result = 0;
      strbuf *buf;
      char *args, *texta;

      s = skip(s+1);
      args = s;

      /* text a */
      if (((*s == '\"') && (buf = get_raw_string(&s,'\"'))) || ((*s == '\'') && (buf = get_raw_string(&s,'\'')))) {
        texta = mystrdup(buf->str);
      }
      else {
        syntax_error(28); /* quoted string or string symbol expected in operand */
        
        s = skip_function_call_args(args);
        nc = sprintf(d,"(0)");
        goto _EXIT_;
      }
      
      s = skip(s);

      if (*s != ',') {
        syntax_error(42,2,1); /* too few arguments */
        
        s = skip_function_call_args(args);        
        nc = sprintf(d,"(0)");
        myfree(texta);
        goto _EXIT_;
      }

      s = skip(s+1);

      /* text b */
      if (((*s == '\"') && (buf = get_raw_string(&s,'\"'))) || ((*s == '\'') && (buf = get_raw_string(&s,'\'')))) {
        if (!stricmp(texta,buf->str))
          result = -1;
        else
          result = 0;
      }
      else {
        syntax_error(28); /* quoted string or string symbol expected in operand */
        
        s = skip_function_call_args(args);
        nc = sprintf(d,"(0)");
        myfree(texta);
        goto _EXIT_;
      }

      s = skip(s);

      if (*s == ')') {
        nc = sprintf(d,"(%d)",result);
        s++;
      }
      else {
        syntax_error(43); /* generic error in function call */
        
        s = skip_function_call_args(args);        
        nc = sprintf(d,"(0)");
        myfree(texta);
      }
    }
    else if ((nocase && (!strnicmp(name,"instr",5))) || (!strncmp(name,"instr",5))) {
      int result = 0, start = 1;
      strbuf *buf;
      char *args, *string;

      s = skip(s+1);
      args = s;

      /* parse start index parameter (if present) */
      if ((*s != '\"') && (*s != '\'')) {
        start = parse_constexpr(&s);
        
        if (start <= 0) {
          syntax_error(29); /* substring index must be positive */

          s = skip_function_call_args(args);        
          nc = sprintf(d,"(0)");
          goto _EXIT_;
        }

        s = skip(s);

        if (*s != ',') {
          syntax_error(42,3,1); /* too few arguments */

          s = skip_function_call_args(args);        
          nc = sprintf(d,"(0)");
          goto _EXIT_;
        }

        s = skip(s+1);
      }

      /* parse the main string parameter */
      if (((*s == '\"') && (buf = get_raw_string(&s,'\"'))) || ((*s == '\'') && (buf = get_raw_string(&s,'\'')))) {
        if (start >= buf->len) {
          syntax_error(46); /* start index greater than string length */

          s = skip_function_call_args(args);        
          nc = sprintf(d,"(0)");
          goto _EXIT_;
        }

        string = mystrdup(buf->str);
      }
      else {
        syntax_error(28); /* quoted string or string symbol expected in operand */
        
        s = skip_function_call_args(args);
        nc = sprintf(d,"(0)");
        goto _EXIT_;
      }
      s = skip(s);

      if (*s != ',') {
        if (start)
          syntax_error(42,3,1); /* too few arguments */
        else
          syntax_error(42,2,1); /* too few arguments */
        
        s = skip_function_call_args(args);        
        nc = sprintf(d,"(0)");
        myfree(string);
        goto _EXIT_;
      }

      s = skip(s+1);

      /* parse the substring parameter and determine the function's output value */
      if (((*s == '\"') && (buf = get_raw_string(&s,'\"'))) || ((*s == '\'') && (buf = get_raw_string(&s,'\'')))) {
        char *found = strstr((string + start - 1),buf->str);
        
        if (found)
          result = found - string + 1;
        else
          result = 0;
      }
      else {
        syntax_error(28); /* quoted string or string symbol expected in operand */
        
        s = skip_function_call_args(args);
        nc = sprintf(d,"(0)");
        myfree(string);
        goto _EXIT_;
      }

      s = skip(s);

      if (*s == ')') {
        nc = sprintf(d,"(%d)",result);
        s++;
      }
      else {
        syntax_error(43); /* generic error in function call */
        
        s = skip_function_call_args(args);        
        nc = sprintf(d,"(0)");
        myfree(string);
      }
    }
    else if ((nocase && (!strnicmp(name,"sqrt",4))) || (!strncmp(name,"sqrt",4))) {
      int64_t result;
      strbuf *buf;

      s = skip(s+1);
      result = parse_constexpr(&s);

      if (result < 0)
        result = UINT32_MAX + result + 1;

      result = (int)(sqrt((double)(result)));
      nc = sprintf(d,"(%d)",result);

      s = skip(s);

      if (*s == ')') {
        s++;
      }
      else {
        syntax_error(43); /* generic error in function call */
        
        s = skip_function_call_args(s);
      }
    }
    else if ((nocase && (!strnicmp(name,"filesize",8))) || (!strncmp(name,"filesize",8))) {
      char *filename;
      strbuf *name;
      FILE *f;
      size_t size = -1;

      s = skip(s+1);
      
      if ((*s != '\"') && (*s != '\'')) {
        syntax_error(45); /* file path must be in quotes */

        s = skip_function_call_args(s);
        nc = sprintf(d,"(-1)");
        goto _EXIT_;
      }
      else if (name = parse_name(0,&s)) {
        filename = convert_path(name->str);

        if (f = locate_file(filename,"rb",NULL,0)) {
          size = filesize(f);
          fclose(f);
        }

        myfree(filename);
      }

      s = skip(s);

      if (*s == ')') {
        nc = sprintf(d,"(%d)",size);
        s++;
      }
      else {
        syntax_error(43); /* generic error in function call */
        
        s = skip_function_call_args(s);        
        nc = sprintf(d,"(-1)");
      }
    }
    else if ((sym = find_symbol(name)) && (sym->type == FUNCTION)) {
      char *funcdef = sym->text;
      char *args = skip(s+1);
      taddr nargs;
      int i, n;

      eval_expr(sym->expr,&nargs,sym->sec,sym->pc);

      /* parse and expand the function arguments passed to this call */
      for (i=0; i<nargs; i++) {
        int parenthDepth = 0;  /* depth of the current set of parenthesis */
        char *end = args;
        
        while (*end != ',') {
          if (ISEOL(end)) {
            syntax_error(41); /* unexpected EOL */

            /* free the memory of any funcarg that we've allocated memory for */
            for (n=0; n<i; n++)
              myfree(funcargs.arg[n]);
              
            s = end;
            nc = sprintf(d,"(0)");
            goto _EXIT_;
          }

          if (*end == '(')
            parenthDepth++;      
          else if (*end == ')') {
            if (parenthDepth == 0) {
              break;
            }
            parenthDepth--;
          }
          
          if ((parenthDepth == 0) && (isspace((unsigned char )*s)))
            break;
          
          end = skip(end+1);
        }

        funcargs.arg[i] = cnvstr(args,end-args);
        end = skip(end);

        if (*end == ')') {
          s = end + 1;

          if ((i+1) < nargs) {
            syntax_error(42,nargs,i+1); /* too few args */

            /* free the memory of any funcarg that we've allocated memory for */
            for (n=0; n<=i; n++)
              myfree(funcargs.arg[n]);

            nc = sprintf(d,"(0)");
            goto _EXIT_;
          }

          /* if the closing parenthesis is found and the number of arguments passed matches the expected amount, break out of the loop. */
          break;
        } else {
          if ((i+1) == nargs) {
            syntax_error(43); /* generic error in function call */

            /* free the memory of any funcarg that we've allocated memory for */
            for (n=0; n<=i; n++)
              myfree(funcargs.arg[n]);
            
            nc = sprintf(d,"(0)");
            goto _EXIT_;
          }
        }

        args = skip(end+1);
      }

      /* initialize the expansion buffer */
      strbuf_alloc(&expansion,0x100);
      expansion.str[0] = '\0';
      expansion.len = 0;

      /* append the opening parenthesis */
      appendchar(&expansion,'(');

      /* read through the function definition and print it to the expansion buffer, expanding the arguments as we go */
      while (!ISEOL(funcdef)) {
        if (*funcdef == '{') {
          char *currarg;
          
          funcdef++;
          /* this if statement should always hold true, but it's here just in case */
          if ((*funcdef-'0') < nargs) {
            currarg = funcargs.arg[*funcdef-'0'];
            appendstr(&expansion,currarg);
          }
          funcdef++;
        } else {
          appendchar(&expansion,*funcdef);
        }
        funcdef++;
      }

      /* append the closing parenthesis */
      appendchar(&expansion,')');

      /* free all of the memory used for the function arguments */
      for (i=0; i<nargs; i++)
        myfree(funcargs.arg[i]);

      /* finally, print the fully expanded function in place of the function call */
      nc = sprintf(d,expansion.str);
    }

    _EXIT_:
    if (nc >= dlen)
      nc = -1;
    else if (nc > 0)
      *line = s;  /* update line pointer when expansion took place */
  }

  return nc;  /* number of chars written to line buffer, -1: out of space */
}

int init_syntax()
{
  size_t i;
  hashdata data;
  
  time_t t = time(NULL);
  struct tm date = *localtime(&t);
  symbol *sym;

  dirhash = new_hashtable(0x1000);
  for (i=0; i<dir_cnt; i++) {
    data.idx = i;
    add_hashentry(dirhash,directives[i].name,data);
  }
  if (debug && dirhash->collisions)
    fprintf(stderr,"*** %d directive collisions!!\n",dirhash->collisions);

  options.c = (nocase) ? 0 : 1;
  options.w = (no_warn) ? 0 : 1;

  cond_init();
  set_internal_abs(REPTNSYM,-1); /* reserve the REPTN symbol */
  
  /* refer Psy-Q names to inaccessible internal symbols */
  sym = internal_abs(NARGSYM);
  refer_symbol(sym,"narg");
  sym = internal_abs(rs_name);
  refer_symbol(sym,"__rs");
  
  current_pc_char = '*';
  current_pc_str[0] = current_pc_char;
  current_pc_str[1] = 0;
  esc_sequences = 0;
  
  /*
   * Date & Time Constant Definitions 
   */

  /* year */
  sym = internal_abs(year_name);
  while (date.tm_year > 100)
    date.tm_year -= 100;
  set_internal_abs(year_name,date.tm_year);
  sym->flags |= EQUATE;
  
  /* month */
  sym = internal_abs(month_name);
  set_internal_abs(month_name,date.tm_mon + 1);
  sym->flags |= EQUATE;

  /* weekday */
  sym = internal_abs(weekday_name);
  set_internal_abs(weekday_name,date.tm_wday + 1);
  sym->flags |= EQUATE;

  /* day */
  sym = internal_abs(day_name);
  set_internal_abs(day_name,date.tm_mday);
  sym->flags |= EQUATE;

  /* hours */
  sym = internal_abs(hours_name);
  set_internal_abs(hours_name,date.tm_hour);
  sym->flags |= EQUATE;

  /* minutes */
  sym = internal_abs(minutes_name);
  set_internal_abs(minutes_name,date.tm_min);
  sym->flags |= EQUATE;

  /* seconds */
  sym = internal_abs(seconds_name);
  set_internal_abs(seconds_name,date.tm_sec);
  sym->flags |= EQUATE;

  /* define built-in functions */
  sym = internal_abs("def");
  sym->type = FUNCTION;
  sym = internal_abs("ref");
  sym->type = FUNCTION;
  sym = internal_abs("strlen");
  sym->type = FUNCTION;
  sym = internal_abs("strcmp");
  sym->type = FUNCTION;
  sym = internal_abs("stricmp");
  sym->type = FUNCTION;
  sym = internal_abs("instr");
  sym->type = FUNCTION;
  sym = internal_abs("sqrt");
  sym->type = FUNCTION;
  sym = internal_abs("filesize");
  sym->type = FUNCTION;

  return 1;
}

int syntax_defsect(void)
{
  defsectname = code_name;
  defsecttype = code_type;
  return 1;
}


int syntax_args(char *p)
{
  if (!strcmp(p,"-noalign"))
    options.ae = 0;
  else if (!strcmp(p,"-spaces"))
    options.ws = 1;
  else if (!strcmp(p,"-altnum"))
    options.an = 1;
  else if (!strcmp(p,"-altlocal"))
    options.l = '.';
  else if (!strcmp(p,"-ldots"))
    dot_idchar = 1;
  else
    return 0;

  return 1;
}
