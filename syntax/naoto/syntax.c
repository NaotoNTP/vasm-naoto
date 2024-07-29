/* syntax.c  syntax module for vasm */
/* (c) in 2024 by 'Naoto' */

#include "vasm.h"
/*#include "error.h"*/

/* The syntax module parses the input (read_next_line), handles
   assembly-directives (section, data-storage etc.) and parses
   mnemonics. Assembly instructions are split up in mnemonic name,
   qualifiers and operands. new_inst returns a matching instruction,
   if one exists.
   Routines for creating sections and adding atoms to sections will
   be provided by the main module.
*/

const char *syntax_copyright="vasm custom syntax module (c) 2024 'Naoto'";

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

hashtable *dirhash;
char commentchar = ';';
int dotdirs;

/* default sections */
static char code_name[] = "CODE",code_type[] = "acrx";
static char data_name[] = "DATA",data_type[] = "adrw";
static char bss_name[] = "BSS",bss_type[] = "aurw";

static char rs_name[] = "__RS";

static struct namelen macro_dirlist[] = {
  { 5,"macro" }, { 0,0 }
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

static int parse_end = 0;

/* options */
static int align_data;
static int allow_spaces;
static int alt_numeric;
static char local_char = '.';

static char *labname;  /* current label field for assignment directives */
static unsigned anon_labno;
static char current_pc_str[2];

/* isolated local labels block */
#define INLSTACKSIZE 100
#define INLLABFMT "=%06d"
static int inline_stack[INLSTACKSIZE];
static int inline_stack_index;
static const char *saved_last_global_label;
static char inl_lab_name[8];

int isidchar(char c)
{
  if (isalnum((unsigned char)c) || c=='_')
    return 1;
  return 0;
}

char *skip(char *s)
{
  while (isspace((unsigned char )*s))
    s++;
  return s;
}

/* check for end of line, issue error, if not */
void eol(char *s)
{
  if (allow_spaces) {
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
  if (allow_spaces) {
    char *start = s;

    s = skip(start);
    if (*s == commentchar)
      *s = '\0';  /* rest of operand is ignored */
  }
  else if (isspace((unsigned char)*s) || *s==commentchar)
    *s = '\0';  /* rest of operand is ignored */
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
    if (alt_numeric && (*base = intel_suffix(s)))
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
    *base = 10;
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
  if (ISIDSTART(*p) || isdigit((unsigned char)*p)) {  /* may start with digit */
    p++;
    while (ISIDCHAR(*p))
      p++;
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

  if (p!=NULL && *p==':' && ISIDSTART(*s) && *s!=local_char && *(p-1)!='$') {
    /* skip local part of global.local label */
    s = p + 1;
    if (p = skip_local(s)) {
      name = make_local_label(n,*start,(s-1)-*start,s,*(p-1)=='$'?(p-1)-s:p-s);
      *start = skip(p);
    }
    else
      return NULL;
  }
  else if (p!=NULL && p>(s+1) && *s==local_char) {  /* .label */
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

/*
 *	Reserve Symbol Directives
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

  /* get current offset symbol expression, then increment or decrement it */
  sym = internal_abs(symname);

  if (!ISEOL(*s)) {
    /* Make a new expression out of the parsed expression multiplied by size
       and add to or subtract it from the current symbol's expression.
       Perform even alignment when requested. */
    new = make_expr(MUL,parse_expr_tmplab(s),number_expr(size));
    simplify_expr(new);

    if (align_data && size>1) {
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

  simplify_expr(new);
  sym->expr = new;
  return equsym;
}

/* assign value of current struct- or frame-offset symbol to an abs-symbol,
   determine operation size from directive extension first */
static symbol *new_setoffset(char *equname,char **s,char *symname,int dir)
{
  taddr size = 1;
  char *start = *s;
  char ext;

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
 *	Declare Constant Directives
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
        if (!align_data)
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
 *	Define Storage Directives
 */
static atom *do_space(int size,expr *cnt,expr *fill)
{
  atom *a;

  a = new_space_atom(cnt,size>>3,fill);
  a->align = align_data ? DATA_ALIGN(size) : 1;
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
 *	Declare Constant Block Directives
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
 *	Program Control Directives
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
 *	Padding and Alignment Directives
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
 *	Include File Directives
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
 *	Conditional Directives
 */

static void ifdef(char *s,int b)
{
  char *name;
  symbol *sym;
  int result;

  if (!(name = parse_symbol(&s))) {
    syntax_error(10);  /* identifier expected */
    return;
  }
  if (sym = find_symbol(name))
    result = sym->type != IMPORT;
  else
    result = 0;
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

static void ifmacro(char *s,int b)
{
  char *name = s;
  int result;

  if (s = skip_identifier(s)) {
    result = find_macro(name,s-name) != NULL;
    cond_if(result == b);
  }
  else
    syntax_error(10);  /*identifier expected */
}

static void handle_ifmacrod(char *s)
{
  ifmacro(s,1);
}

static void handle_ifmacrond(char *s)
{
  ifmacro(s,0);
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
    general_error(30);  /* expression must be constant */
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

/*
 *	Multiline Comment Block Directives
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
 *	Struct Directives
 */
static void handle_struct(char *s)
{
  strbuf *name;

  if (name = parse_identifier(0,&s)) {
    s = skip(s);
    eol(s);
    if (new_structure(name->str))
      current_section->flags |= LABELS_ARE_LOCAL;
  }
  else
    syntax_error(10);  /* identifier expected */
}

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
 *	Inlining Directives
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
}

/*
 *	Repetition Directives
 */
static void handle_rept(char *s)
{
  int cnt = (int)parse_constexpr(&s);

  new_repeat(cnt<0?0:cnt,NULL,NULL,rept_dirlist,endr_dirlist);
}

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

static void handle_endr(char *s)
{
  syntax_error(12,"endr","rept");  /* unexpected endr without rept */
}

/*
 *	Macro Directives
 */
static void handle_endm(char *s)
{
  syntax_error(12,"endm","macro");  /* unexpected endm without macro */
}

static void handle_mexit(char *s)
{
  leave_macro();
}

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

/*
 *	Section Directives
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
    if (!stricmp(name,"code") || !stricmp(name,"text"))
      attr = code_type;
    else if (!strcmp(name,"data"))
      attr = data_type;
    else if (!strcmp(name,"bss"))
      attr = bss_type;
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
 *	Linker-Related Directives
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

static void handle_local(char *s)
{
  do_bind(s,LOCAL);
}

static void handle_weak(char *s)
{
  do_bind(s,WEAK);
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

/*
 *	Miscellaneous Directives
 */
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
    
	case 0:	/* message */
	  syntax_error(16,txt->str);  
	  break;

    case 1:	/* warning */
	  syntax_error(17,txt->str);
	  break;

    case 2:	/* error */
	  syntax_error(18,txt->str);
	  break;

    case 3:	/* fatal error */
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

struct {
  const char *name;
  void (*func)(char *);
} directives[] = {
  "rsset",handle_rsset,	
  "rsreset",handle_rsreset,
  "rseven",handle_rseven,

#if defined(VASM_CPU_M68K)
  "rs",handle_rs16,
  "rs.b",handle_rs8,
  "rs.w",handle_rs16,
  "rs.l",handle_rs32,

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
#else
  "rb",handle_rs8,
  "rw",handle_rs16,
  "rl",handle_rs32,

  "db",handle_d8,
  "dw",handle_d16,
  "dl",handle_d32,

  "dcb",handle_blk8,
  "dcw",handle_blk16,
  "dcl",handle_blk32,

  "ds",handle_spc8,
#endif

  "org",handle_org,
  "obj",handle_obj,
  "objend",handle_objend,
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

  "ifdef",handle_ifd,
  "ifnodef",handle_ifnd,
  "ifmac",handle_ifmacrod,
  "ifnomac",handle_ifmacrond,

  "ifstr",handle_ifnb,
  "ifnostr",handle_ifb,
  "ifstreq",handle_ifc,
  "ifstrne",handle_ifnc,  

  "ifeq",handle_ifeq,
  "ifne",handle_ifne,
  "ifgt",handle_ifgt,
  "ifge",handle_ifge,
  "iflt",handle_iflt,
  "ifle",handle_ifle,

  "comment",handle_comment,
  "comend",handle_comend,

  "struct",handle_struct,
  "strend",handle_endstruct,

  "module",handle_module,
  "modend",handle_endmodule,

  "rept",handle_rept,
  "irp",handle_irp,
  "irpc",handle_irpc,
  "endr",handle_endr,

  "endm",handle_endm,
  "mexit",handle_mexit,
  "purge",handle_purge,
  
  "section",handle_section,
  "pushs",handle_pushsect,
  "pops",handle_popsect,

  "local",handle_local,
  "weak",handle_weak,
  "global",handle_global,
  "xref",handle_xref,
  "xdef",handle_xdef,

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

  return !strnicmp(s,name,len) &&
         ((isspace((unsigned char)*d) || ISEOL(d)) ||
          (*d=='.' && (isspace((unsigned char)*(d+2))||ISEOL(d+2))));
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
  char *s,*line,*inst,*labname;
  char *ext[MAX_QUALIFIERS?MAX_QUALIFIERS:1];
  char *op[MAX_OPERANDS];
  int ext_len[MAX_QUALIFIERS?MAX_QUALIFIERS:1];
  int op_len[MAX_OPERANDS];
  int ext_cnt,op_cnt,inst_len;
  instruction *ip;

  while (line = read_next_line()) {
	if (parse_end)
      continue;

    s = line;
    if (!cond_state()) {
      /* skip source until ELSE or ENDIF */
      int idx;

      (void)parse_label_or_pc(&s);
      idx = check_directive(&s);
      if (idx >= 0) {
        if (!strncmp(directives[idx].name,"if",2))
          cond_skipif();
        else if (directives[idx].func == handle_else)
          cond_else();
        else if (directives[idx].func == handle_endif)
          cond_endif();
        else if (directives[idx].func == handle_elseif) {
          s = skip(s);
          cond_elseif(eval_ifexp(&s,1));
        }
      }
      continue;
    }

    if (labname = parse_label_or_pc(&s)) {
      /* we have found a global or local label, or current-pc character */
      symbol *label;

      s = skip(s);

      s = handle_iif(s);

      if (!strnicmp(s,"equ",3) && isspace((unsigned char)*(s+3))) {
        s = skip(s+3);
        label = new_equate(labname,parse_expr_tmplab(&s));
      }
	  else if (!strnicmp(s,"set",3) && isspace((unsigned char)*(s+3))) {
        /* set allows redefinitions */
        s = skip(s+3);
        label = new_abs(labname,parse_expr_tmplab(&s));
      }
	  else if (*s=='=') {
        s++;
		if (*s=='=') {
			/* '==' is shorthand for equ */
			s++;
			s = skip(s);
			label = new_equate(labname,parse_expr_tmplab(&s));
		} 
		else {
			/* '=' is shorthand for set */
			s = skip(s);
        	label = new_abs(labname,parse_expr_tmplab(&s));
		}
	  }
      else if (offs_directive(s,"rs")) {
        label = new_setoffset(labname,&s,rs_name,1);
      }
      else if (!strnicmp(s,"macro",5) &&
               (isspace((unsigned char)*(s+5)) || *(s+5)=='\0'
                || *(s+5)==commentchar)) {
        char *params = skip(s+5);
        strbuf *buf;

        s = line;
        if (!(buf = parse_identifier(0,&s)))
          ierror(0);
        new_macro(buf->str,macro_dirlist,endm_dirlist,params);
        continue;
      }
	  else if (!strnicmp(s,"struct",6) &&
               (isspace((unsigned char)*(s+6)) || *(s+6)=='\0'
                || *(s+6)==commentchar)) {
        strbuf *buf;

        s = line;
        if (!(buf = parse_identifier(0,&s)))
          ierror(0);
        if (new_structure(buf->str))
          current_section->flags |= LABELS_ARE_LOCAL;
        continue;
      }
#ifdef PARSE_CPU_LABEL
      else if (!PARSE_CPU_LABEL(labname,&s)) {
#else
      else {
#endif
        /* it's just a label */
        label = new_labsym(0,labname);
        add_atom(0,new_label_atom(label));
      }
    }

    /* check for directives */
	s = skip(s);
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
    while (*s && !isspace((unsigned char)*s))
      s++;
    inst_len = s - inst;
#else
    s = parse_instruction(s,&inst_len,ext,ext_len,&ext_cnt);
#endif
    if (!isspace((unsigned char)*s) && *s!='\0')
      syntax_error(2);  /* no space before operands */
    s = skip(s);

    if (execute_macro(inst,inst_len,ext,ext_len,ext_cnt,s))
      continue;
    if (execute_struct(inst,inst_len,s))
      continue;

    /* read operands, terminated by comma or blank (unless in parentheses) */
    op_cnt = 0;
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
      
      if (allow_spaces) {
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
      if (allow_spaces && ip->op[0]==NULL && op_cnt!=0)
        syntax_error(6);  /* mnemonic without operands has tokens in op.field */
#endif
      add_atom(0,new_inst_atom(ip));
    }
  }

  cond_check();  /* check for open conditional blocks */
}


/* parse next macro argument */
char *parse_macro_arg(struct macro *m,char *s,
                      struct namelen *param,struct namelen *arg)
{
  arg->len = 0;  /* cannot select specific named arguments */
  param->name = s;
  s = skip_operand(s);
  param->len = s - param->name;
  return s;
}


/* count the number of macro args that were passed this call */
int count_passed_macargs(source *src)
{
  int i, n = 0;

  for (i = 0; i < maxmacparams; i++) {
    if (src->param_len[i] > 0) n++;
  }

  return n;
}


/* write 0 to buffer when macro argument is missing or empty, 1 otherwise */
static int macro_arg_defined(source *src,char *argstart,char *argend,char *d,int type)
{
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
  int nc = 0;
  int n;
  char *s = *line;
  char *end;

  if (*s++ == '\\') {
    /* possible macro expansion detected */

    if (*s == '\\') {
      if (dlen >= 1) {
        *d++ = *s++;
        if (esc_sequences) {
          if (dlen >= 2) {
            *d++ = '\\';  /* make it a double \ again */
            nc = 2;
          }
          else nc = -1;
        }
        else nc = 1;
      }
      else nc = -1;
    }

    else if (*s == '@') {
      /* \@: insert a unique id */
      if (dlen > 7) {
        nc = sprintf(d,"_%06lu",src->id);
        s++;
      }
      else nc = -1;
    }
    else if (*s == '#') {
      /* \# : insert number of parameters */
      if (dlen > 3) {
        nc = sprintf(d,"%d",count_passed_macargs(src));
        s++;
      }
      else nc = -1;
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
        nc = copy_macro_param(src,*s-'1',d,dlen);
      s++;
    }
    else if ((end = skip_identifier(s)) != NULL) {
      if ((n = find_macarg_name(src,s,end-s)) >= 0) {
        /* \argname: insert named macro parameter n */
        nc = copy_macro_param(src,n,d,dlen);
        s = end;
      }
    }

    if (nc >= dlen)
      nc = -1;
    else if (nc >= 0)
      *line = s;  /* update line pointer when expansion took place */
  }

  return nc;  /* number of chars written to line buffer, -1: out of space */
}


int init_syntax()
{
  size_t i;
  hashdata data;

  dirhash = new_hashtable(0x1000);
  for (i=0; i<dir_cnt; i++) {
    data.idx = i;
    add_hashentry(dirhash,directives[i].name,data);
  }
  if (debug && dirhash->collisions)
    fprintf(stderr,"*** %d directive collisions!!\n",dirhash->collisions);

  cond_init();
  set_internal_abs(REPTNSYM,-1); /* reserve the REPTN symbol */
  internal_abs(rs_name);
  current_pc_char = '*';
  current_pc_str[0] = current_pc_char;
  current_pc_str[1] = 0;
  esc_sequences = 1;

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
  if (!strcmp(p,"-align"))
    align_data = 1;
  else if (!strcmp(p,"-spaces"))
    allow_spaces = 1;
  else if (!strcmp(p,"-altnum"))
    alt_numeric = 1;
  else if (!strcmp(p,"-altlocal"))
    local_char = '@';
  else
    return 0;

  return 1;
}
