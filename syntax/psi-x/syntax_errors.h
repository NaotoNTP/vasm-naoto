  "syntax error",ERROR,																															/* 0 */
  "invalid extension",ERROR,																												/* 1 */
  "no space before operands",WARNING,																								/* 2 */
  "too many closing parentheses",WARNING,																						/* 3 */
  "missing closing parentheses",WARNING,																						/* 4 */
  "missing operand",ERROR,																													/* 5 */
  "garbage at end of line",WARNING,																									/* 6 */
  "unexpected use of \"%s\" outside of macro",ERROR,																/* 7 */
  "invalid data operand",ERROR,																											/* 8 */
  "invalid radix base value (%d)",ERROR,																						/* 9 */
  "identifier expected",ERROR,																											/* 10 */
  "assembly failed",FATAL|ERROR,																										/* 11 */
  "unexpected \"%s\" without \"%s\"",ERROR,																					/* 12 */
  "\",\" expected",WARNING,																													/* 13 */
  "maximum module nesting depth exceeded (%d)",ERROR,																/* 14 */
  "invalid message severity",ERROR,																									/* 15 */

  "\nuser-defined message: %s",NOLINE|MESSAGE,																			/* 16 */
  "\nuser-defined warning: %s",NOLINE|WARNING,																			/* 17 */
  "\nuser-defined error: %s",NOLINE|ERROR,																					/* 18 */
  "\nuser-defined fatal error: %s",NOLINE|FATAL|ERROR,															/* 19 */

  "skipping instruction in struct init",WARNING,																		/* 20 */
  "last %d bytes of string constant have been cut",WARNING,													/* 21 */
  "invalid numeric expansion",ERROR,																								/* 22 */
  "enclosed macro argument missing \"}\"",ERROR,																		/* 23 */

  "invalid \"public\" parameter (must be either \"on\" or \"off\")",ERROR,					/* 24 */
  "invalid data size value (%d bytes)",ERROR,																				/* 25 */
  "local macro variable <%s> already declared",WARNING,															/* 26 */
	"string symbol <%s> not found",ERROR,																							/* 27 */
	"quoted string or string symbol expected",ERROR,																	/* 28 */
	"substring index out of range",WARNING,																						/* 29 */
	"substring starting index is greater than the ending index",WARNING,							/* 30 */
	"substring index is greater than the length of the string",WARNING,								/* 31 */
	"string stack capacity reached (%d)",ERROR,																				/* 32 */
	"string stack is empty",ERROR,																										/* 33 */

	"invalid option argument \"%c\"",ERROR,																						/* 34 */
	"unrecognized option given",WARNING,																							/* 35 */
	"options stack capacity reached (%d)",ERROR,																			/* 36 */
	"options stack is empty",ERROR,																										/* 37 */

  "too many arguments specified (maximum of %d allowed)",ERROR,                     /* 38 */
  "functions must accept at least 1 argument",ERROR,			                          /* 39 */
  "function definitions must be enclosed with curly braces (missing \"%c\")",ERROR,	/* 40 */
  "unexpected end of line",ERROR,                                                   /* 41 */
  "function call is missing arguments (expected %d, got %d)",ERROR,                 /* 42 */
  "error in function call",ERROR,          																					/* 43 */
  "duplicate argument name in function declaration \"%s\"",ERROR,          					/* 44 */
  "file path must be in quotes",ERROR,			                          							/* 45 */
  "start index is greater than the length of the string",ERROR,        							/* 46 */
  "expression must evaluate",ERROR,                                                 /* 47 */
  