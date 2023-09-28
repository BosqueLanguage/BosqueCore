%option noyywrap nodefault nounput noinput yylineno
%{
#include "bsqon.tab.h"

#define MAX_STR_CONST 4096

int yycolumn = 1;

char string_buf[MAX_STR_CONST];
char* string_buf_ptr;

/* Forward declarations */
void yyerror(char* s, ...);

/* This is executed before every action. */
#define YY_USER_ACTION                                                   \
  start_line = prev_yylineno; start_column = yycolumn;                   \
  if (yylineno == prev_yylineno) yycolumn += yyleng;                     \
  else {                                                                 \
    for (yycolumn = 1; yytext[yyleng - yycolumn] != '\n'; ++yycolumn) {} \
    prev_yylineno = yylineno;                                            \
  }

%}

%x COMMENT
%x STRING
%x ASCII_STRING
%x REGEX
%x PATH_ITEM

NON_ZERO_INTEGRAL ([1-9][0-9]*)
EXP	([Ee][-+]?[0-9]+)

DATE ([0-9]{4})-([0-9]{2})-([0-9]{2})
TIME ([0-9]{2}):([0-9]{2}):([0-9]{2})
TZNAME ([a-zA-Z0-9/ _-]+)

UUID ([a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12})

IDENTIFIER ([a-z][a-zA-Z0-9_]*|[_][a-zA-Z0-9_]+)

%%

  int start_line, start_column;
  int prev_yylineno = yylineno;

 /* standard parens */
"(" |
")" |
"{" |
"}" |
"[" |
"]" | 
"<" |
">"         { return yytext[0]; }

 /* symbols */
"..."       { return SYM_ELLIPSIS; }

"::"        { return SYM_DOUBLE_COLON; }
"=>"        { return SYM_ENTRY; }

":"         { return SYM_COLON; }
","         { return SYM_COMMA; }
"&"         { return SYM_AMP; }
"|"         { return SYM_BAR; }
"!"         { return SYM_BANG; }
"="         { return SYM_EQUALS; }
"."         { return SYM_DOT; }
"@"         { return SYM_AT; }
"_"         { return SYM_UNDERSCORE; }

 /* keywords */
"something" { return KW_SOMETHING; }

"nothing"   { return KW_NOTHING; }

"false"     { return KW_FALSE; }

"$src"      { return KW_SRC; }
"none"      { return KW_NONE; }
"null"      { return KW_NULL; }
"some"      { return KW_SOME; }
"true"      { return KW_TRUE; } 

"err"       { return KW_ERR; }
"let"       { return KW_LET; }

"in"        { return KW_IN; }
"ok"        { return KW_OK; }

 /* numbers */
(0|[+]?{NON_ZERO_INTEGRAL})n   { yylval.str = yytext; return TOKEN_NAT; }
(0|[+-]?{NON_ZERO_INTEGRAL})i  { yylval.str = yytext; return TOKEN_INT; }
(0|[+]?{NON_ZERO_INTEGRAL})N   { yylval.str = yytext; return TOKEN_BIG_NAT; }
(0|[+-]?{NON_ZERO_INTEGRAL})I  { yylval.str = yytext; return TOKEN_BIG_INT; }

(0|[+-]?{NON_ZERO_INTEGRAL})R |
((0|[+-]?{NON_ZERO_INTEGRAL})\/{NON_ZERO_INTEGRAL})R { yylval.str = yytext; return TOKEN_RATIONAL; }

[+-]?"0."[0-9]+{EXP}?f |
[+-]?{NON_ZERO_INTEGRAL}"."[0-9]+{EXP}?f { yylval.str = yytext; return TOKEN_FLOAT; }

[+-]?"0."[0-9]+{EXP}?d |
[+-]?{NON_ZERO_INTEGRAL}"."[0-9]+{EXP}?d { yylval.str = yytext; return TOKEN_DOUBLE; }

 /* numberinos */
0|[+-]?{NON_ZERO_INTEGRAL} { yylval.str = yytext; return TOKEN_INT_NUMBERINO; }

[+-]?"."[0-9]+{EXP}? |
[+-]?"0."[0-9]+{EXP}? |
[+-]?{NON_ZERO_INTEGRAL}"."[0-9]+{EXP}? { yylval.str = yytext; return TOKEN_FLOAT_NUMBERINO; }

 /* strings */

0x"["[A-Z0-9]*"]"       { yylval.str = yytext; return TOKEN_BYTE_BUFFER; }
uuid4"{"{UUID}"}"       { yylval.str = yytext; return TOKEN_UUID_V4; }
uuid7"{"{UUID}"}"       { yylval.str = yytext; return TOKEN_UUID_V7; }
sha3"{"[a-z0-9]{128}"}" { yylval.str = yytext; return TOKEN_SHA_HASH; }

<INITIAL>{
\"       { BEGIN(STRING); string_buf_ptr = string_buf; }
}
<STRING>{
\"       { BEGIN(INITIAL); *string_buf_ptr = '\0'; yylval.str = string_buf; return TOKEN_STRING; }
<<EOF>>  { BEGIN(INITIAL); yyerror("Unclosed String"); return YYEOF; }
\\\\     { *string_buf_ptr++ = yytext[0]; *string_buf_ptr++ = yytext[1]; } /* JSON Strings */
\\\"     { *string_buf_ptr++ = yytext[0]; *string_buf_ptr++ = yytext[1]; } /* JSON Strings */
[^"]     { *string_buf_ptr++ = yytext[0]; }
}

<INITIAL>{
ascii\{\" { BEGIN(ASCII_STRING); }
}
<ASCII_STRING>{
\"\}      { BEGIN(INITIAL); *string_buf_ptr = '\0'; yylval.str = string_buf; return TOKEN_ASCII_STRING; }
<<EOF>>   { BEGIN(INITIAL); yyerror("Unclosed ASCIIString"); return YYEOF; }
.|\n      { *string_buf_ptr++ = yytext[0]; }
}

<INITIAL>{
regex\{\" { BEGIN(REGEX); }
}
<REGEX>{
\"\}      { BEGIN(INITIAL); *string_buf_ptr = '\0'; yylval.str = string_buf; return TOKEN_REGEX; }
<<EOF>>   { BEGIN(INITIAL); yyerror("Unclosed Regex"); return YYEOF; }
\\\\      { *string_buf_ptr++ = yytext[0]; *string_buf_ptr++ = yytext[1]; } /* JSON Strings */
\\\"      { *string_buf_ptr++ = yytext[0]; *string_buf_ptr++ = yytext[1]; } /* JSON Strings */
\n        { yyerror("Newline in Path Item"); return YYerror; }
.         { *string_buf_ptr++ = yytext[0]; }
}

<INITIAL>{
(path|fragment|glob)\{\" { BEGIN(REGEX); }
}
<PATH_ITEM>{
\"\}      { BEGIN(INITIAL); *string_buf_ptr = '\0'; yylval.str = string_buf; return TOKEN_PATH_ITEM; }
<<EOF>>   { BEGIN(INITIAL); yyerror("Unclosed Path Item"); return YYEOF; }
\n        { yyerror("Newline in Path Item"); return YYerror; }
.         { *string_buf_ptr++ = yytext[0]; }
}

 /* dates */
{DATE}T{TIME}{TZNAME} { yylval.str = yytext; return TOKEN_DATE_TIME; }
{DATE}T{TIME}         { yylval.str = yytext; return TOKEN_UTC_DATE_TIME; }
{DATE}                { yylval.str = yytext; return TOKEN_PLAIN_DATE; }
{TIME}                { yylval.str = yytext; return TOKEN_PLAIN_TIME; }

(0|{NON_ZERO_INTEGRAL})t { yylval.str = yytext; return TOKEN_TICK_TIME; }
(0|{NON_ZERO_INTEGRAL})l { yylval.str = yytext; return TOKEN_LOGICAL_TIME; }

{DATE}T{TIME}("."[0-9]{3})Z { yylval.str = yytext; return TOKEN_TIMESTAMP; }

 /* names */
{IDENTIFIER}    { yylval.str = yytext; return TOKEN_IDENTIFIER; }
[#]{IDENTIFIER} { yylval.str = yytext; return TOKEN_REF; }

[A-Z]([a-zA-Z0-9_])+(::[A-Z]([a-zA-Z0-9_])+)* { yylval.str = yytext; return TOKEN_TYPE_COMPONENT; }

 /* comments */
<INITIAL>{
"/*"      { BEGIN(COMMENT); }
}
<COMMENT>{
"*/"      { BEGIN(INITIAL); }
<<EOF>> { BEGIN(INITIAL); yyerror("Unclosed Multiline Comment"); return 0; }
[^*\n]+   /* eat comment in chunks */
"*"       /* eat the lone star */
\n        /* eat the newline -- yylineno should be incremented automatically? */
}

"//".*    /* line comment */

[ \t\n]   /* ignore white space */ 

.	{ return yytext[0]; } /* catch all and error in parser */

%%

