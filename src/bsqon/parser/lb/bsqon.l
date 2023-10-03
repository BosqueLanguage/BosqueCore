%option noyywrap nodefault nounput noinput yylineno

%{
#include "bsqon.tab.h"

#include "bytestring.h"

#define MAX_STR_CONST 4096

int yycolumn = 1;

uint8_t string_buf[MAX_STR_CONST];
struct ByteString string_buf_bs = { string_buf, 0 };

/* Forward declarations */
void ByteStringStoreChar(char c);
void ByteStringStoreText(const char* c, size_t len);

void yyerror(const char* s, ...);

/* This is executed before every action. */
#define YY_USER_ACTION                                                   \
  start_line = prev_yylineno; start_column = yycolumn;                   \
  if (yylineno == prev_yylineno) yycolumn += yyleng;                     \
  else {                                                                 \
    for (yycolumn = 1; yytext[yyleng - yycolumn] != '\n'; ++yycolumn) {} \
    prev_yylineno = yylineno;                                            \
  }                                                                      \
  yylloc.first_line = start_line; yylloc.first_column = start_column;      \
  yylloc.last_line = yylineno; yylloc.last_column = yycolumn;              

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

(0|[+-]?{NON_ZERO_INTEGRAL})R                        { yylval.str = yytext; return TOKEN_RATIONAL; }
((0|[+-]?{NON_ZERO_INTEGRAL})\/{NON_ZERO_INTEGRAL})R { yylval.str = yytext; return TOKEN_RATIONAL; }

[-]0[niNIR]                                      { yyerror("Zero cannot be negative"); return YYerror; }
[-]{NON_ZERO_INTEGRAL}[nN]                       { yyerror("Cannot have negative natural number"); return YYerror; }
[+]?0+{NON_ZERO_INTEGRAL}[nN]                    { yyerror("Leading zero is not allowed"); return YYerror; }
[+-]?0+{NON_ZERO_INTEGRAL}[iIR]                  { yyerror("Leading zero is not allowed"); return YYerror; }
[+-]?0+{NON_ZERO_INTEGRAL}\/{NON_ZERO_INTEGRAL}R { yyerror("Leading zero is not allowed"); return YYerror; }
[+]?00+[nN]                                      { yyerror("Leading zero is not allowed"); return YYerror; }
[+-]?00+[iIR]                                    { yyerror("Leading zero is not allowed"); return YYerror; }
((0|[+-]?{NON_ZERO_INTEGRAL})\/0)R               { yyerror("Zero as divisor"); return YYerror; }

[+-]?"0."[0-9]+{EXP}?f                   { yylval.str = yytext; return TOKEN_FLOAT; }
[+-]?{NON_ZERO_INTEGRAL}"."[0-9]+{EXP}?f { yylval.str = yytext; return TOKEN_FLOAT; }

[+-]?"0."[0-9]+{EXP}?d                   { yylval.str = yytext; return TOKEN_DOUBLE; }
[+-]?{NON_ZERO_INTEGRAL}"."[0-9]+{EXP}?d { yylval.str = yytext; return TOKEN_DOUBLE; }

[+-]?0+"0."[0-9]+{EXP}?[fd]                   { yyerror("Redundant leading zero is not allowed"); return YYerror; }
[+-]?0+{NON_ZERO_INTEGRAL}"."[0-9]+{EXP}?[fd] { yyerror("Leading zero is not allowed"); return YYerror; }
[+-]?"."[0-9]+{EXP}?[fd]                      { yyerror("Leading decimal is not allowed"); return YYerror; }

 /* numberinos */
0|[+-]?{NON_ZERO_INTEGRAL} { yylval.str = yytext; return TOKEN_INT_NUMBERINO; }

[-]0                       { yyerror("Zero cannot be negative"); return YYerror; }
[+-]?0+{NON_ZERO_INTEGRAL} { yyerror("Leading zero is not allowed"); return YYerror; }
[+]?00+                    { yyerror("Leading zero is not allowed"); return YYerror; }

[+-]?"."[0-9]+{EXP}?                    { yylval.str = yytext; return TOKEN_FLOAT_NUMBERINO; }
[+-]?"0."[0-9]+{EXP}?                   { yylval.str = yytext; return TOKEN_FLOAT_NUMBERINO; }
[+-]?{NON_ZERO_INTEGRAL}"."[0-9]+{EXP}? { yylval.str = yytext; return TOKEN_FLOAT_NUMBERINO; }

[+-]?0+"0."[0-9]+{EXP}?                   { yyerror("Redundant leading zero is not allowed"); return YYerror; }
[+-]?0+{NON_ZERO_INTEGRAL}"."[0-9]+{EXP}? { yyerror("Leading zero is not allowed"); return YYerror; }

 /* strings */

0x"["[A-Z0-9]*"]"       { yylval.str = yytext; return TOKEN_BYTE_BUFFER; }
uuid4"{"{UUID}"}"       { yylval.str = yytext; return TOKEN_UUID_V4; }
uuid7"{"{UUID}"}"       { yylval.str = yytext; return TOKEN_UUID_V7; }
sha3"{"[a-z0-9]{128}"}" { yylval.str = yytext; return TOKEN_SHA_HASH; }

<INITIAL>{
\"       { BEGIN(STRING); string_buf_bs.len = 0; ByteStringStoreChar('"'); }
}
<STRING>{
\"       { BEGIN(INITIAL); ByteStringStoreChar('"'); yylval.bstr = &string_buf_bs; return TOKEN_STRING; }
<<EOF>>  { BEGIN(INITIAL); yyerror("Unclosed String"); return YYEOF; }
\\\\     { ByteStringStoreText(yytext, yyleng); } /* JSON Strings */
\\\"     { ByteStringStoreText(yytext, yyleng); } /* JSON Strings */
[^"]     { ByteStringStoreChar(yytext[0]); }
}

<INITIAL>{
ascii\{\" { BEGIN(ASCII_STRING); string_buf_bs.len = 0; ByteStringStoreText(yytext, yyleng); }
}
<ASCII_STRING>{
\"\}      { BEGIN(INITIAL); ByteStringStoreText(yytext, yyleng); yylval.bstr = &string_buf_bs; return TOKEN_ASCII_STRING; }
<<EOF>>   { BEGIN(INITIAL); yyerror("Unclosed ASCIIString"); return YYEOF; }
.|\n      { ByteStringStoreChar(yytext[0]); }
}

<INITIAL>{
regex\{\" { BEGIN(REGEX); string_buf_bs.len = 0; ByteStringStoreText(yytext, yyleng); }
}
<REGEX>{
\"\}      { BEGIN(INITIAL); ByteStringStoreText(yytext, yyleng); yylval.bstr = &string_buf_bs; return TOKEN_REGEX; }
<<EOF>>   { BEGIN(INITIAL); yyerror("Unclosed Regex"); return YYEOF; }
\\\\      { ByteStringStoreText(yytext, yyleng); } /* JSON Strings */
\\\"      { ByteStringStoreText(yytext, yyleng); } /* JSON Strings */
\n        { yyerror("Newline in Path Item"); return YYerror; }
.         { ByteStringStoreChar(yytext[0]); }
}

<INITIAL>{
(path|fragment|glob)\{\" { BEGIN(REGEX); string_buf_bs.len = 0; ByteStringStoreText(yytext, yyleng); }
}
<PATH_ITEM>{
\"\}      { BEGIN(INITIAL); ByteStringStoreText(yytext, yyleng); yylval.bstr = &string_buf_bs; return TOKEN_PATH_ITEM; }
<<EOF>>   { BEGIN(INITIAL); yyerror("Unclosed Path Item"); return YYEOF; }
\n        { yyerror("Newline in Path Item"); return YYerror; }
.         { ByteStringStoreChar(yytext[0]); }
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
#{IDENTIFIER} { yylval.str = yytext; return TOKEN_REF; }
_"$"{IDENTIFIER} { yylval.str = yytext; return TOKEN_UNSPEC_IDENTIFIER; }

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

void ByteStringStoreChar(char c)
{
    if (string_buf_bs.len == MAX_STR_CONST) {
        yyerror("String constant too long");
        string_buf_bs.len++;
    }

    if(string_buf_bs.len < MAX_STR_CONST) {
        string_buf[string_buf_bs.len++] = (uint8_t)c;
    }
}

void ByteStringStoreText(const char* c, size_t len)
{
    if (string_buf_bs.len < MAX_STR_CONST && MAX_STR_CONST <= string_buf_bs.len + len) {
        yyerror("String constant too long");
        string_buf_bs.len += len;
    }

    if(MAX_STR_CONST <= string_buf_bs.len + len) {
        for(size_t i = 0; i < len; i++) {
            string_buf[string_buf_bs.len++] = (uint8_t)c[i];
        }
    }
}