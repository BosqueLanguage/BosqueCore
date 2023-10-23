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

size_t isSpecialTypedLiteralIdConflict(const char* txt);

void yyerror(const char* s, ...);

/* This is executed before every action. */
#define YY_USER_ACTION                                                   \
  start_line = prev_yylineno; start_column = yycolumn;                   \
  if (yylineno == prev_yylineno) yycolumn += yyleng;                     \
  else {                                                                 \
    for (yycolumn = 1; yytext[yyleng - yycolumn] != '\n'; ++yycolumn) {} \
    prev_yylineno = yylineno;                                            \
  }                                                                      \
  yylloc.first_line = start_line; yylloc.first_column = start_column;    \
  yylloc.last_line = yylineno; yylloc.last_column = yycolumn;              

%}

%x STRING
%x ASCII_STRING
%x REGEX
%x PATH_ITEM

NON_ZERO_INTEGRAL ([1-9][0-9]*)
EXP	([Ee][-+]?[0-9]+)

DATE ([0-9]{4})-([0-9]{2})-([0-9]{2})
TIME ([0-9]{2}):([0-9]{2}):([0-9]{2})
TZNAME ((\{[a-zA-Z0-9/, _-]+\})|[A-Z]+)

UUID ([a-fA-F0-9]{8}-[a-fA-F0-9]{4}-[a-fA-F0-9]{4}-[a-fA-F0-9]{4}-[a-fA-F0-9]{12})

IDENTIFIER ([_]?[a-z][a-zA-Z0-9_]*)
TYPE_IDENTIFIER ([A-Z][a-zA-Z0-9_]*)

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
"some"      { return KW_SOME; }
"true"      { return KW_TRUE; } 

"err"       { return KW_ERR; }
"let"       { return KW_LET; }

"in"        { return KW_IN; }
"ok"        { return KW_OK; }

 /* numbers */
(0|[+]?{NON_ZERO_INTEGRAL})n   { yylval.str = AST_STRDUP(yytext); return TOKEN_NAT; }
(0|[+-]?{NON_ZERO_INTEGRAL})i  { yylval.str = AST_STRDUP(yytext); return TOKEN_INT; }
(0|[+]?{NON_ZERO_INTEGRAL})N   { yylval.str = AST_STRDUP(yytext); return TOKEN_BIG_NAT; }
(0|[+-]?{NON_ZERO_INTEGRAL})I  { yylval.str = AST_STRDUP(yytext); return TOKEN_BIG_INT; }

(0|[+-]?{NON_ZERO_INTEGRAL})R                        { yylval.str = AST_STRDUP(yytext); return TOKEN_RATIONAL; }
((0|[+-]?{NON_ZERO_INTEGRAL})\/{NON_ZERO_INTEGRAL})R { yylval.str = AST_STRDUP(yytext); return TOKEN_RATIONAL; }

[-]0[niNIR]                                      { yyerror("Zero cannot be negative"); return YYerror; }
[-]{NON_ZERO_INTEGRAL}[nN]                       { yyerror("Cannot have negative natural number"); return YYerror; }
[+]?0+{NON_ZERO_INTEGRAL}[nN]                    { yyerror("Leading zero is not allowed"); return YYerror; }
[+-]?0+{NON_ZERO_INTEGRAL}[iIR]                  { yyerror("Leading zero is not allowed"); return YYerror; }
[+-]?0+{NON_ZERO_INTEGRAL}\/{NON_ZERO_INTEGRAL}R { yyerror("Leading zero is not allowed"); return YYerror; }
[+]?00+[nN]                                      { yyerror("Leading zero is not allowed"); return YYerror; }
[+-]?00+[iIR]                                    { yyerror("Leading zero is not allowed"); return YYerror; }
((0|[+-]?{NON_ZERO_INTEGRAL})\/0)R               { yyerror("Zero as divisor"); return YYerror; }

[+-]?"0."[0-9]+{EXP}?f                   { yylval.str = AST_STRDUP(yytext); return TOKEN_FLOAT; }
[+-]?{NON_ZERO_INTEGRAL}"."[0-9]+{EXP}?f { yylval.str = AST_STRDUP(yytext); return TOKEN_FLOAT; }

[+-]?"0."[0-9]+{EXP}?d                   { yylval.str = AST_STRDUP(yytext); return TOKEN_DOUBLE; }
[+-]?{NON_ZERO_INTEGRAL}"."[0-9]+{EXP}?d { yylval.str = AST_STRDUP(yytext); return TOKEN_DOUBLE; }

[+-]?0+"0."[0-9]+{EXP}?[fd]                   { yyerror("Redundant leading zero is not allowed"); return YYerror; }
[+-]?0+{NON_ZERO_INTEGRAL}"."[0-9]+{EXP}?[fd] { yyerror("Leading zero is not allowed"); return YYerror; }
[+-]?"."[0-9]+{EXP}?[fd]                      { yyerror("Leading decimal is not allowed"); return YYerror; }

 /* numberinos */
0|{NON_ZERO_INTEGRAL}       { yylval.str = AST_STRDUP(yytext); return TOKEN_NUMBERINO; }

[+-](0|{NON_ZERO_INTEGRAL}) { yyerror("Cannot have sign on indexer"); return YYerror; }
0+{NON_ZERO_INTEGRAL}       { yyerror("Leading zero is not allowed"); return YYerror; }
00+                         { yyerror("Leading zero is not allowed"); return YYerror; }

 /* strings */

0x"["[a-fA-F0-9]*"]"    { yylval.str = AST_STRDUP(yytext); return TOKEN_BYTE_BUFFER; }
uuid4"{"{UUID}"}"       { yylval.str = AST_STRDUP(yytext); return TOKEN_UUID_V4; }
uuid7"{"{UUID}"}"       { yylval.str = AST_STRDUP(yytext); return TOKEN_UUID_V7; }
sha3"{"[a-f0-9]{64}"}"  { yylval.str = AST_STRDUP(yytext); return TOKEN_SHA_HASH; }

0x"["[^\]]*"]"        { yyerror("Invalid buffer contents"); return YYerror; }
uuid(4|7)"{"[^}]*"}" { yyerror("Invalid UUID value"); return YYerror; }
sha3"{"[^}]*"}"      { yyerror("Invalid SHA3 value"); return YYerror; }

0x"["[a-zA-Z0-9]*          { yyerror("Missing close bracket"); return YYerror; }
uuid(4|7)"{"[a-zA-Z0-9-]+  { yyerror("Missing close bracket"); return YYerror; }
sha3"{"[a-zA-Z0-9]+        { yyerror("Missing close bracket"); return YYerror; }

<INITIAL>{
\"            { BEGIN(STRING); string_buf_bs.len = 0; ByteStringStoreChar('"'); }
}
<STRING>{
\"            { BEGIN(INITIAL); ByteStringStoreChar('"'); yylval.bstr = bstrAlloc(string_buf_bs); return TOKEN_STRING; }
<<EOF>>       { BEGIN(INITIAL); yyerror("Unclosed String"); return YYEOF; }
\n[ \t\r]*\\  { ByteStringStoreChar('\n'); /*ignore whitespace till alignment on multi-line string*/ }
[^"]          { ByteStringStoreChar(yytext[0]); }
}

<INITIAL>{
'             { BEGIN(ASCII_STRING); string_buf_bs.len = 0; ByteStringStoreChar('\''); }
}
<ASCII_STRING>{
'             { BEGIN(INITIAL); ByteStringStoreChar('\''); yylval.bstr = bstrAlloc(string_buf_bs); return TOKEN_ASCII_STRING; }
<<EOF>>       { BEGIN(INITIAL); yyerror("Unclosed ASCIIString"); return YYEOF; }
\n[ \t\r]*\\  { ByteStringStoreChar('\n'); /*ignore whitespace till alignment on multi-line string*/ }
[!-~ \t]      { ByteStringStoreChar(yytext[0]); }
.             { yyerror("Non-printable character (ignoring)"); return YYerror; }
}

<INITIAL>{
"/"         { BEGIN(REGEX); string_buf_bs.len = 0; ByteStringStoreChar('/'); }
}
<REGEX>{
"/"         { BEGIN(INITIAL); ByteStringStoreChar('/'); yylval.bstr = bstrAlloc(string_buf_bs); return TOKEN_REGEX; }
<<EOF>>     { BEGIN(INITIAL); yyerror("Unclosed Regex"); return YYEOF; }
\n          { yyerror("Newline in Regex"); return YYerror; }
[!-~ \t]    { ByteStringStoreChar(yytext[0]); }
.           { yyerror("Invalid character (ignoring)"); return YYerror;}
}

<INITIAL>{
[gf]?`      { BEGIN(PATH_ITEM); string_buf_bs.len = 0; ByteStringStoreText(yytext, yyleng); }
}
<PATH_ITEM>{
`           { BEGIN(INITIAL); ByteStringStoreChar('`'); yylval.bstr = bstrAlloc(string_buf_bs); return TOKEN_PATH_ITEM; }
<<EOF>>     { BEGIN(INITIAL); yyerror("Unclosed Path Item"); return YYEOF; }
[ \t\n\r]   { yyerror("Whitespace in Path Item"); return YYerror; }
[!-~]       { ByteStringStoreChar(yytext[0]); }
.           { yyerror("Invalid character (ignoring)"); return YYerror;}
}

 /* dates */
{DATE}T{TIME}@{TZNAME} { yylval.str = AST_STRDUP(yytext); return TOKEN_DATE_TIME; }
{DATE}T{TIME}Z?        { yylval.str = AST_STRDUP(yytext); return TOKEN_UTC_DATE_TIME; }
{DATE}                 { yylval.str = AST_STRDUP(yytext); return TOKEN_PLAIN_DATE; }
{TIME}                 { yylval.str = AST_STRDUP(yytext); return TOKEN_PLAIN_TIME; }

(0|{NON_ZERO_INTEGRAL})t { yylval.str = AST_STRDUP(yytext); return TOKEN_TICK_TIME; }
(0|{NON_ZERO_INTEGRAL})l { yylval.str = AST_STRDUP(yytext); return TOKEN_LOGICAL_TIME; }

[+-]0[tl]                                        { yyerror("Cannot have sign/negative time"); return YYerror; }
[+-]{NON_ZERO_INTEGRAL}[tl]                      { yyerror("Cannot have sign/negative time"); return YYerror; }
0+{NON_ZERO_INTEGRAL}[tl]                        { yyerror("Leading zero is not allowed"); return YYerror; }
[+-]?00+[tl]                                     { yyerror("Leading zero is not allowed"); return YYerror; }

{DATE}T{TIME}("."[0-9]{3})Z { yylval.str = AST_STRDUP(yytext); return TOKEN_TIMESTAMP; }

 /* names */
{IDENTIFIER} { 
    size_t conflict = isSpecialTypedLiteralIdConflict(yytext);
    if(conflict != 0) {
        char buff[16];
        memcpy(buff, yytext, conflict);

        yyless(strlen(yytext) - conflict);
        if(strncmp("none", buff, 4) == 0) {
            return KW_NONE;
        }
        else if(strncmp("true", buff, 4) == 0) {
            return KW_TRUE;
        }
        else if(strncmp("false", buff, 5) == 0) {
            return KW_FALSE;
        }
        else {
            return KW_NOTHING;
        }
    } 
    else { 
        yylval.str = AST_STRDUP(yytext); 
        return TOKEN_IDENTIFIER; 
    } 
  }

_"$"{IDENTIFIER} { 
    yylval.str = AST_STRDUP(yytext); 
    return TOKEN_UNSPEC_IDENTIFIER; 
  }

{TYPE_IDENTIFIER}(::{TYPE_IDENTIFIER})* { yylval.str = AST_STRDUP(yytext); return TOKEN_TYPE_COMPONENT; }

 /* comments */
"%%"[^\n]*    /* line comment */

[ \t\n\r]   /* ignore white space */ 

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

    for(size_t i = 0; i < len; i++) {
        string_buf[string_buf_bs.len++] = (uint8_t)c[i];
    }
}
