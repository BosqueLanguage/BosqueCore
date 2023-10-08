%{
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>

#include "bsqon_type_ast.h"
#include "bsqon_ast.h"

int yylex(void);
void yyerror(const char* s, ...);

struct BSQON_TYPE_AST_Node* yybsqonval_type;
struct BSQON_AST_Node* yybsqonval;
char* filename = "<stdin>";

#define MAX_PARSER_ERRORS 128
#define MAX_ERROR_LENGTH 1024

char errorbuf[MAX_ERROR_LENGTH];
char* errors[MAX_PARSER_ERRORS];
int errorcount = 0;

#define YYDEBUG 1
%}

%union {
   struct BSQON_TYPE_AST_List* bsqon_t_list;
   struct BSQON_TYPE_AST_NamedList* bsqon_t_namedlist;
   struct BSQON_TYPE_AST_Node* bsqon_t;
   struct BSQON_AST_Node* bsqon;
   struct ByteString* bstr;
   char* str;
}

%define parse.error verbose
%locations

/* declare tokens */
%left SYM_BAR
%left SYM_AMP

%token SYM_ELLIPSIS SYM_DOUBLE_COLON SYM_ENTRY SYM_COLON SYM_COMMA SYM_BANG SYM_EQUALS SYM_DOT SYM_AT SYM_UNDERSCORE
%token KW_SOMETHING KW_NOTHING KW_FALSE KW_SRC KW_NONE KW_SOME KW_TRUE KW_ERR KW_LET KW_IN KW_OK

%token <str> TOKEN_NAT TOKEN_INT TOKEN_BIG_NAT TOKEN_BIG_INT 
%token <str> TOKEN_RATIONAL TOKEN_FLOAT TOKEN_DOUBLE
%token <str> TOKEN_NUMBERINO

%token <str> TOKEN_BYTE_BUFFER TOKEN_UUID_V4 TOKEN_UUID_V7 TOKEN_SHA_HASH
%token <bstr> TOKEN_STRING TOKEN_ASCII_STRING TOKEN_REGEX TOKEN_PATH_ITEM

%token <str> TOKEN_DATE_TIME TOKEN_UTC_DATE_TIME TOKEN_PLAIN_DATE TOKEN_PLAIN_TIME
%token <str> TOKEN_LOGICAL_TIME TOKEN_TICK_TIME TOKEN_TIMESTAMP

%token <str> TOKEN_IDENTIFIER "identifier"
%token <str> TOKEN_UNSPEC_IDENTIFIER TOKEN_TYPE_COMPONENT

  /* %type <a> exp stmt list explist */
  /* %type <sl> symlist */

%type <bsqon_t_list> bsqontypel bsqontermslist
%type <bsqon_t> bsqontypel_entry
%type <bsqon_t_namedlist> bsqonnametypel
%type <bsqon_t> bsqontype bsqonnominaltype bsqontupletype
%type <bsqon_t> bsqontyperoot

%type <bsqon> bsqonval bsqonliteral bsqonunspecvar bsqonidentifier
%type <bsqon> bsqonroot

  //----------------------------
  //%start bsqonroot
  %start bsqontyperoot

%%

bsqonnominaltype:
   TOKEN_TYPE_COMPONENT { $$ = BSQON_AST_NominalNodeCreate($1, NULL); }
   | TOKEN_TYPE_COMPONENT bsqontermslist { $$ = BSQON_AST_NominalNodeCreate($1, $2); }
;

bsqontermslist:
   '<' bsqontype '>' { $$ = BSQON_TYPE_AST_ListCons($2, NULL); }
   | '<' bsqontypel bsqontype '>' { $$ = BSQON_TYPE_AST_ListCompleteParse(BSQON_TYPE_AST_ListCons($3, $2)); }
   | '<' error '>' { $$ = BSQON_TYPE_AST_ListCons(BSQON_AST_ErrorNodeCreate(), NULL); yyerrok; }
   | '<' bsqontypel error '>' { $$ = BSQON_TYPE_AST_ListCompleteParse(BSQON_TYPE_AST_ListCons(BSQON_AST_ErrorNodeCreate(), $2)); yyerrok; }
;

bsqontupletype:
   '[' ']' { $$ = BSQON_AST_TupleNodeCreate(NULL); }
   | '[' bsqontype ']' { $$ = BSQON_AST_TupleNodeCreate(BSQON_TYPE_AST_ListCons($2, NULL)); }
   | '[' bsqontypel bsqontype ']' { $$ = BSQON_AST_TupleNodeCreate(BSQON_TYPE_AST_ListCompleteParse(BSQON_TYPE_AST_ListCons($3, $2))); }
   | '[' error ']' { $$ = BSQON_AST_TupleNodeCreate(BSQON_TYPE_AST_ListCons(BSQON_AST_ErrorNodeCreate(), NULL)); yyerrok; }
   | '[' bsqontypel error ']' { $$ = BSQON_AST_TupleNodeCreate(BSQON_TYPE_AST_ListCompleteParse(BSQON_TYPE_AST_ListCons(BSQON_AST_ErrorNodeCreate(), $2))); yyerrok; }
;

bsqontypel:
   bsqontypel bsqontypel_entry { $$ = BSQON_TYPE_AST_ListCons($2, $1); }
   | bsqontypel_entry { $$ = BSQON_TYPE_AST_ListCons($1, NULL); }
;

bsqontypel_entry:
   bsqontype SYM_COMMA { $$ = $1; }
   | error SYM_COMMA { $$ = BSQON_AST_ErrorNodeCreate(); yyerrok; }
;

bsqonnametypel:
;

bsqontype:
   bsqonnominaltype { $$ = $1; }
   | bsqontupletype { $$ = $1; }
;

bsqontyperoot:
   bsqontype { yybsqonval_type = $1; $$ = $1; }
;

bsqonliteral: 
   KW_NONE                 { $$ = BSQON_AST_LiteralNodeCreateEmpty(BSQON_AST_TAG_None); }
   | KW_NOTHING            { $$ = BSQON_AST_LiteralNodeCreateEmpty(BSQON_AST_TAG_Nothing); }
   | KW_TRUE               { $$ = BSQON_AST_LiteralNodeCreateEmpty(BSQON_AST_TAG_True); }
   | KW_FALSE              { $$ = BSQON_AST_LiteralNodeCreateEmpty(BSQON_AST_TAG_False); }
   | TOKEN_NAT             { $$ = BSQON_AST_LiteralNodeCreateChars(BSQON_AST_TAG_Nat, $1); }
   | TOKEN_INT             { $$ = BSQON_AST_LiteralNodeCreateChars(BSQON_AST_TAG_Int, $1); }
   | TOKEN_BIG_NAT         { $$ = BSQON_AST_LiteralNodeCreateChars(BSQON_AST_TAG_BigNat, $1); }
   | TOKEN_BIG_INT         { $$ = BSQON_AST_LiteralNodeCreateChars(BSQON_AST_TAG_BigInt, $1); }
   | TOKEN_RATIONAL        { $$ = BSQON_AST_LiteralNodeCreateChars(BSQON_AST_TAG_Rational, $1); }
   | TOKEN_FLOAT           { $$ = BSQON_AST_LiteralNodeCreateChars(BSQON_AST_TAG_Float, $1); }
   | TOKEN_DOUBLE          { $$ = BSQON_AST_LiteralNodeCreateChars(BSQON_AST_TAG_Double, $1); }
   | TOKEN_NUMBERINO       { $$ = BSQON_AST_LiteralNodeCreateChars(BSQON_AST_TAG_Numberino, $1); }
   | TOKEN_BYTE_BUFFER     { $$ = BSQON_AST_LiteralNodeCreateChars(BSQON_AST_TAG_ByteBuffer, $1); }
   | TOKEN_UUID_V4         { $$ = BSQON_AST_LiteralNodeCreateChars(BSQON_AST_TAG_UUIDv4, $1); }
   | TOKEN_UUID_V7         { $$ = BSQON_AST_LiteralNodeCreateChars(BSQON_AST_TAG_UUIDv7, $1); }
   | TOKEN_SHA_HASH        { $$ = BSQON_AST_LiteralNodeCreateChars(BSQON_AST_TAG_SHAHashcode, $1); }
   | TOKEN_STRING          { $$ = BSQON_AST_LiteralNodeCreateBytes(BSQON_AST_TAG_String, $1); }
   | TOKEN_ASCII_STRING    { $$ = BSQON_AST_LiteralNodeCreateBytes(BSQON_AST_TAG_ASCIIString, $1); }
   | TOKEN_REGEX           { $$ = BSQON_AST_LiteralNodeCreateBytes(BSQON_AST_TAG_Regex, $1); }
   | TOKEN_PATH_ITEM       { $$ = BSQON_AST_LiteralNodeCreateBytes(BSQON_AST_TAG_PathItem, $1); }
   | TOKEN_DATE_TIME       { $$ = BSQON_AST_LiteralNodeCreateChars(BSQON_AST_TAG_DateTime, $1); }
   | TOKEN_UTC_DATE_TIME   { $$ = BSQON_AST_LiteralNodeCreateChars(BSQON_AST_TAG_UTCDateTime, $1); }
   | TOKEN_PLAIN_DATE      { $$ = BSQON_AST_LiteralNodeCreateChars(BSQON_AST_TAG_PlainDate, $1); }
   | TOKEN_PLAIN_TIME      { $$ = BSQON_AST_LiteralNodeCreateChars(BSQON_AST_TAG_PlainTime, $1); }
   | TOKEN_LOGICAL_TIME    { $$ = BSQON_AST_LiteralNodeCreateChars(BSQON_AST_TAG_LogicalTime, $1); }
   | TOKEN_TICK_TIME       { $$ = BSQON_AST_LiteralNodeCreateChars(BSQON_AST_TAG_TickTime, $1); }
   | TOKEN_TIMESTAMP       { $$ = BSQON_AST_LiteralNodeCreateChars(BSQON_AST_TAG_Timestamp, $1); }
;

bsqonunspecvar: 
   TOKEN_UNSPEC_IDENTIFIER { $$ = BSQON_AST_NameNodeCreate(BSQON_AST_TAG_UnspecIdentifier, $1); }
;

bsqonidentifier: 
   KW_SRC       { $$ = BSQON_AST_NameNodeCreate(BSQON_AST_TAG_Identifier, "$src"); }
   | TOKEN_IDENTIFIER { $$ = BSQON_AST_NameNodeCreate(BSQON_AST_TAG_Identifier, $1); }
;

bsqonval: 
  bsqonliteral | bsqonunspecvar | bsqonidentifier { $$ = $1; }
 ;

bsqonroot: bsqonval { yybsqonval = $1; $$ = $1; }
%%

extern FILE* yyin;

void yyerror(const char *s, ...)
{
   va_list ap;
   va_start(ap, s);

   if(yylloc.first_line) {
      int ccount = snprintf(errorbuf, MAX_ERROR_LENGTH, "%s @ %d.%d-%d.%d -- %s", s, yylloc.first_line, yylloc.first_column, yylloc.last_line, yylloc.last_column, filename);

      if(errorcount < MAX_PARSER_ERRORS) {
         errors[errorcount++] = strndup(errorbuf, ccount);
      }
   }
}

#ifndef EXPORT
int main(int argc, char** argv)
{
   if(argc > 1 && !strcmp(argv[1], "-d")) {
      yydebug = 1; argc--; argv++;
   }

    //see page 34 of book

   if(argc == 1) {
      yyin = stdin;
      filename = "<stdin>";
   }
   else {
      if((yyin = fopen(argv[1], "r")) == NULL) {
         perror(argv[1]);
         exit(1);
      }

      filename = argv[1];
   }

   if(!yyparse()) {
      //----------------------------
      //BSQON_AST_print(yybsqonval);
      BSQON_TYPE_AST_print(yybsqonval_type);

      printf("\n");
      fflush(stdout);
   }
      
   for(size_t i = 0; i < errorcount; ++i) {
      printf("%s\n", errors[i]);
      fflush(stdout);
   }
}
#endif
