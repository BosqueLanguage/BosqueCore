%{
#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>

//#include "bsqon.h"

int yylex(void);
void yyerror(char* s, ...);

#define YYDEBUG 1
%}

%union {
  int bsqon;
  char* str;
}

/* declare tokens */
%left SYM_BAR
%left SYM_AMP

%token SYM_ELLIPSIS SYM_DOUBLE_COLON SYM_ENTRY SYM_COLON SYM_COMMA SYM_BANG SYM_EQUALS SYM_DOT SYM_AT SYM_UNDERSCORE
%token KW_SOMETHING KW_NOTHING KW_FALSE KW_SRC KW_NONE KW_NULL KW_SOME KW_TRUE KW_ERR KW_LET KW_IN KW_OK

%token <str> TOKEN_NAT TOKEN_INT TOKEN_BIG_NAT TOKEN_BIG_INT 
%token <str> TOKEN_RATIONAL TOKEN_FLOAT TOKEN_DOUBLE
%token <str> TOKEN_INT_NUMBERINO TOKEN_FLOAT_NUMBERINO

%token <str> TOKEN_BYTE_BUFFER TOKEN_UUID_V4 TOKEN_UUID_V7 TOKEN_SHA_HASH
%token <str> TOKEN_STRING TOKEN_ASCII_STRING TOKEN_REGEX TOKEN_PATH_ITEM

%token <str> TOKEN_DATE_TIME TOKEN_UTC_DATE_TIME TOKEN_PLAIN_DATE TOKEN_PLAIN_TIME
%token <str> TOKEN_LOGICAL_TIME TOKEN_TICK_TIME TOKEN_TIMESTAMP

%token <str> TOKEN_IDENTIFIER TOKEN_REF TOKEN_TYPE_COMPONENT

  /* %type <a> exp stmt list explist */
  /* %type <sl> symlist */

%type <bsqon> bsqonliteral bsqonval

%start bsqonval

%%

bsqonliteral: 
   KW_NONE { printf("%s\n", "null"); $$ = 1; }
   | KW_TRUE           { printf("%s\n", "true"); $$ = 1; }
   | KW_FALSE           { printf("%s\n", "false"); $$ = 1; }
   | TOKEN_NAT           { printf("%s\n", $1); $$ = 1; }
   | TOKEN_INT                { printf("%s\n", $1); $$ = 1; }
   | TOKEN_BIG_NAT           { printf("%s\n", $1); $$ = 1; }
   | TOKEN_BIG_INT           { printf("%s\n", $1); $$ = 1; }
;

bsqonval: 
  bsqonliteral
 ;
%%

extern FILE* yyin;

void yyerror(char *s, ...)
{
   va_list ap;
   va_start(ap, s);

/*
   if(yylloc.first_line) {
      fprintf(stderr, "%s:%d.%d-%d.%d: error: ", yylloc.filename, yylloc.first_line, yylloc.first_column, yylloc.last_line, yylloc.last_column);
   }
*/

   vfprintf(stderr, s, ap);
   fprintf(stderr, "\n");
}

int main(int argc, char** argv)
{
   if(argc == 0) {
      printf("Usage: %s [-d] file\n", argv[0]);
      perror(argv[1]);
      exit(1);
   }

   if(argc > 1 && !strcmp(argv[1], "-d")) {
      yydebug = 1; argc--; argv++;
   }

    //see page 34 of book

   if(argc > 1) {
      if((yyin = fopen(argv[1], "r")) == NULL) {
         perror(argv[1]);
         exit(1);
      }

      //filename = av[1];
   }

   if(!yyparse()) {
      printf("Parse ok!\n");
   }
   else {
      printf("Parse errors...\n");
   }
}
