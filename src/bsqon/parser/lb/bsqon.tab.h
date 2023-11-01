/* A Bison parser, made by GNU Bison 3.8.2.  */

/* Bison interface for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2015, 2018-2021 Free Software Foundation,
   Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* DO NOT RELY ON FEATURES THAT ARE NOT DOCUMENTED in the manual,
   especially those whose name start with YY_ or yy_.  They are
   private implementation details that can be changed or removed.  */

#ifndef YY_YY_BSQON_TAB_H_INCLUDED
# define YY_YY_BSQON_TAB_H_INCLUDED
/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int yydebug;
#endif

/* Token kinds.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    YYEMPTY = -2,
    YYEOF = 0,                     /* "end of file"  */
    YYerror = 256,                 /* error  */
    YYUNDEF = 257,                 /* "invalid token"  */
    SYM_BAR = 258,                 /* SYM_BAR  */
    SYM_AMP = 260,                 /* SYM_AMP  */
    SYM_COLON = 262,               /* ":"  */
    SYM_COMMA = 263,               /* ","  */
    KW_NONE = 264,                 /* "none"  */
    KW_NOTHING = 265,              /* "nothing"  */
    KW_TRUE = 266,                 /* "true"  */
    KW_FALSE = 267,                /* "false"  */
    KW_SOMETHING = 268,            /* "something"  */
    KW_OK = 269,                   /* "ok"  */
    KW_ERR = 270,                  /* "err"  */
    SYM_DOUBLE_COLON = 271,        /* "::"  */
    SYM_ELLIPSIS = 272,            /* SYM_ELLIPSIS  */
    SYM_ENTRY = 273,               /* SYM_ENTRY  */
    SYM_BANG = 274,                /* SYM_BANG  */
    SYM_EQUALS = 275,              /* SYM_EQUALS  */
    SYM_DOT = 276,                 /* SYM_DOT  */
    SYM_AT = 277,                  /* SYM_AT  */
    SYM_UNDERSCORE = 278,          /* SYM_UNDERSCORE  */
    KW_SOME = 279,                 /* KW_SOME  */
    KW_SRC = 280,                  /* KW_SRC  */
    KW_LET = 281,                  /* KW_LET  */
    KW_IN = 282,                   /* KW_IN  */
    TOKEN_NAT = 283,               /* TOKEN_NAT  */
    TOKEN_INT = 284,               /* TOKEN_INT  */
    TOKEN_BIG_NAT = 285,           /* TOKEN_BIG_NAT  */
    TOKEN_BIG_INT = 286,           /* TOKEN_BIG_INT  */
    TOKEN_RATIONAL = 287,          /* TOKEN_RATIONAL  */
    TOKEN_FLOAT = 288,             /* TOKEN_FLOAT  */
    TOKEN_DOUBLE = 289,            /* TOKEN_DOUBLE  */
    TOKEN_NUMBERINO = 290,         /* "numberino"  */
    TOKEN_BYTE_BUFFER = 291,       /* TOKEN_BYTE_BUFFER  */
    TOKEN_UUID_V4 = 292,           /* TOKEN_UUID_V4  */
    TOKEN_UUID_V7 = 293,           /* TOKEN_UUID_V7  */
    TOKEN_SHA_HASH = 294,          /* TOKEN_SHA_HASH  */
    TOKEN_STRING = 295,            /* TOKEN_STRING  */
    TOKEN_ASCII_STRING = 296,      /* TOKEN_ASCII_STRING  */
    TOKEN_REGEX = 297,             /* TOKEN_REGEX  */
    TOKEN_PATH_ITEM = 298,         /* TOKEN_PATH_ITEM  */
    TOKEN_DATE_TIME = 299,         /* TOKEN_DATE_TIME  */
    TOKEN_UTC_DATE_TIME = 300,     /* TOKEN_UTC_DATE_TIME  */
    TOKEN_PLAIN_DATE = 301,        /* TOKEN_PLAIN_DATE  */
    TOKEN_PLAIN_TIME = 302,        /* TOKEN_PLAIN_TIME  */
    TOKEN_LOGICAL_TIME = 303,      /* TOKEN_LOGICAL_TIME  */
    TOKEN_TICK_TIME = 304,         /* TOKEN_TICK_TIME  */
    TOKEN_TIMESTAMP = 305,         /* TOKEN_TIMESTAMP  */
    TOKEN_IDENTIFIER = 306,        /* "identifier"  */
    TOKEN_TYPE_COMPONENT = 307,    /* "type name"  */
    TOKEN_UNSPEC_IDENTIFIER = 308  /* "unspec identifier"  */
  };
  typedef enum yytokentype yytoken_kind_t;
#endif

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
union YYSTYPE
{
#line 31 "bsqon.y"

   struct BSQON_TYPE_AST_List* bsqon_t_list;
   struct BSQON_TYPE_AST_NamedListEntry* bsqon_t_nametypel_entry;
   struct BSQON_TYPE_AST_NamedList* bsqon_t_namedlist;
   struct BSQON_TYPE_AST_Node* bsqon_t;

   struct BSQON_AST_NamedListEntry* bsqon_nameval_entry;
   struct BSQON_AST_List* bsqon_list;
   struct BSQON_AST_NamedList* bsqon_namedlist;

   struct BSQON_AST_Node* bsqon;
   struct ByteString* bstr;
   char* str;

#line 130 "bsqon.tab.h"

};
typedef union YYSTYPE YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif

/* Location type.  */
#if ! defined YYLTYPE && ! defined YYLTYPE_IS_DECLARED
typedef struct YYLTYPE YYLTYPE;
struct YYLTYPE
{
  int first_line;
  int first_column;
  int last_line;
  int last_column;
};
# define YYLTYPE_IS_DECLARED 1
# define YYLTYPE_IS_TRIVIAL 1
#endif


extern YYSTYPE yylval;
extern YYLTYPE yylloc;

int yyparse (void);


#endif /* !YY_YY_BSQON_TAB_H_INCLUDED  */
