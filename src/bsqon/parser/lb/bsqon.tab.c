/* A Bison parser, made by GNU Bison 3.8.2.  */

/* Bison implementation for Yacc-like parsers in C

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

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* DO NOT RELY ON FEATURES THAT ARE NOT DOCUMENTED in the manual,
   especially those whose name start with YY_ or yy_.  They are
   private implementation details that can be changed or removed.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output, and Bison version.  */
#define YYBISON 30802

/* Bison version string.  */
#define YYBISON_VERSION "3.8.2"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 0

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1




/* First part of user prologue.  */
#line 1 "bsqon.y"

#include <stdio.h>
#include <stdlib.h>
#include <stdarg.h>
#include <string.h>

#include "bsqon_type_ast.h"
#include "bsqon_ast.h"

int yylex(void);
void yyerror(const char* s, ...);

#define MK_SPOS_S(T) (createSourcePos((T).first_line, (T).first_column, (T).last_line, (T).last_column))
#define MK_SPOS_R(S, E) (createSourcePos((S).first_line, (S).first_column, (E).last_line, (E).last_column))

struct BSQON_TYPE_AST_Node* yybsqonval_type;
struct BSQON_AST_Node* yybsqonval;
char* filename = "<stdin>";

#define MAX_PARSER_ERRORS 128
#define MAX_ERROR_LENGTH 1024

char errorbuf[MAX_ERROR_LENGTH];
char* errors[MAX_PARSER_ERRORS];
int errorcount = 0;

#define YYDEBUG 1

#line 100 "bsqon.tab.c"

# ifndef YY_CAST
#  ifdef __cplusplus
#   define YY_CAST(Type, Val) static_cast<Type> (Val)
#   define YY_REINTERPRET_CAST(Type, Val) reinterpret_cast<Type> (Val)
#  else
#   define YY_CAST(Type, Val) ((Type) (Val))
#   define YY_REINTERPRET_CAST(Type, Val) ((Type) (Val))
#  endif
# endif
# ifndef YY_NULLPTR
#  if defined __cplusplus
#   if 201103L <= __cplusplus
#    define YY_NULLPTR nullptr
#   else
#    define YY_NULLPTR 0
#   endif
#  else
#   define YY_NULLPTR ((void*)0)
#  endif
# endif

#include "bsqon.tab.h"
/* Symbol kind.  */
enum yysymbol_kind_t
{
  YYSYMBOL_YYEMPTY = -2,
  YYSYMBOL_YYEOF = 0,                      /* "end of file"  */
  YYSYMBOL_YYerror = 1,                    /* error  */
  YYSYMBOL_YYUNDEF = 2,                    /* "invalid token"  */
  YYSYMBOL_SYM_BAR = 3,                    /* SYM_BAR  */
  YYSYMBOL_4_ = 4,                         /* "|"  */
  YYSYMBOL_SYM_AMP = 5,                    /* SYM_AMP  */
  YYSYMBOL_6_ = 6,                         /* "&"  */
  YYSYMBOL_SYM_COLON = 7,                  /* ":"  */
  YYSYMBOL_SYM_COMMA = 8,                  /* ","  */
  YYSYMBOL_KW_NONE = 9,                    /* "none"  */
  YYSYMBOL_KW_NOTHING = 10,                /* "nothing"  */
  YYSYMBOL_KW_TRUE = 11,                   /* "true"  */
  YYSYMBOL_KW_FALSE = 12,                  /* "false"  */
  YYSYMBOL_KW_SOMETHING = 13,              /* "something"  */
  YYSYMBOL_KW_OK = 14,                     /* "ok"  */
  YYSYMBOL_KW_ERR = 15,                    /* "err"  */
  YYSYMBOL_SYM_DOUBLE_COLON = 16,          /* "::"  */
  YYSYMBOL_SYM_ELLIPSIS = 17,              /* SYM_ELLIPSIS  */
  YYSYMBOL_SYM_ENTRY = 18,                 /* SYM_ENTRY  */
  YYSYMBOL_SYM_BANG = 19,                  /* SYM_BANG  */
  YYSYMBOL_SYM_EQUALS = 20,                /* SYM_EQUALS  */
  YYSYMBOL_SYM_DOT = 21,                   /* SYM_DOT  */
  YYSYMBOL_SYM_AT = 22,                    /* SYM_AT  */
  YYSYMBOL_SYM_UNDERSCORE = 23,            /* SYM_UNDERSCORE  */
  YYSYMBOL_KW_SOME = 24,                   /* KW_SOME  */
  YYSYMBOL_KW_SRC = 25,                    /* KW_SRC  */
  YYSYMBOL_KW_LET = 26,                    /* KW_LET  */
  YYSYMBOL_KW_IN = 27,                     /* KW_IN  */
  YYSYMBOL_TOKEN_NAT = 28,                 /* TOKEN_NAT  */
  YYSYMBOL_TOKEN_INT = 29,                 /* TOKEN_INT  */
  YYSYMBOL_TOKEN_BIG_NAT = 30,             /* TOKEN_BIG_NAT  */
  YYSYMBOL_TOKEN_BIG_INT = 31,             /* TOKEN_BIG_INT  */
  YYSYMBOL_TOKEN_RATIONAL = 32,            /* TOKEN_RATIONAL  */
  YYSYMBOL_TOKEN_FLOAT = 33,               /* TOKEN_FLOAT  */
  YYSYMBOL_TOKEN_DOUBLE = 34,              /* TOKEN_DOUBLE  */
  YYSYMBOL_TOKEN_NUMBERINO = 35,           /* "numberino"  */
  YYSYMBOL_TOKEN_BYTE_BUFFER = 36,         /* TOKEN_BYTE_BUFFER  */
  YYSYMBOL_TOKEN_UUID_V4 = 37,             /* TOKEN_UUID_V4  */
  YYSYMBOL_TOKEN_UUID_V7 = 38,             /* TOKEN_UUID_V7  */
  YYSYMBOL_TOKEN_SHA_HASH = 39,            /* TOKEN_SHA_HASH  */
  YYSYMBOL_TOKEN_STRING = 40,              /* TOKEN_STRING  */
  YYSYMBOL_TOKEN_ASCII_STRING = 41,        /* TOKEN_ASCII_STRING  */
  YYSYMBOL_TOKEN_REGEX = 42,               /* TOKEN_REGEX  */
  YYSYMBOL_TOKEN_PATH_ITEM = 43,           /* TOKEN_PATH_ITEM  */
  YYSYMBOL_TOKEN_DATE_TIME = 44,           /* TOKEN_DATE_TIME  */
  YYSYMBOL_TOKEN_UTC_DATE_TIME = 45,       /* TOKEN_UTC_DATE_TIME  */
  YYSYMBOL_TOKEN_PLAIN_DATE = 46,          /* TOKEN_PLAIN_DATE  */
  YYSYMBOL_TOKEN_PLAIN_TIME = 47,          /* TOKEN_PLAIN_TIME  */
  YYSYMBOL_TOKEN_LOGICAL_TIME = 48,        /* TOKEN_LOGICAL_TIME  */
  YYSYMBOL_TOKEN_TICK_TIME = 49,           /* TOKEN_TICK_TIME  */
  YYSYMBOL_TOKEN_TIMESTAMP = 50,           /* TOKEN_TIMESTAMP  */
  YYSYMBOL_TOKEN_IDENTIFIER = 51,          /* "identifier"  */
  YYSYMBOL_TOKEN_TYPE_COMPONENT = 52,      /* "type name"  */
  YYSYMBOL_TOKEN_UNSPEC_IDENTIFIER = 53,   /* "unspec identifier"  */
  YYSYMBOL_54_ = 54,                       /* '<'  */
  YYSYMBOL_55_ = 55,                       /* '>'  */
  YYSYMBOL_56_ = 56,                       /* '['  */
  YYSYMBOL_57_ = 57,                       /* ']'  */
  YYSYMBOL_58_ = 58,                       /* '{'  */
  YYSYMBOL_59_ = 59,                       /* '}'  */
  YYSYMBOL_60_ = 60,                       /* '('  */
  YYSYMBOL_61_ = 61,                       /* ')'  */
  YYSYMBOL_62_ = 62,                       /* ':'  */
  YYSYMBOL_YYACCEPT = 63,                  /* $accept  */
  YYSYMBOL_bsqontypel = 64,                /* bsqontypel  */
  YYSYMBOL_bsqontypel_entry = 65,          /* bsqontypel_entry  */
  YYSYMBOL_bsqonnametypel = 66,            /* bsqonnametypel  */
  YYSYMBOL_bsqonnametypel_entry = 67,      /* bsqonnametypel_entry  */
  YYSYMBOL_bsqonnominaltype = 68,          /* bsqonnominaltype  */
  YYSYMBOL_bsqontermslist = 69,            /* bsqontermslist  */
  YYSYMBOL_bsqontupletype = 70,            /* bsqontupletype  */
  YYSYMBOL_bsqonrecordtype = 71,           /* bsqonrecordtype  */
  YYSYMBOL_bsqontype = 72,                 /* bsqontype  */
  YYSYMBOL_bsqontspec = 73,                /* bsqontspec  */
  YYSYMBOL_bsqonliteral = 74,              /* bsqonliteral  */
  YYSYMBOL_bsqonunspecvar = 75,            /* bsqonunspecvar  */
  YYSYMBOL_bsqonidentifier = 76,           /* bsqonidentifier  */
  YYSYMBOL_bsqonscopedidentifier = 77,     /* bsqonscopedidentifier  */
  YYSYMBOL_bsqonstringof = 78,             /* bsqonstringof  */
  YYSYMBOL_bsqonpath = 79,                 /* bsqonpath  */
  YYSYMBOL_bsqontypeliteral = 80,          /* bsqontypeliteral  */
  YYSYMBOL_bsqonterminal = 81,             /* bsqonterminal  */
  YYSYMBOL_bsqon_mapentry = 82,            /* bsqon_mapentry  */
  YYSYMBOL_bsqonvall = 83,                 /* bsqonvall  */
  YYSYMBOL_bsqonl_entry = 84,              /* bsqonl_entry  */
  YYSYMBOL_bsqonbracketvalue = 85,         /* bsqonbracketvalue  */
  YYSYMBOL_bsqonnamevall = 86,             /* bsqonnamevall  */
  YYSYMBOL_bsqon_braceval = 87,            /* bsqon_braceval  */
  YYSYMBOL_bsqonnameval_entry = 88,        /* bsqonnameval_entry  */
  YYSYMBOL_bsqonbracevalue = 89,           /* bsqonbracevalue  */
  YYSYMBOL_bsqonbracketbracevalue = 90,    /* bsqonbracketbracevalue  */
  YYSYMBOL_bsqontypedvalue = 91,           /* bsqontypedvalue  */
  YYSYMBOL_bsqonstructvalue = 92,          /* bsqonstructvalue  */
  YYSYMBOL_bsqonspecialcons = 93,          /* bsqonspecialcons  */
  YYSYMBOL_bsqonval = 94,                  /* bsqonval  */
  YYSYMBOL_bsqonroot = 95                  /* bsqonroot  */
};
typedef enum yysymbol_kind_t yysymbol_kind_t;




#ifdef short
# undef short
#endif

/* On compilers that do not define __PTRDIFF_MAX__ etc., make sure
   <limits.h> and (if available) <stdint.h> are included
   so that the code can choose integer types of a good width.  */

#ifndef __PTRDIFF_MAX__
# include <limits.h> /* INFRINGES ON USER NAME SPACE */
# if defined __STDC_VERSION__ && 199901 <= __STDC_VERSION__
#  include <stdint.h> /* INFRINGES ON USER NAME SPACE */
#  define YY_STDINT_H
# endif
#endif

/* Narrow types that promote to a signed type and that can represent a
   signed or unsigned integer of at least N bits.  In tables they can
   save space and decrease cache pressure.  Promoting to a signed type
   helps avoid bugs in integer arithmetic.  */

#ifdef __INT_LEAST8_MAX__
typedef __INT_LEAST8_TYPE__ yytype_int8;
#elif defined YY_STDINT_H
typedef int_least8_t yytype_int8;
#else
typedef signed char yytype_int8;
#endif

#ifdef __INT_LEAST16_MAX__
typedef __INT_LEAST16_TYPE__ yytype_int16;
#elif defined YY_STDINT_H
typedef int_least16_t yytype_int16;
#else
typedef short yytype_int16;
#endif

/* Work around bug in HP-UX 11.23, which defines these macros
   incorrectly for preprocessor constants.  This workaround can likely
   be removed in 2023, as HPE has promised support for HP-UX 11.23
   (aka HP-UX 11i v2) only through the end of 2022; see Table 2 of
   <https://h20195.www2.hpe.com/V2/getpdf.aspx/4AA4-7673ENW.pdf>.  */
#ifdef __hpux
# undef UINT_LEAST8_MAX
# undef UINT_LEAST16_MAX
# define UINT_LEAST8_MAX 255
# define UINT_LEAST16_MAX 65535
#endif

#if defined __UINT_LEAST8_MAX__ && __UINT_LEAST8_MAX__ <= __INT_MAX__
typedef __UINT_LEAST8_TYPE__ yytype_uint8;
#elif (!defined __UINT_LEAST8_MAX__ && defined YY_STDINT_H \
       && UINT_LEAST8_MAX <= INT_MAX)
typedef uint_least8_t yytype_uint8;
#elif !defined __UINT_LEAST8_MAX__ && UCHAR_MAX <= INT_MAX
typedef unsigned char yytype_uint8;
#else
typedef short yytype_uint8;
#endif

#if defined __UINT_LEAST16_MAX__ && __UINT_LEAST16_MAX__ <= __INT_MAX__
typedef __UINT_LEAST16_TYPE__ yytype_uint16;
#elif (!defined __UINT_LEAST16_MAX__ && defined YY_STDINT_H \
       && UINT_LEAST16_MAX <= INT_MAX)
typedef uint_least16_t yytype_uint16;
#elif !defined __UINT_LEAST16_MAX__ && USHRT_MAX <= INT_MAX
typedef unsigned short yytype_uint16;
#else
typedef int yytype_uint16;
#endif

#ifndef YYPTRDIFF_T
# if defined __PTRDIFF_TYPE__ && defined __PTRDIFF_MAX__
#  define YYPTRDIFF_T __PTRDIFF_TYPE__
#  define YYPTRDIFF_MAXIMUM __PTRDIFF_MAX__
# elif defined PTRDIFF_MAX
#  ifndef ptrdiff_t
#   include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  endif
#  define YYPTRDIFF_T ptrdiff_t
#  define YYPTRDIFF_MAXIMUM PTRDIFF_MAX
# else
#  define YYPTRDIFF_T long
#  define YYPTRDIFF_MAXIMUM LONG_MAX
# endif
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif defined __STDC_VERSION__ && 199901 <= __STDC_VERSION__
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned
# endif
#endif

#define YYSIZE_MAXIMUM                                  \
  YY_CAST (YYPTRDIFF_T,                                 \
           (YYPTRDIFF_MAXIMUM < YY_CAST (YYSIZE_T, -1)  \
            ? YYPTRDIFF_MAXIMUM                         \
            : YY_CAST (YYSIZE_T, -1)))

#define YYSIZEOF(X) YY_CAST (YYPTRDIFF_T, sizeof (X))


/* Stored state numbers (used for stacks). */
typedef yytype_uint8 yy_state_t;

/* State numbers in computations.  */
typedef int yy_state_fast_t;

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(Msgid) dgettext ("bison-runtime", Msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(Msgid) Msgid
# endif
#endif


#ifndef YY_ATTRIBUTE_PURE
# if defined __GNUC__ && 2 < __GNUC__ + (96 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_PURE __attribute__ ((__pure__))
# else
#  define YY_ATTRIBUTE_PURE
# endif
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# if defined __GNUC__ && 2 < __GNUC__ + (7 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_UNUSED __attribute__ ((__unused__))
# else
#  define YY_ATTRIBUTE_UNUSED
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YY_USE(E) ((void) (E))
#else
# define YY_USE(E) /* empty */
#endif

/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
#if defined __GNUC__ && ! defined __ICC && 406 <= __GNUC__ * 100 + __GNUC_MINOR__
# if __GNUC__ * 100 + __GNUC_MINOR__ < 407
#  define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                           \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")
# else
#  define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                           \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")              \
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# endif
# define YY_IGNORE_MAYBE_UNINITIALIZED_END      \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif

#if defined __cplusplus && defined __GNUC__ && ! defined __ICC && 6 <= __GNUC__
# define YY_IGNORE_USELESS_CAST_BEGIN                          \
    _Pragma ("GCC diagnostic push")                            \
    _Pragma ("GCC diagnostic ignored \"-Wuseless-cast\"")
# define YY_IGNORE_USELESS_CAST_END            \
    _Pragma ("GCC diagnostic pop")
#endif
#ifndef YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_END
#endif


#define YY_ASSERT(E) ((void) (0 && (E)))

#if 1

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined EXIT_SUCCESS
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
      /* Use EXIT_SUCCESS as a witness for stdlib.h.  */
#     ifndef EXIT_SUCCESS
#      define EXIT_SUCCESS 0
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's 'empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (0)
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined EXIT_SUCCESS \
       && ! ((defined YYMALLOC || defined malloc) \
             && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef EXIT_SUCCESS
#    define EXIT_SUCCESS 0
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined EXIT_SUCCESS
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined EXIT_SUCCESS
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* 1 */

#if (! defined yyoverflow \
     && (! defined __cplusplus \
         || (defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL \
             && defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yy_state_t yyss_alloc;
  YYSTYPE yyvs_alloc;
  YYLTYPE yyls_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (YYSIZEOF (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (YYSIZEOF (yy_state_t) + YYSIZEOF (YYSTYPE) \
             + YYSIZEOF (YYLTYPE)) \
      + 2 * YYSTACK_GAP_MAXIMUM)

# define YYCOPY_NEEDED 1

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)                           \
    do                                                                  \
      {                                                                 \
        YYPTRDIFF_T yynewbytes;                                         \
        YYCOPY (&yyptr->Stack_alloc, Stack, yysize);                    \
        Stack = &yyptr->Stack_alloc;                                    \
        yynewbytes = yystacksize * YYSIZEOF (*Stack) + YYSTACK_GAP_MAXIMUM; \
        yyptr += yynewbytes / YYSIZEOF (*yyptr);                        \
      }                                                                 \
    while (0)

#endif

#if defined YYCOPY_NEEDED && YYCOPY_NEEDED
/* Copy COUNT objects from SRC to DST.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(Dst, Src, Count) \
      __builtin_memcpy (Dst, Src, YY_CAST (YYSIZE_T, (Count)) * sizeof (*(Src)))
#  else
#   define YYCOPY(Dst, Src, Count)              \
      do                                        \
        {                                       \
          YYPTRDIFF_T yyi;                      \
          for (yyi = 0; yyi < (Count); yyi++)   \
            (Dst)[yyi] = (Src)[yyi];            \
        }                                       \
      while (0)
#  endif
# endif
#endif /* !YYCOPY_NEEDED */

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  93
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   761

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  63
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  33
/* YYNRULES -- Number of rules.  */
#define YYNRULES  126
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  201

/* YYMAXUTOK -- Last valid token kind.  */
#define YYMAXUTOK   308


/* YYTRANSLATE(TOKEN-NUM) -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, with out-of-bounds checking.  */
#define YYTRANSLATE(YYX)                                \
  (0 <= (YYX) && (YYX) <= YYMAXUTOK                     \
   ? YY_CAST (yysymbol_kind_t, yytranslate[YYX])        \
   : YYSYMBOL_YYUNDEF)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex.  */
static const yytype_int8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
      60,    61,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,    62,     2,
      54,     2,    55,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,    56,     2,    57,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    58,     2,    59,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     3,     4,
       5,     6,     7,     8,     9,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53
};

#if YYDEBUG
/* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_int16 yyrline[] =
{
       0,   113,   113,   114,   118,   119,   123,   124,   128,   129,
     133,   134,   135,   139,   140,   141,   142,   146,   147,   148,
     149,   150,   154,   155,   156,   157,   158,   162,   163,   164,
     165,   166,   167,   168,   172,   173,   174,   182,   183,   184,
     185,   186,   187,   188,   189,   190,   191,   192,   193,   194,
     195,   196,   197,   198,   199,   200,   201,   202,   203,   204,
     205,   206,   207,   211,   215,   216,   220,   224,   225,   229,
     233,   237,   241,   245,   251,   251,   251,   251,   251,   251,
     251,   255,   256,   257,   258,   262,   263,   267,   268,   272,
     273,   274,   275,   276,   280,   281,   285,   285,   289,   290,
     291,   292,   296,   297,   298,   299,   300,   301,   302,   303,
     304,   308,   308,   312,   313,   314,   315,   319,   319,   323,
     324,   325,   329,   329,   329,   337,   338
};
#endif

/** Accessing symbol of state STATE.  */
#define YY_ACCESSING_SYMBOL(State) YY_CAST (yysymbol_kind_t, yystos[State])

#if 1
/* The user-facing name of the symbol whose (internal) number is
   YYSYMBOL.  No bounds checking.  */
static const char *yysymbol_name (yysymbol_kind_t yysymbol) YY_ATTRIBUTE_UNUSED;

/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "\"end of file\"", "error", "\"invalid token\"", "SYM_BAR", "\"|\"",
  "SYM_AMP", "\"&\"", "\":\"", "\",\"", "\"none\"", "\"nothing\"",
  "\"true\"", "\"false\"", "\"something\"", "\"ok\"", "\"err\"", "\"::\"",
  "SYM_ELLIPSIS", "SYM_ENTRY", "SYM_BANG", "SYM_EQUALS", "SYM_DOT",
  "SYM_AT", "SYM_UNDERSCORE", "KW_SOME", "KW_SRC", "KW_LET", "KW_IN",
  "TOKEN_NAT", "TOKEN_INT", "TOKEN_BIG_NAT", "TOKEN_BIG_INT",
  "TOKEN_RATIONAL", "TOKEN_FLOAT", "TOKEN_DOUBLE", "\"numberino\"",
  "TOKEN_BYTE_BUFFER", "TOKEN_UUID_V4", "TOKEN_UUID_V7", "TOKEN_SHA_HASH",
  "TOKEN_STRING", "TOKEN_ASCII_STRING", "TOKEN_REGEX", "TOKEN_PATH_ITEM",
  "TOKEN_DATE_TIME", "TOKEN_UTC_DATE_TIME", "TOKEN_PLAIN_DATE",
  "TOKEN_PLAIN_TIME", "TOKEN_LOGICAL_TIME", "TOKEN_TICK_TIME",
  "TOKEN_TIMESTAMP", "\"identifier\"", "\"type name\"",
  "\"unspec identifier\"", "'<'", "'>'", "'['", "']'", "'{'", "'}'", "'('",
  "')'", "':'", "$accept", "bsqontypel", "bsqontypel_entry",
  "bsqonnametypel", "bsqonnametypel_entry", "bsqonnominaltype",
  "bsqontermslist", "bsqontupletype", "bsqonrecordtype", "bsqontype",
  "bsqontspec", "bsqonliteral", "bsqonunspecvar", "bsqonidentifier",
  "bsqonscopedidentifier", "bsqonstringof", "bsqonpath",
  "bsqontypeliteral", "bsqonterminal", "bsqon_mapentry", "bsqonvall",
  "bsqonl_entry", "bsqonbracketvalue", "bsqonnamevall", "bsqon_braceval",
  "bsqonnameval_entry", "bsqonbracevalue", "bsqonbracketbracevalue",
  "bsqontypedvalue", "bsqonstructvalue", "bsqonspecialcons", "bsqonval",
  "bsqonroot", YY_NULLPTR
};

static const char *
yysymbol_name (yysymbol_kind_t yysymbol)
{
  return yytname[yysymbol];
}
#endif

#define YYPACT_NINF (-81)

#define yypact_value_is_default(Yyn) \
  ((Yyn) == YYPACT_NINF)

#define YYTABLE_NINF (-1)

#define yytable_value_is_error(Yyn) \
  0

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
static const yytype_int16 yypact[] =
{
     274,    68,   -19,    -6,   -81,   -81,   -30,   -20,   -11,   -81,
     -81,   -81,   -81,   -81,   -81,   -81,   -81,    36,   -81,   -81,
     -81,   -81,    73,    73,   -81,    73,   -81,   -81,   -81,   -81,
     -81,   -81,   -81,   -81,    66,   -81,    57,   220,   166,   275,
      67,   -81,   -81,   -81,   -81,   -81,   -81,   -81,   -81,   -81,
     -81,   -81,   -81,   -81,   -81,   133,   -81,    73,    73,   328,
     328,   328,    73,   118,   118,   118,    15,   -81,    83,     8,
     -32,   118,   -81,   -81,    84,   699,   -81,   -81,   382,   -81,
     139,    -7,    93,   134,   -81,   436,    -3,   -81,   137,   105,
     107,   -81,    73,   -81,   118,   118,    68,    96,    99,   100,
     118,    29,    40,    47,   -81,   118,   -81,   -81,   181,    68,
      -5,   -81,    54,    21,   156,   -81,   113,   -81,    68,   -81,
     490,   -81,   703,   -81,   101,   -81,   544,   -81,   -81,   -81,
     598,   660,   150,    -2,   -81,   -81,   -81,   -81,   -81,   118,
     -81,   -81,   -81,   -81,   -81,   110,     9,    38,   -81,   182,
      90,    90,   -81,   -81,   -81,   -81,    37,    28,   -81,    71,
     165,   -81,   -81,    68,   -81,   -81,   -81,    68,   -81,   184,
      20,   -81,   652,   -81,   -81,   -81,   -81,   -81,   168,   -81,
     -81,   -81,    45,    10,    85,   -81,   -81,   -81,   -81,   236,
      81,   -81,   -81,   -81,   -81,    94,    17,   -81,   -81,   -81,
     -81
};

/* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
   Performed when YYTABLE does not specify something else to do.  Zero
   means the default is an error.  */
static const yytype_int8 yydefact[] =
{
       0,   126,    37,    38,    39,    40,     0,     0,     0,    64,
      41,    42,    43,    44,    45,    46,    47,     0,    48,    49,
      50,    51,    52,    53,    55,    54,    56,    57,    58,    59,
      60,    61,    62,    65,    10,    63,     0,     0,     0,     0,
      74,    75,    76,    77,    78,    79,    80,   122,   111,   112,
     117,   118,   124,   123,   125,     0,   116,     0,     0,     0,
       0,     0,     0,    67,    68,    69,     0,    11,     0,     0,
       0,    34,    35,    36,     0,     0,    89,    97,     0,    86,
       0,    96,     0,    65,   102,     0,     0,    95,    96,     0,
       0,   114,     0,     1,    71,    72,     0,     0,     0,     0,
      70,     0,     0,     0,     3,    27,    28,    29,     0,     0,
       0,    17,     0,     0,     0,    22,     0,     7,     0,    88,
       0,    92,     0,    85,    96,    87,     0,    90,   101,   109,
       0,     0,    65,     0,    94,   100,   107,    66,    12,    73,
     119,   120,   121,     5,    15,     0,     0,     0,     2,     0,
       0,     0,     4,    13,   115,    20,     0,     0,    18,     0,
       0,     6,   113,    84,    82,    93,    91,    83,    81,     0,
       0,   110,     0,   108,    33,    32,    16,    14,    31,    30,
      21,    19,     0,     0,     0,    99,   105,    98,   103,     0,
       0,     9,    25,     8,    23,     0,     0,   106,   104,    26,
      24
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
     -81,   114,   -80,   -81,    77,   -15,   -81,   146,   187,   -68,
     -81,   -81,   -81,   -81,   -81,   -81,   -81,   -81,   -81,   -81,
     -81,   148,   -81,   -81,    80,   142,   -81,    -1,   -81,   -81,
     -81,     2,   -81
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int8 yydefgoto[] =
{
       0,   103,   104,   116,   117,    39,    67,   106,   107,   108,
      74,    40,    41,    42,    43,    44,    45,    46,    47,    77,
      78,    79,    48,    85,    80,    87,    49,    50,    51,    52,
      53,    88,    55
};

/* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule whose
   number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_uint8 yytable[] =
{
      56,   113,    54,   143,    57,   135,   135,    63,    64,   110,
      65,   126,   150,   150,   151,   151,   101,    58,   193,   114,
     150,    71,   151,   148,   150,   193,   151,   115,   187,   152,
      59,   150,   148,   151,   146,   149,   152,   143,    91,    81,
      60,   145,    94,    95,   157,   143,   143,   100,   147,    61,
     127,   105,   155,   191,   105,   156,   136,   173,    68,    62,
      34,    97,    98,    99,    69,   111,    70,    34,   102,   194,
     175,    69,   182,    70,    56,   102,   200,   139,   158,   188,
     124,    56,   178,   179,   144,   181,   195,   105,   105,   187,
      92,   183,    34,   176,   180,    56,    69,   105,    70,    34,
     102,   128,   191,    69,   192,    70,    34,   102,   154,    34,
      69,   120,    70,    69,   102,    70,   196,   162,    86,   126,
      66,    56,   164,    34,    37,    34,    38,    69,   168,    70,
      56,   102,   170,    93,    90,   105,   105,    34,   109,   118,
     198,    69,    34,    70,   105,   102,    69,   125,    70,    37,
     102,    38,   129,   199,   130,   126,   137,   140,   166,   138,
     141,   142,    56,   159,   160,   133,    56,    82,    56,   105,
     172,   174,   184,   151,   190,     2,     3,     4,     5,     6,
       7,     8,    72,   112,   150,   150,   151,   151,    56,   152,
     152,     9,   185,   161,    10,    11,    12,    13,    14,    15,
      16,    17,    18,    19,    20,    21,    22,    23,    24,    25,
      26,    27,    28,    29,    30,    31,    32,    83,    34,    35,
      36,    75,    37,    73,    38,    84,   123,   134,     0,     2,
       3,     4,     5,     6,     7,     8,   153,   177,     0,     0,
      37,     0,    38,   186,   185,     9,     0,     0,    10,    11,
      12,    13,    14,    15,    16,    17,    18,    19,    20,    21,
      22,    23,    24,    25,    26,    27,    28,    29,    30,    31,
      32,    33,    34,    35,    36,     1,    37,    76,    38,     0,
       0,     0,    89,     2,     3,     4,     5,     6,     7,     8,
       0,    90,    37,     0,    38,   197,     0,     0,     0,     9,
       0,     0,    10,    11,    12,    13,    14,    15,    16,    17,
      18,    19,    20,    21,    22,    23,    24,    25,    26,    27,
      28,    29,    30,    31,    32,    33,    34,    35,    36,    96,
      37,    37,    38,    38,     0,     0,     0,     2,     3,     4,
       5,     6,     7,     8,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     9,     0,     0,    10,    11,    12,    13,
      14,    15,    16,    17,    18,    19,    20,    21,    22,    23,
      24,    25,    26,    27,    28,    29,    30,    31,    32,    33,
      34,    35,    36,   122,    37,     0,    38,     0,     0,     0,
       0,     2,     3,     4,     5,     6,     7,     8,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     9,     0,     0,
      10,    11,    12,    13,    14,    15,    16,    17,    18,    19,
      20,    21,    22,    23,    24,    25,    26,    27,    28,    29,
      30,    31,    32,    33,    34,    35,    36,   131,    37,     0,
      38,     0,     0,     0,     0,     2,     3,     4,     5,     6,
       7,     8,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     9,     0,     0,    10,    11,    12,    13,    14,    15,
      16,    17,    18,    19,    20,    21,    22,    23,    24,    25,
      26,    27,    28,    29,    30,    31,    32,   132,    34,    35,
      36,   163,    37,     0,    38,     0,     0,     0,     0,     2,
       3,     4,     5,     6,     7,     8,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     9,     0,     0,    10,    11,
      12,    13,    14,    15,    16,    17,    18,    19,    20,    21,
      22,    23,    24,    25,    26,    27,    28,    29,    30,    31,
      32,    33,    34,    35,    36,   167,    37,     0,    38,     0,
       0,     0,     0,     2,     3,     4,     5,     6,     7,     8,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     9,
       0,     0,    10,    11,    12,    13,    14,    15,    16,    17,
      18,    19,    20,    21,    22,    23,    24,    25,    26,    27,
      28,    29,    30,    31,    32,    33,    34,    35,    36,   169,
      37,     0,    38,     0,     0,     0,     0,     2,     3,     4,
       5,     6,     7,     8,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     9,     0,     0,    10,    11,    12,    13,
      14,    15,    16,    17,    18,    19,    20,    21,    22,    23,
      24,    25,    26,    27,    28,    29,    30,    31,    32,    33,
      34,    35,    36,   189,    37,     0,    38,     0,     0,     0,
       0,     2,     3,     4,     5,     6,     7,     8,   128,     0,
       0,     0,     0,     0,     0,     0,     0,     9,   120,     0,
      10,    11,    12,    13,    14,    15,    16,    17,    18,    19,
      20,    21,    22,    23,    24,    25,    26,    27,    28,    29,
      30,    31,    32,    33,    34,    35,    36,   119,    37,     0,
      38,   119,     0,     0,     0,     0,    37,   120,    38,   171,
       0,   120,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,    37,   121,    38,     0,    37,
     165,    38
};

static const yytype_int16 yycheck[] =
{
       1,    69,     0,     8,    23,     8,     8,    22,    23,     1,
      25,    18,     3,     3,     5,     5,     1,    23,     8,    51,
       3,    36,     5,   103,     3,     8,     5,    59,     8,     8,
      60,     3,   112,     5,   102,   103,     8,     8,    39,    37,
      60,     1,    57,    58,   112,     8,     8,    62,     1,    60,
      57,    66,    57,     8,    69,     1,    59,    59,     1,    23,
      52,    59,    60,    61,    56,    57,    58,    52,    60,    59,
      61,    56,     1,    58,    75,    60,    59,    92,    57,    59,
      78,    82,   150,   151,    55,    57,     1,   102,   103,     8,
      23,   159,    52,    55,    57,    96,    56,   112,    58,    52,
      60,     8,     8,    56,    59,    58,    52,    60,   109,    52,
      56,    18,    58,    56,    60,    58,   184,   118,    38,    18,
      54,   122,   120,    52,    56,    52,    58,    56,   126,    58,
     131,    60,   130,     0,    16,   150,   151,    52,    55,    55,
      59,    56,    52,    58,   159,    60,    56,     8,    58,    56,
      60,    58,    59,    59,    20,    18,    51,    61,    57,    52,
      61,    61,   163,     7,    51,    85,   167,     1,   169,   184,
      20,    61,     7,     5,   172,     9,    10,    11,    12,    13,
      14,    15,    36,    69,     3,     3,     5,     5,   189,     8,
       8,    25,     8,   116,    28,    29,    30,    31,    32,    33,
      34,    35,    36,    37,    38,    39,    40,    41,    42,    43,
      44,    45,    46,    47,    48,    49,    50,    51,    52,    53,
      54,     1,    56,    36,    58,    59,    78,    85,    -1,     9,
      10,    11,    12,    13,    14,    15,    55,    55,    -1,    -1,
      56,    -1,    58,    59,     8,    25,    -1,    -1,    28,    29,
      30,    31,    32,    33,    34,    35,    36,    37,    38,    39,
      40,    41,    42,    43,    44,    45,    46,    47,    48,    49,
      50,    51,    52,    53,    54,     1,    56,    57,    58,    -1,
      -1,    -1,     7,     9,    10,    11,    12,    13,    14,    15,
      -1,    16,    56,    -1,    58,    59,    -1,    -1,    -1,    25,
      -1,    -1,    28,    29,    30,    31,    32,    33,    34,    35,
      36,    37,    38,    39,    40,    41,    42,    43,    44,    45,
      46,    47,    48,    49,    50,    51,    52,    53,    54,     1,
      56,    56,    58,    58,    -1,    -1,    -1,     9,    10,    11,
      12,    13,    14,    15,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    25,    -1,    -1,    28,    29,    30,    31,
      32,    33,    34,    35,    36,    37,    38,    39,    40,    41,
      42,    43,    44,    45,    46,    47,    48,    49,    50,    51,
      52,    53,    54,     1,    56,    -1,    58,    -1,    -1,    -1,
      -1,     9,    10,    11,    12,    13,    14,    15,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    25,    -1,    -1,
      28,    29,    30,    31,    32,    33,    34,    35,    36,    37,
      38,    39,    40,    41,    42,    43,    44,    45,    46,    47,
      48,    49,    50,    51,    52,    53,    54,     1,    56,    -1,
      58,    -1,    -1,    -1,    -1,     9,    10,    11,    12,    13,
      14,    15,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    25,    -1,    -1,    28,    29,    30,    31,    32,    33,
      34,    35,    36,    37,    38,    39,    40,    41,    42,    43,
      44,    45,    46,    47,    48,    49,    50,    51,    52,    53,
      54,     1,    56,    -1,    58,    -1,    -1,    -1,    -1,     9,
      10,    11,    12,    13,    14,    15,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    25,    -1,    -1,    28,    29,
      30,    31,    32,    33,    34,    35,    36,    37,    38,    39,
      40,    41,    42,    43,    44,    45,    46,    47,    48,    49,
      50,    51,    52,    53,    54,     1,    56,    -1,    58,    -1,
      -1,    -1,    -1,     9,    10,    11,    12,    13,    14,    15,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    25,
      -1,    -1,    28,    29,    30,    31,    32,    33,    34,    35,
      36,    37,    38,    39,    40,    41,    42,    43,    44,    45,
      46,    47,    48,    49,    50,    51,    52,    53,    54,     1,
      56,    -1,    58,    -1,    -1,    -1,    -1,     9,    10,    11,
      12,    13,    14,    15,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    25,    -1,    -1,    28,    29,    30,    31,
      32,    33,    34,    35,    36,    37,    38,    39,    40,    41,
      42,    43,    44,    45,    46,    47,    48,    49,    50,    51,
      52,    53,    54,     1,    56,    -1,    58,    -1,    -1,    -1,
      -1,     9,    10,    11,    12,    13,    14,    15,     8,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    25,    18,    -1,
      28,    29,    30,    31,    32,    33,    34,    35,    36,    37,
      38,    39,    40,    41,    42,    43,    44,    45,    46,    47,
      48,    49,    50,    51,    52,    53,    54,     8,    56,    -1,
      58,     8,    -1,    -1,    -1,    -1,    56,    18,    58,    59,
      -1,    18,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    56,    57,    58,    -1,    56,
      57,    58
};

/* YYSTOS[STATE-NUM] -- The symbol kind of the accessing symbol of
   state STATE-NUM.  */
static const yytype_int8 yystos[] =
{
       0,     1,     9,    10,    11,    12,    13,    14,    15,    25,
      28,    29,    30,    31,    32,    33,    34,    35,    36,    37,
      38,    39,    40,    41,    42,    43,    44,    45,    46,    47,
      48,    49,    50,    51,    52,    53,    54,    56,    58,    68,
      74,    75,    76,    77,    78,    79,    80,    81,    85,    89,
      90,    91,    92,    93,    94,    95,    90,    23,    23,    60,
      60,    60,    23,    68,    68,    68,    54,    69,     1,    56,
      58,    68,    70,    71,    73,     1,    57,    82,    83,    84,
      87,    94,     1,    51,    59,    86,    87,    88,    94,     7,
      16,    90,    23,     0,    68,    68,     1,    94,    94,    94,
      68,     1,    60,    64,    65,    68,    70,    71,    72,    55,
       1,    57,    64,    72,    51,    59,    66,    67,    55,     8,
      18,    57,     1,    84,    94,     8,    18,    57,     8,    59,
      20,     1,    51,    87,    88,     8,    59,    51,    52,    68,
      61,    61,    61,     8,    55,     1,    72,     1,    65,    72,
       3,     5,     8,    55,    90,    57,     1,    72,    57,     7,
      51,    67,    90,     1,    94,    57,    57,     1,    94,     1,
      94,    59,    20,    59,    61,    61,    55,    55,    72,    72,
      57,    57,     1,    72,     7,     8,    59,     8,    59,     1,
      94,     8,    59,     8,    59,     1,    72,    59,    59,    59,
      59
};

/* YYR1[RULE-NUM] -- Symbol kind of the left-hand side of rule RULE-NUM.  */
static const yytype_int8 yyr1[] =
{
       0,    63,    64,    64,    65,    65,    66,    66,    67,    67,
      68,    68,    68,    69,    69,    69,    69,    70,    70,    70,
      70,    70,    71,    71,    71,    71,    71,    72,    72,    72,
      72,    72,    72,    72,    73,    73,    73,    74,    74,    74,
      74,    74,    74,    74,    74,    74,    74,    74,    74,    74,
      74,    74,    74,    74,    74,    74,    74,    74,    74,    74,
      74,    74,    74,    75,    76,    76,    77,    78,    78,    79,
      80,    80,    80,    80,    81,    81,    81,    81,    81,    81,
      81,    82,    82,    82,    82,    83,    83,    84,    84,    85,
      85,    85,    85,    85,    86,    86,    87,    87,    88,    88,
      88,    88,    89,    89,    89,    89,    89,    89,    89,    89,
      89,    90,    90,    91,    91,    91,    91,    92,    92,    93,
      93,    93,    94,    94,    94,    95,    95
};

/* YYR2[RULE-NUM] -- Number of symbols on the right-hand side of rule RULE-NUM.  */
static const yytype_int8 yyr2[] =
{
       0,     2,     2,     1,     2,     2,     2,     1,     4,     4,
       1,     2,     3,     3,     4,     3,     4,     2,     3,     4,
       3,     4,     2,     5,     6,     5,     6,     1,     1,     1,
       3,     3,     3,     3,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     1,     1,     1,     1,
       1,     1,     1,     1,     1,     1,     3,     2,     2,     2,
       3,     3,     3,     3,     1,     1,     1,     1,     1,     1,
       1,     3,     3,     3,     3,     2,     1,     2,     2,     2,
       3,     4,     3,     4,     2,     1,     1,     1,     4,     4,
       2,     2,     2,     5,     6,     5,     6,     3,     4,     3,
       4,     1,     1,     4,     2,     4,     2,     1,     1,     4,
       4,     4,     1,     1,     1,     1,     1
};


enum { YYENOMEM = -2 };

#define yyerrok         (yyerrstatus = 0)
#define yyclearin       (yychar = YYEMPTY)

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab
#define YYNOMEM         goto yyexhaustedlab


#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)                                    \
  do                                                              \
    if (yychar == YYEMPTY)                                        \
      {                                                           \
        yychar = (Token);                                         \
        yylval = (Value);                                         \
        YYPOPSTACK (yylen);                                       \
        yystate = *yyssp;                                         \
        goto yybackup;                                            \
      }                                                           \
    else                                                          \
      {                                                           \
        yyerror (YY_("syntax error: cannot back up")); \
        YYERROR;                                                  \
      }                                                           \
  while (0)

/* Backward compatibility with an undocumented macro.
   Use YYerror or YYUNDEF. */
#define YYERRCODE YYUNDEF

/* YYLLOC_DEFAULT -- Set CURRENT to span from RHS[1] to RHS[N].
   If N is 0, then set CURRENT to the empty location which ends
   the previous symbol: RHS[0] (always defined).  */

#ifndef YYLLOC_DEFAULT
# define YYLLOC_DEFAULT(Current, Rhs, N)                                \
    do                                                                  \
      if (N)                                                            \
        {                                                               \
          (Current).first_line   = YYRHSLOC (Rhs, 1).first_line;        \
          (Current).first_column = YYRHSLOC (Rhs, 1).first_column;      \
          (Current).last_line    = YYRHSLOC (Rhs, N).last_line;         \
          (Current).last_column  = YYRHSLOC (Rhs, N).last_column;       \
        }                                                               \
      else                                                              \
        {                                                               \
          (Current).first_line   = (Current).last_line   =              \
            YYRHSLOC (Rhs, 0).last_line;                                \
          (Current).first_column = (Current).last_column =              \
            YYRHSLOC (Rhs, 0).last_column;                              \
        }                                                               \
    while (0)
#endif

#define YYRHSLOC(Rhs, K) ((Rhs)[K])


/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)                        \
do {                                            \
  if (yydebug)                                  \
    YYFPRINTF Args;                             \
} while (0)


/* YYLOCATION_PRINT -- Print the location on the stream.
   This macro was not mandated originally: define only if we know
   we won't break user code: when these are the locations we know.  */

# ifndef YYLOCATION_PRINT

#  if defined YY_LOCATION_PRINT

   /* Temporary convenience wrapper in case some people defined the
      undocumented and private YY_LOCATION_PRINT macros.  */
#   define YYLOCATION_PRINT(File, Loc)  YY_LOCATION_PRINT(File, *(Loc))

#  elif defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL

/* Print *YYLOCP on YYO.  Private, do not rely on its existence. */

YY_ATTRIBUTE_UNUSED
static int
yy_location_print_ (FILE *yyo, YYLTYPE const * const yylocp)
{
  int res = 0;
  int end_col = 0 != yylocp->last_column ? yylocp->last_column - 1 : 0;
  if (0 <= yylocp->first_line)
    {
      res += YYFPRINTF (yyo, "%d", yylocp->first_line);
      if (0 <= yylocp->first_column)
        res += YYFPRINTF (yyo, ".%d", yylocp->first_column);
    }
  if (0 <= yylocp->last_line)
    {
      if (yylocp->first_line < yylocp->last_line)
        {
          res += YYFPRINTF (yyo, "-%d", yylocp->last_line);
          if (0 <= end_col)
            res += YYFPRINTF (yyo, ".%d", end_col);
        }
      else if (0 <= end_col && yylocp->first_column < end_col)
        res += YYFPRINTF (yyo, "-%d", end_col);
    }
  return res;
}

#   define YYLOCATION_PRINT  yy_location_print_

    /* Temporary convenience wrapper in case some people defined the
       undocumented and private YY_LOCATION_PRINT macros.  */
#   define YY_LOCATION_PRINT(File, Loc)  YYLOCATION_PRINT(File, &(Loc))

#  else

#   define YYLOCATION_PRINT(File, Loc) ((void) 0)
    /* Temporary convenience wrapper in case some people defined the
       undocumented and private YY_LOCATION_PRINT macros.  */
#   define YY_LOCATION_PRINT  YYLOCATION_PRINT

#  endif
# endif /* !defined YYLOCATION_PRINT */


# define YY_SYMBOL_PRINT(Title, Kind, Value, Location)                    \
do {                                                                      \
  if (yydebug)                                                            \
    {                                                                     \
      YYFPRINTF (stderr, "%s ", Title);                                   \
      yy_symbol_print (stderr,                                            \
                  Kind, Value, Location); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*-----------------------------------.
| Print this symbol's value on YYO.  |
`-----------------------------------*/

static void
yy_symbol_value_print (FILE *yyo,
                       yysymbol_kind_t yykind, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp)
{
  FILE *yyoutput = yyo;
  YY_USE (yyoutput);
  YY_USE (yylocationp);
  if (!yyvaluep)
    return;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YY_USE (yykind);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}


/*---------------------------.
| Print this symbol on YYO.  |
`---------------------------*/

static void
yy_symbol_print (FILE *yyo,
                 yysymbol_kind_t yykind, YYSTYPE const * const yyvaluep, YYLTYPE const * const yylocationp)
{
  YYFPRINTF (yyo, "%s %s (",
             yykind < YYNTOKENS ? "token" : "nterm", yysymbol_name (yykind));

  YYLOCATION_PRINT (yyo, yylocationp);
  YYFPRINTF (yyo, ": ");
  yy_symbol_value_print (yyo, yykind, yyvaluep, yylocationp);
  YYFPRINTF (yyo, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

static void
yy_stack_print (yy_state_t *yybottom, yy_state_t *yytop)
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)                            \
do {                                                            \
  if (yydebug)                                                  \
    yy_stack_print ((Bottom), (Top));                           \
} while (0)


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

static void
yy_reduce_print (yy_state_t *yyssp, YYSTYPE *yyvsp, YYLTYPE *yylsp,
                 int yyrule)
{
  int yylno = yyrline[yyrule];
  int yynrhs = yyr2[yyrule];
  int yyi;
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %d):\n",
             yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr,
                       YY_ACCESSING_SYMBOL (+yyssp[yyi + 1 - yynrhs]),
                       &yyvsp[(yyi + 1) - (yynrhs)],
                       &(yylsp[(yyi + 1) - (yynrhs)]));
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print (yyssp, yyvsp, yylsp, Rule); \
} while (0)

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args) ((void) 0)
# define YY_SYMBOL_PRINT(Title, Kind, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif


/* Context of a parse error.  */
typedef struct
{
  yy_state_t *yyssp;
  yysymbol_kind_t yytoken;
  YYLTYPE *yylloc;
} yypcontext_t;

/* Put in YYARG at most YYARGN of the expected tokens given the
   current YYCTX, and return the number of tokens stored in YYARG.  If
   YYARG is null, return the number of expected tokens (guaranteed to
   be less than YYNTOKENS).  Return YYENOMEM on memory exhaustion.
   Return 0 if there are more than YYARGN expected tokens, yet fill
   YYARG up to YYARGN. */
static int
yypcontext_expected_tokens (const yypcontext_t *yyctx,
                            yysymbol_kind_t yyarg[], int yyargn)
{
  /* Actual size of YYARG. */
  int yycount = 0;
  int yyn = yypact[+*yyctx->yyssp];
  if (!yypact_value_is_default (yyn))
    {
      /* Start YYX at -YYN if negative to avoid negative indexes in
         YYCHECK.  In other words, skip the first -YYN actions for
         this state because they are default actions.  */
      int yyxbegin = yyn < 0 ? -yyn : 0;
      /* Stay within bounds of both yycheck and yytname.  */
      int yychecklim = YYLAST - yyn + 1;
      int yyxend = yychecklim < YYNTOKENS ? yychecklim : YYNTOKENS;
      int yyx;
      for (yyx = yyxbegin; yyx < yyxend; ++yyx)
        if (yycheck[yyx + yyn] == yyx && yyx != YYSYMBOL_YYerror
            && !yytable_value_is_error (yytable[yyx + yyn]))
          {
            if (!yyarg)
              ++yycount;
            else if (yycount == yyargn)
              return 0;
            else
              yyarg[yycount++] = YY_CAST (yysymbol_kind_t, yyx);
          }
    }
  if (yyarg && yycount == 0 && 0 < yyargn)
    yyarg[0] = YYSYMBOL_YYEMPTY;
  return yycount;
}




#ifndef yystrlen
# if defined __GLIBC__ && defined _STRING_H
#  define yystrlen(S) (YY_CAST (YYPTRDIFF_T, strlen (S)))
# else
/* Return the length of YYSTR.  */
static YYPTRDIFF_T
yystrlen (const char *yystr)
{
  YYPTRDIFF_T yylen;
  for (yylen = 0; yystr[yylen]; yylen++)
    continue;
  return yylen;
}
# endif
#endif

#ifndef yystpcpy
# if defined __GLIBC__ && defined _STRING_H && defined _GNU_SOURCE
#  define yystpcpy stpcpy
# else
/* Copy YYSRC to YYDEST, returning the address of the terminating '\0' in
   YYDEST.  */
static char *
yystpcpy (char *yydest, const char *yysrc)
{
  char *yyd = yydest;
  const char *yys = yysrc;

  while ((*yyd++ = *yys++) != '\0')
    continue;

  return yyd - 1;
}
# endif
#endif

#ifndef yytnamerr
/* Copy to YYRES the contents of YYSTR after stripping away unnecessary
   quotes and backslashes, so that it's suitable for yyerror.  The
   heuristic is that double-quoting is unnecessary unless the string
   contains an apostrophe, a comma, or backslash (other than
   backslash-backslash).  YYSTR is taken from yytname.  If YYRES is
   null, do not copy; instead, return the length of what the result
   would have been.  */
static YYPTRDIFF_T
yytnamerr (char *yyres, const char *yystr)
{
  if (*yystr == '"')
    {
      YYPTRDIFF_T yyn = 0;
      char const *yyp = yystr;
      for (;;)
        switch (*++yyp)
          {
          case '\'':
          case ',':
            goto do_not_strip_quotes;

          case '\\':
            if (*++yyp != '\\')
              goto do_not_strip_quotes;
            else
              goto append;

          append:
          default:
            if (yyres)
              yyres[yyn] = *yyp;
            yyn++;
            break;

          case '"':
            if (yyres)
              yyres[yyn] = '\0';
            return yyn;
          }
    do_not_strip_quotes: ;
    }

  if (yyres)
    return yystpcpy (yyres, yystr) - yyres;
  else
    return yystrlen (yystr);
}
#endif


static int
yy_syntax_error_arguments (const yypcontext_t *yyctx,
                           yysymbol_kind_t yyarg[], int yyargn)
{
  /* Actual size of YYARG. */
  int yycount = 0;
  /* There are many possibilities here to consider:
     - If this state is a consistent state with a default action, then
       the only way this function was invoked is if the default action
       is an error action.  In that case, don't check for expected
       tokens because there are none.
     - The only way there can be no lookahead present (in yychar) is if
       this state is a consistent state with a default action.  Thus,
       detecting the absence of a lookahead is sufficient to determine
       that there is no unexpected or expected token to report.  In that
       case, just report a simple "syntax error".
     - Don't assume there isn't a lookahead just because this state is a
       consistent state with a default action.  There might have been a
       previous inconsistent state, consistent state with a non-default
       action, or user semantic action that manipulated yychar.
     - Of course, the expected token list depends on states to have
       correct lookahead information, and it depends on the parser not
       to perform extra reductions after fetching a lookahead from the
       scanner and before detecting a syntax error.  Thus, state merging
       (from LALR or IELR) and default reductions corrupt the expected
       token list.  However, the list is correct for canonical LR with
       one exception: it will still contain any token that will not be
       accepted due to an error action in a later state.
  */
  if (yyctx->yytoken != YYSYMBOL_YYEMPTY)
    {
      int yyn;
      if (yyarg)
        yyarg[yycount] = yyctx->yytoken;
      ++yycount;
      yyn = yypcontext_expected_tokens (yyctx,
                                        yyarg ? yyarg + 1 : yyarg, yyargn - 1);
      if (yyn == YYENOMEM)
        return YYENOMEM;
      else
        yycount += yyn;
    }
  return yycount;
}

/* Copy into *YYMSG, which is of size *YYMSG_ALLOC, an error message
   about the unexpected token YYTOKEN for the state stack whose top is
   YYSSP.

   Return 0 if *YYMSG was successfully written.  Return -1 if *YYMSG is
   not large enough to hold the message.  In that case, also set
   *YYMSG_ALLOC to the required number of bytes.  Return YYENOMEM if the
   required number of bytes is too large to store.  */
static int
yysyntax_error (YYPTRDIFF_T *yymsg_alloc, char **yymsg,
                const yypcontext_t *yyctx)
{
  enum { YYARGS_MAX = 5 };
  /* Internationalized format string. */
  const char *yyformat = YY_NULLPTR;
  /* Arguments of yyformat: reported tokens (one for the "unexpected",
     one per "expected"). */
  yysymbol_kind_t yyarg[YYARGS_MAX];
  /* Cumulated lengths of YYARG.  */
  YYPTRDIFF_T yysize = 0;

  /* Actual size of YYARG. */
  int yycount = yy_syntax_error_arguments (yyctx, yyarg, YYARGS_MAX);
  if (yycount == YYENOMEM)
    return YYENOMEM;

  switch (yycount)
    {
#define YYCASE_(N, S)                       \
      case N:                               \
        yyformat = S;                       \
        break
    default: /* Avoid compiler warnings. */
      YYCASE_(0, YY_("syntax error"));
      YYCASE_(1, YY_("syntax error, unexpected %s"));
      YYCASE_(2, YY_("syntax error, unexpected %s, expecting %s"));
      YYCASE_(3, YY_("syntax error, unexpected %s, expecting %s or %s"));
      YYCASE_(4, YY_("syntax error, unexpected %s, expecting %s or %s or %s"));
      YYCASE_(5, YY_("syntax error, unexpected %s, expecting %s or %s or %s or %s"));
#undef YYCASE_
    }

  /* Compute error message size.  Don't count the "%s"s, but reserve
     room for the terminator.  */
  yysize = yystrlen (yyformat) - 2 * yycount + 1;
  {
    int yyi;
    for (yyi = 0; yyi < yycount; ++yyi)
      {
        YYPTRDIFF_T yysize1
          = yysize + yytnamerr (YY_NULLPTR, yytname[yyarg[yyi]]);
        if (yysize <= yysize1 && yysize1 <= YYSTACK_ALLOC_MAXIMUM)
          yysize = yysize1;
        else
          return YYENOMEM;
      }
  }

  if (*yymsg_alloc < yysize)
    {
      *yymsg_alloc = 2 * yysize;
      if (! (yysize <= *yymsg_alloc
             && *yymsg_alloc <= YYSTACK_ALLOC_MAXIMUM))
        *yymsg_alloc = YYSTACK_ALLOC_MAXIMUM;
      return -1;
    }

  /* Avoid sprintf, as that infringes on the user's name space.
     Don't have undefined behavior even if the translation
     produced a string with the wrong number of "%s"s.  */
  {
    char *yyp = *yymsg;
    int yyi = 0;
    while ((*yyp = *yyformat) != '\0')
      if (*yyp == '%' && yyformat[1] == 's' && yyi < yycount)
        {
          yyp += yytnamerr (yyp, yytname[yyarg[yyi++]]);
          yyformat += 2;
        }
      else
        {
          ++yyp;
          ++yyformat;
        }
  }
  return 0;
}


/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
yydestruct (const char *yymsg,
            yysymbol_kind_t yykind, YYSTYPE *yyvaluep, YYLTYPE *yylocationp)
{
  YY_USE (yyvaluep);
  YY_USE (yylocationp);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yykind, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YY_USE (yykind);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}


/* Lookahead token kind.  */
int yychar;

/* The semantic value of the lookahead symbol.  */
YYSTYPE yylval;
/* Location data for the lookahead symbol.  */
YYLTYPE yylloc
# if defined YYLTYPE_IS_TRIVIAL && YYLTYPE_IS_TRIVIAL
  = { 1, 1, 1, 1 }
# endif
;
/* Number of syntax errors so far.  */
int yynerrs;




/*----------.
| yyparse.  |
`----------*/

int
yyparse (void)
{
    yy_state_fast_t yystate = 0;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus = 0;

    /* Refer to the stacks through separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* Their size.  */
    YYPTRDIFF_T yystacksize = YYINITDEPTH;

    /* The state stack: array, bottom, top.  */
    yy_state_t yyssa[YYINITDEPTH];
    yy_state_t *yyss = yyssa;
    yy_state_t *yyssp = yyss;

    /* The semantic value stack: array, bottom, top.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs = yyvsa;
    YYSTYPE *yyvsp = yyvs;

    /* The location stack: array, bottom, top.  */
    YYLTYPE yylsa[YYINITDEPTH];
    YYLTYPE *yyls = yylsa;
    YYLTYPE *yylsp = yyls;

  int yyn;
  /* The return value of yyparse.  */
  int yyresult;
  /* Lookahead symbol kind.  */
  yysymbol_kind_t yytoken = YYSYMBOL_YYEMPTY;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;
  YYLTYPE yyloc;

  /* The locations where the error started and ended.  */
  YYLTYPE yyerror_range[3];

  /* Buffer for error messages, and its allocated size.  */
  char yymsgbuf[128];
  char *yymsg = yymsgbuf;
  YYPTRDIFF_T yymsg_alloc = sizeof yymsgbuf;

#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N), yylsp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yychar = YYEMPTY; /* Cause a token to be read.  */

  yylsp[0] = yylloc;
  goto yysetstate;


/*------------------------------------------------------------.
| yynewstate -- push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;


/*--------------------------------------------------------------------.
| yysetstate -- set current state (the top of the stack) to yystate.  |
`--------------------------------------------------------------------*/
yysetstate:
  YYDPRINTF ((stderr, "Entering state %d\n", yystate));
  YY_ASSERT (0 <= yystate && yystate < YYNSTATES);
  YY_IGNORE_USELESS_CAST_BEGIN
  *yyssp = YY_CAST (yy_state_t, yystate);
  YY_IGNORE_USELESS_CAST_END
  YY_STACK_PRINT (yyss, yyssp);

  if (yyss + yystacksize - 1 <= yyssp)
#if !defined yyoverflow && !defined YYSTACK_RELOCATE
    YYNOMEM;
#else
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYPTRDIFF_T yysize = yyssp - yyss + 1;

# if defined yyoverflow
      {
        /* Give user a chance to reallocate the stack.  Use copies of
           these so that the &'s don't force the real ones into
           memory.  */
        yy_state_t *yyss1 = yyss;
        YYSTYPE *yyvs1 = yyvs;
        YYLTYPE *yyls1 = yyls;

        /* Each stack pointer address is followed by the size of the
           data in use in that stack, in bytes.  This used to be a
           conditional around just the two extra args, but that might
           be undefined if yyoverflow is a macro.  */
        yyoverflow (YY_("memory exhausted"),
                    &yyss1, yysize * YYSIZEOF (*yyssp),
                    &yyvs1, yysize * YYSIZEOF (*yyvsp),
                    &yyls1, yysize * YYSIZEOF (*yylsp),
                    &yystacksize);
        yyss = yyss1;
        yyvs = yyvs1;
        yyls = yyls1;
      }
# else /* defined YYSTACK_RELOCATE */
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
        YYNOMEM;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
        yystacksize = YYMAXDEPTH;

      {
        yy_state_t *yyss1 = yyss;
        union yyalloc *yyptr =
          YY_CAST (union yyalloc *,
                   YYSTACK_ALLOC (YY_CAST (YYSIZE_T, YYSTACK_BYTES (yystacksize))));
        if (! yyptr)
          YYNOMEM;
        YYSTACK_RELOCATE (yyss_alloc, yyss);
        YYSTACK_RELOCATE (yyvs_alloc, yyvs);
        YYSTACK_RELOCATE (yyls_alloc, yyls);
#  undef YYSTACK_RELOCATE
        if (yyss1 != yyssa)
          YYSTACK_FREE (yyss1);
      }
# endif

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;
      yylsp = yyls + yysize - 1;

      YY_IGNORE_USELESS_CAST_BEGIN
      YYDPRINTF ((stderr, "Stack size increased to %ld\n",
                  YY_CAST (long, yystacksize)));
      YY_IGNORE_USELESS_CAST_END

      if (yyss + yystacksize - 1 <= yyssp)
        YYABORT;
    }
#endif /* !defined yyoverflow && !defined YYSTACK_RELOCATE */


  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;


/*-----------.
| yybackup.  |
`-----------*/
yybackup:
  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yypact_value_is_default (yyn))
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either empty, or end-of-input, or a valid lookahead.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token\n"));
      yychar = yylex ();
    }

  if (yychar <= YYEOF)
    {
      yychar = YYEOF;
      yytoken = YYSYMBOL_YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else if (yychar == YYerror)
    {
      /* The scanner already issued an error message, process directly
         to error recovery.  But do not keep the error token as
         lookahead, it is too special and may lead us to an endless
         loop in error recovery. */
      yychar = YYUNDEF;
      yytoken = YYSYMBOL_YYerror;
      yyerror_range[1] = yylloc;
      goto yyerrlab1;
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yytable_value_is_error (yyn))
        goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);
  yystate = yyn;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END
  *++yylsp = yylloc;

  /* Discard the shifted token.  */
  yychar = YYEMPTY;
  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     '$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];

  /* Default location. */
  YYLLOC_DEFAULT (yyloc, (yylsp - yylen), yylen);
  yyerror_range[1] = yyloc;
  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {
  case 2: /* bsqontypel: bsqontypel bsqontypel_entry  */
#line 113 "bsqon.y"
                               { (yyval.bsqon_t_list) = BSQON_TYPE_AST_ListCons((yyvsp[0].bsqon_t), (yyvsp[-1].bsqon_t_list)); }
#line 1835 "bsqon.tab.c"
    break;

  case 3: /* bsqontypel: bsqontypel_entry  */
#line 114 "bsqon.y"
                      { (yyval.bsqon_t_list) = BSQON_TYPE_AST_ListCons((yyvsp[0].bsqon_t), NULL); }
#line 1841 "bsqon.tab.c"
    break;

  case 4: /* bsqontypel_entry: bsqontype ","  */
#line 118 "bsqon.y"
                       { (yyval.bsqon_t) = (yyvsp[-1].bsqon_t); }
#line 1847 "bsqon.tab.c"
    break;

  case 5: /* bsqontypel_entry: error ","  */
#line 119 "bsqon.y"
                     { (yyval.bsqon_t) = BSQON_TYPE_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1]))); yyerrok; }
#line 1853 "bsqon.tab.c"
    break;

  case 6: /* bsqonnametypel: bsqonnametypel bsqonnametypel_entry  */
#line 123 "bsqon.y"
                                       { (yyval.bsqon_t_namedlist) = BSQON_TYPE_AST_NamedListCons((yyvsp[0].bsqon_t_nametypel_entry), (yyvsp[-1].bsqon_t_namedlist)); }
#line 1859 "bsqon.tab.c"
    break;

  case 7: /* bsqonnametypel: bsqonnametypel_entry  */
#line 124 "bsqon.y"
                          { (yyval.bsqon_t_namedlist) = BSQON_TYPE_AST_NamedListCons((yyvsp[0].bsqon_t_nametypel_entry), NULL); }
#line 1865 "bsqon.tab.c"
    break;

  case 8: /* bsqonnametypel_entry: "identifier" ":" bsqontype ","  */
#line 128 "bsqon.y"
                                                  { (yyval.bsqon_t_nametypel_entry) = BSQON_TYPE_AST_NamedListEntryCreate((yyvsp[-3].str), (yyvsp[-1].bsqon_t)); }
#line 1871 "bsqon.tab.c"
    break;

  case 9: /* bsqonnametypel_entry: "identifier" ":" error ","  */
#line 129 "bsqon.y"
                                                { (yyval.bsqon_t_nametypel_entry) = BSQON_TYPE_AST_NamedListEntryCreate((yyvsp[-3].str), BSQON_TYPE_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1])))); yyerrok; }
#line 1877 "bsqon.tab.c"
    break;

  case 10: /* bsqonnominaltype: "type name"  */
#line 133 "bsqon.y"
                        { (yyval.bsqon_t) = BSQON_AST_NominalNodeCreate((yyvsp[0].str), NULL); }
#line 1883 "bsqon.tab.c"
    break;

  case 11: /* bsqonnominaltype: "type name" bsqontermslist  */
#line 134 "bsqon.y"
                                         { (yyval.bsqon_t) = BSQON_AST_NominalNodeCreate((yyvsp[-1].str), (yyvsp[0].bsqon_t_list)); }
#line 1889 "bsqon.tab.c"
    break;

  case 12: /* bsqonnominaltype: bsqonnominaltype "::" "type name"  */
#line 135 "bsqon.y"
                                                            { (yyval.bsqon_t) = BSQON_AST_NominalExtNodeCreate(BSQON_AST_asNominalNode((yyvsp[-2].bsqon_t)), (yyvsp[0].str)); }
#line 1895 "bsqon.tab.c"
    break;

  case 13: /* bsqontermslist: '<' bsqontype '>'  */
#line 139 "bsqon.y"
                     { (yyval.bsqon_t_list) = BSQON_TYPE_AST_ListCons((yyvsp[-1].bsqon_t), NULL); }
#line 1901 "bsqon.tab.c"
    break;

  case 14: /* bsqontermslist: '<' bsqontypel bsqontype '>'  */
#line 140 "bsqon.y"
                                  { (yyval.bsqon_t_list) = BSQON_TYPE_AST_ListCompleteParse(BSQON_TYPE_AST_ListCons((yyvsp[-1].bsqon_t), (yyvsp[-2].bsqon_t_list))); }
#line 1907 "bsqon.tab.c"
    break;

  case 15: /* bsqontermslist: '<' error '>'  */
#line 141 "bsqon.y"
                   { (yyval.bsqon_t_list) = BSQON_TYPE_AST_ListCons(BSQON_TYPE_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1]))), NULL); yyerrok; }
#line 1913 "bsqon.tab.c"
    break;

  case 16: /* bsqontermslist: '<' bsqontypel error '>'  */
#line 142 "bsqon.y"
                              { (yyval.bsqon_t_list) = BSQON_TYPE_AST_ListCompleteParse(BSQON_TYPE_AST_ListCons(BSQON_TYPE_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1]))), (yyvsp[-2].bsqon_t_list))); yyerrok; }
#line 1919 "bsqon.tab.c"
    break;

  case 17: /* bsqontupletype: '[' ']'  */
#line 146 "bsqon.y"
           { (yyval.bsqon_t) = BSQON_AST_TupleNodeCreate(NULL); }
#line 1925 "bsqon.tab.c"
    break;

  case 18: /* bsqontupletype: '[' bsqontype ']'  */
#line 147 "bsqon.y"
                       { (yyval.bsqon_t) = BSQON_AST_TupleNodeCreate(BSQON_TYPE_AST_ListCons((yyvsp[-1].bsqon_t), NULL)); }
#line 1931 "bsqon.tab.c"
    break;

  case 19: /* bsqontupletype: '[' bsqontypel bsqontype ']'  */
#line 148 "bsqon.y"
                                  { (yyval.bsqon_t) = BSQON_AST_TupleNodeCreate(BSQON_TYPE_AST_ListCompleteParse(BSQON_TYPE_AST_ListCons((yyvsp[-1].bsqon_t), (yyvsp[-2].bsqon_t_list)))); }
#line 1937 "bsqon.tab.c"
    break;

  case 20: /* bsqontupletype: '[' error ']'  */
#line 149 "bsqon.y"
                   { (yyval.bsqon_t) = BSQON_AST_TupleNodeCreate(BSQON_TYPE_AST_ListCons(BSQON_TYPE_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1]))), NULL)); yyerrok; }
#line 1943 "bsqon.tab.c"
    break;

  case 21: /* bsqontupletype: '[' bsqontypel error ']'  */
#line 150 "bsqon.y"
                              { (yyval.bsqon_t) = BSQON_AST_TupleNodeCreate(BSQON_TYPE_AST_ListCompleteParse(BSQON_TYPE_AST_ListCons(BSQON_TYPE_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1]))), (yyvsp[-2].bsqon_t_list)))); yyerrok; }
#line 1949 "bsqon.tab.c"
    break;

  case 22: /* bsqonrecordtype: '{' '}'  */
#line 154 "bsqon.y"
           { (yyval.bsqon_t) = BSQON_AST_RecordNodeCreate(NULL); }
#line 1955 "bsqon.tab.c"
    break;

  case 23: /* bsqonrecordtype: '{' "identifier" ":" bsqontype '}'  */
#line 155 "bsqon.y"
                                                  { (yyval.bsqon_t) = BSQON_AST_RecordNodeCreate(BSQON_TYPE_AST_NamedListCons(BSQON_TYPE_AST_NamedListEntryCreate((yyvsp[-3].str), (yyvsp[-1].bsqon_t)), NULL)); }
#line 1961 "bsqon.tab.c"
    break;

  case 24: /* bsqonrecordtype: '{' bsqonnametypel "identifier" ":" bsqontype '}'  */
#line 156 "bsqon.y"
                                                                 { (yyval.bsqon_t) = BSQON_AST_RecordNodeCreate(BSQON_TYPE_AST_NamedListCompleteParse(BSQON_TYPE_AST_NamedListCons(BSQON_TYPE_AST_NamedListEntryCreate((yyvsp[-3].str), (yyvsp[-1].bsqon_t)), (yyvsp[-4].bsqon_t_namedlist)))); }
#line 1967 "bsqon.tab.c"
    break;

  case 25: /* bsqonrecordtype: '{' "identifier" ":" error '}'  */
#line 157 "bsqon.y"
                                              { (yyval.bsqon_t) = BSQON_AST_RecordNodeCreate(BSQON_TYPE_AST_NamedListCons(BSQON_TYPE_AST_NamedListEntryCreate((yyvsp[-3].str), BSQON_TYPE_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1])))), NULL)); yyerrok; }
#line 1973 "bsqon.tab.c"
    break;

  case 26: /* bsqonrecordtype: '{' bsqonnametypel "identifier" ":" error '}'  */
#line 158 "bsqon.y"
                                                             { (yyval.bsqon_t) = BSQON_AST_RecordNodeCreate(BSQON_TYPE_AST_NamedListCompleteParse(BSQON_TYPE_AST_NamedListCons(BSQON_TYPE_AST_NamedListEntryCreate((yyvsp[-3].str), BSQON_TYPE_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1])))), (yyvsp[-4].bsqon_t_namedlist)))); yyerrok; }
#line 1979 "bsqon.tab.c"
    break;

  case 27: /* bsqontype: bsqonnominaltype  */
#line 162 "bsqon.y"
                    { (yyval.bsqon_t) = (yyvsp[0].bsqon_t); }
#line 1985 "bsqon.tab.c"
    break;

  case 28: /* bsqontype: bsqontupletype  */
#line 163 "bsqon.y"
                    { (yyval.bsqon_t) = (yyvsp[0].bsqon_t); }
#line 1991 "bsqon.tab.c"
    break;

  case 29: /* bsqontype: bsqonrecordtype  */
#line 164 "bsqon.y"
                     { (yyval.bsqon_t) = (yyvsp[0].bsqon_t); }
#line 1997 "bsqon.tab.c"
    break;

  case 30: /* bsqontype: bsqontype SYM_AMP bsqontype  */
#line 165 "bsqon.y"
                                 { (yyval.bsqon_t) = BSQON_AST_ConjunctionCreate((yyvsp[-2].bsqon_t), (yyvsp[0].bsqon_t)); }
#line 2003 "bsqon.tab.c"
    break;

  case 31: /* bsqontype: bsqontype SYM_BAR bsqontype  */
#line 166 "bsqon.y"
                                 { (yyval.bsqon_t) = BSQON_AST_UnionCreate((yyvsp[-2].bsqon_t), (yyvsp[0].bsqon_t)); }
#line 2009 "bsqon.tab.c"
    break;

  case 32: /* bsqontype: '(' bsqontype ')'  */
#line 167 "bsqon.y"
                       { (yyval.bsqon_t) = (yyvsp[-1].bsqon_t); }
#line 2015 "bsqon.tab.c"
    break;

  case 33: /* bsqontype: '(' error ')'  */
#line 168 "bsqon.y"
                   { (yyval.bsqon_t) = BSQON_TYPE_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1]))); yyerrok; }
#line 2021 "bsqon.tab.c"
    break;

  case 34: /* bsqontspec: bsqonnominaltype  */
#line 172 "bsqon.y"
                    { (yyval.bsqon_t) = (yyvsp[0].bsqon_t); }
#line 2027 "bsqon.tab.c"
    break;

  case 35: /* bsqontspec: bsqontupletype  */
#line 173 "bsqon.y"
                    { (yyval.bsqon_t) = (yyvsp[0].bsqon_t); }
#line 2033 "bsqon.tab.c"
    break;

  case 36: /* bsqontspec: bsqonrecordtype  */
#line 174 "bsqon.y"
                     { (yyval.bsqon_t) = (yyvsp[0].bsqon_t); }
#line 2039 "bsqon.tab.c"
    break;

  case 37: /* bsqonliteral: "none"  */
#line 182 "bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralSingletonNodeCreate(BSQON_AST_TAG_None, MK_SPOS_S((yylsp[0]))); }
#line 2045 "bsqon.tab.c"
    break;

  case 38: /* bsqonliteral: "nothing"  */
#line 183 "bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralSingletonNodeCreate(BSQON_AST_TAG_Nothing, MK_SPOS_S((yylsp[0]))); }
#line 2051 "bsqon.tab.c"
    break;

  case 39: /* bsqonliteral: "true"  */
#line 184 "bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralSingletonNodeCreate(BSQON_AST_TAG_True, MK_SPOS_S((yylsp[0]))); }
#line 2057 "bsqon.tab.c"
    break;

  case 40: /* bsqonliteral: "false"  */
#line 185 "bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralSingletonNodeCreate(BSQON_AST_TAG_False, MK_SPOS_S((yylsp[0]))); }
#line 2063 "bsqon.tab.c"
    break;

  case 41: /* bsqonliteral: TOKEN_NAT  */
#line 186 "bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_Nat, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2069 "bsqon.tab.c"
    break;

  case 42: /* bsqonliteral: TOKEN_INT  */
#line 187 "bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_Int, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2075 "bsqon.tab.c"
    break;

  case 43: /* bsqonliteral: TOKEN_BIG_NAT  */
#line 188 "bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_BigNat, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2081 "bsqon.tab.c"
    break;

  case 44: /* bsqonliteral: TOKEN_BIG_INT  */
#line 189 "bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_BigInt, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2087 "bsqon.tab.c"
    break;

  case 45: /* bsqonliteral: TOKEN_RATIONAL  */
#line 190 "bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_Rational, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2093 "bsqon.tab.c"
    break;

  case 46: /* bsqonliteral: TOKEN_FLOAT  */
#line 191 "bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_Float, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2099 "bsqon.tab.c"
    break;

  case 47: /* bsqonliteral: TOKEN_DOUBLE  */
#line 192 "bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_Decimal, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2105 "bsqon.tab.c"
    break;

  case 48: /* bsqonliteral: TOKEN_BYTE_BUFFER  */
#line 193 "bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_ByteBuffer, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2111 "bsqon.tab.c"
    break;

  case 49: /* bsqonliteral: TOKEN_UUID_V4  */
#line 194 "bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_UUIDv4, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2117 "bsqon.tab.c"
    break;

  case 50: /* bsqonliteral: TOKEN_UUID_V7  */
#line 195 "bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_UUIDv7, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2123 "bsqon.tab.c"
    break;

  case 51: /* bsqonliteral: TOKEN_SHA_HASH  */
#line 196 "bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_SHAHashcode, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2129 "bsqon.tab.c"
    break;

  case 52: /* bsqonliteral: TOKEN_STRING  */
#line 197 "bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStringNodeCreate(BSQON_AST_TAG_String, MK_SPOS_S((yylsp[0])), (yyvsp[0].bstr)); }
#line 2135 "bsqon.tab.c"
    break;

  case 53: /* bsqonliteral: TOKEN_ASCII_STRING  */
#line 198 "bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStringNodeCreate(BSQON_AST_TAG_ASCIIString, MK_SPOS_S((yylsp[0])), (yyvsp[0].bstr)); }
#line 2141 "bsqon.tab.c"
    break;

  case 54: /* bsqonliteral: TOKEN_PATH_ITEM  */
#line 199 "bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStringNodeCreate(BSQON_AST_TAG_NakedPath, MK_SPOS_S((yylsp[0])), (yyvsp[0].bstr)); }
#line 2147 "bsqon.tab.c"
    break;

  case 55: /* bsqonliteral: TOKEN_REGEX  */
#line 200 "bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStringNodeCreate(BSQON_AST_TAG_Regex, MK_SPOS_S((yylsp[0])), (yyvsp[0].bstr)); }
#line 2153 "bsqon.tab.c"
    break;

  case 56: /* bsqonliteral: TOKEN_DATE_TIME  */
#line 201 "bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_DateTime, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2159 "bsqon.tab.c"
    break;

  case 57: /* bsqonliteral: TOKEN_UTC_DATE_TIME  */
#line 202 "bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_UTCDateTime, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2165 "bsqon.tab.c"
    break;

  case 58: /* bsqonliteral: TOKEN_PLAIN_DATE  */
#line 203 "bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_PlainDate, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2171 "bsqon.tab.c"
    break;

  case 59: /* bsqonliteral: TOKEN_PLAIN_TIME  */
#line 204 "bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_PlainTime, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2177 "bsqon.tab.c"
    break;

  case 60: /* bsqonliteral: TOKEN_LOGICAL_TIME  */
#line 205 "bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_LogicalTime, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2183 "bsqon.tab.c"
    break;

  case 61: /* bsqonliteral: TOKEN_TICK_TIME  */
#line 206 "bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_TickTime, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2189 "bsqon.tab.c"
    break;

  case 62: /* bsqonliteral: TOKEN_TIMESTAMP  */
#line 207 "bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_Timestamp, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2195 "bsqon.tab.c"
    break;

  case 63: /* bsqonunspecvar: "unspec identifier"  */
#line 211 "bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_NameNodeCreate(BSQON_AST_TAG_UnspecIdentifier, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2201 "bsqon.tab.c"
    break;

  case 64: /* bsqonidentifier: KW_SRC  */
#line 215 "bsqon.y"
                { (yyval.bsqon) = BSQON_AST_NameNodeCreate(BSQON_AST_TAG_Identifier, MK_SPOS_S((yylsp[0])), "$src"); }
#line 2207 "bsqon.tab.c"
    break;

  case 65: /* bsqonidentifier: "identifier"  */
#line 216 "bsqon.y"
                      { (yyval.bsqon) = BSQON_AST_NameNodeCreate(BSQON_AST_TAG_Identifier, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2213 "bsqon.tab.c"
    break;

  case 67: /* bsqonstringof: TOKEN_STRING bsqonnominaltype  */
#line 224 "bsqon.y"
                                 { (yyval.bsqon) = BSQON_AST_StringOfNodeCreate(BSQON_AST_TAG_StringOf, MK_SPOS_R((yylsp[-1]), (yylsp[0])), (yyvsp[-1].bstr), (yyvsp[0].bsqon_t)); }
#line 2219 "bsqon.tab.c"
    break;

  case 68: /* bsqonstringof: TOKEN_ASCII_STRING bsqonnominaltype  */
#line 225 "bsqon.y"
                                         { (yyval.bsqon) = BSQON_AST_StringOfNodeCreate(BSQON_AST_TAG_ASCIIStringOf, MK_SPOS_R((yylsp[-1]), (yylsp[0])), (yyvsp[-1].bstr), (yyvsp[0].bsqon_t)); }
#line 2225 "bsqon.tab.c"
    break;

  case 69: /* bsqonpath: TOKEN_PATH_ITEM bsqonnominaltype  */
#line 229 "bsqon.y"
                                    { (yyval.bsqon) = BSQON_AST_PathNodeCreate(MK_SPOS_R((yylsp[-1]), (yylsp[0])), BSQON_AST_LiteralStringNodeCreate(BSQON_AST_TAG_NakedPath, MK_SPOS_S((yylsp[-1])), (yyvsp[-1].bstr)), (yyvsp[0].bsqon_t)); }
#line 2231 "bsqon.tab.c"
    break;

  case 70: /* bsqontypeliteral: "numberino" SYM_UNDERSCORE bsqonnominaltype  */
#line 233 "bsqon.y"
                                                   {
      yyerror("Missing numeric specifier");
      (yyval.bsqon) = BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-2])));
   }
#line 2240 "bsqon.tab.c"
    break;

  case 71: /* bsqontypeliteral: "none" SYM_UNDERSCORE bsqonnominaltype  */
#line 237 "bsqon.y"
                                             {
      yyerror("Cannot have a typedecl of none or nothing");
      (yyval.bsqon) = BSQON_AST_ErrorNodeCreate(MK_SPOS_R((yylsp[-2]), (yylsp[0])));
   }
#line 2249 "bsqon.tab.c"
    break;

  case 72: /* bsqontypeliteral: "nothing" SYM_UNDERSCORE bsqonnominaltype  */
#line 241 "bsqon.y"
                                                {
      yyerror("Cannot have a typedecl of none or nothing");
      (yyval.bsqon) = BSQON_AST_ErrorNodeCreate(MK_SPOS_R((yylsp[-2]), (yylsp[0])));
   }
#line 2258 "bsqon.tab.c"
    break;

  case 73: /* bsqontypeliteral: bsqonliteral SYM_UNDERSCORE bsqonnominaltype  */
#line 245 "bsqon.y"
                                                  {
      (yyval.bsqon) = BSQON_AST_TypedLiteralNodeCreate(MK_SPOS_R((yylsp[-2]), (yylsp[0])), (yyvsp[-2].bsqon), (yyvsp[0].bsqon_t));
   }
#line 2266 "bsqon.tab.c"
    break;

  case 80: /* bsqonterminal: bsqontypeliteral  */
#line 251 "bsqon.y"
                                                                                                                          { (yyval.bsqon) = (yyvsp[0].bsqon); }
#line 2272 "bsqon.tab.c"
    break;

  case 81: /* bsqon_mapentry: bsqonval SYM_ENTRY bsqonval  */
#line 255 "bsqon.y"
                               { (yyval.bsqon) = BSQON_AST_MapEntryNodeCreate(MK_SPOS_R((yylsp[-2]), (yylsp[0])), (yyvsp[-2].bsqon), (yyvsp[0].bsqon)); }
#line 2278 "bsqon.tab.c"
    break;

  case 82: /* bsqon_mapentry: error SYM_ENTRY bsqonval  */
#line 256 "bsqon.y"
                              { (yyval.bsqon) = BSQON_AST_MapEntryNodeCreate(MK_SPOS_R((yylsp[-2]), (yylsp[0])), BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-2]))), (yyvsp[0].bsqon)); yyerrok; }
#line 2284 "bsqon.tab.c"
    break;

  case 83: /* bsqon_mapentry: bsqonval SYM_ENTRY error  */
#line 257 "bsqon.y"
                              { (yyval.bsqon) = BSQON_AST_MapEntryNodeCreate(MK_SPOS_R((yylsp[-2]), (yylsp[0])), (yyvsp[-2].bsqon), BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[0])))); yyerrok; }
#line 2290 "bsqon.tab.c"
    break;

  case 84: /* bsqon_mapentry: error SYM_ENTRY error  */
#line 258 "bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_MapEntryNodeCreate(MK_SPOS_R((yylsp[-2]), (yylsp[0])), BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-2]))), BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[0])))); yyerrok; }
#line 2296 "bsqon.tab.c"
    break;

  case 85: /* bsqonvall: bsqonvall bsqonl_entry  */
#line 262 "bsqon.y"
                          { (yyval.bsqon_list) = BSQON_AST_ListCons((yyvsp[0].bsqon), (yyvsp[-1].bsqon_list)); }
#line 2302 "bsqon.tab.c"
    break;

  case 86: /* bsqonvall: bsqonl_entry  */
#line 263 "bsqon.y"
                  { (yyval.bsqon_list) = BSQON_AST_ListCons((yyvsp[0].bsqon), NULL); }
#line 2308 "bsqon.tab.c"
    break;

  case 87: /* bsqonl_entry: bsqon_braceval ","  */
#line 267 "bsqon.y"
                            { (yyval.bsqon) = (yyvsp[-1].bsqon); }
#line 2314 "bsqon.tab.c"
    break;

  case 88: /* bsqonl_entry: error ","  */
#line 268 "bsqon.y"
                     { (yyval.bsqon) = BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1]))); yyerrok; }
#line 2320 "bsqon.tab.c"
    break;

  case 89: /* bsqonbracketvalue: '[' ']'  */
#line 272 "bsqon.y"
           { (yyval.bsqon) = BSQON_AST_BracketValueNodeCreate(MK_SPOS_R((yylsp[-1]), (yylsp[0])), NULL); }
#line 2326 "bsqon.tab.c"
    break;

  case 90: /* bsqonbracketvalue: '[' bsqonval ']'  */
#line 273 "bsqon.y"
                      { (yyval.bsqon) = BSQON_AST_BracketValueNodeCreate(MK_SPOS_R((yylsp[-2]), (yylsp[0])), BSQON_AST_ListCons((yyvsp[-1].bsqon), NULL)); }
#line 2332 "bsqon.tab.c"
    break;

  case 91: /* bsqonbracketvalue: '[' bsqonvall bsqonval ']'  */
#line 274 "bsqon.y"
                                { (yyval.bsqon) = BSQON_AST_BracketValueNodeCreate(MK_SPOS_R((yylsp[-3]), (yylsp[0])), BSQON_AST_ListCompleteParse(BSQON_AST_ListCons((yyvsp[-1].bsqon), (yyvsp[-2].bsqon_list)))); }
#line 2338 "bsqon.tab.c"
    break;

  case 92: /* bsqonbracketvalue: '[' error ']'  */
#line 275 "bsqon.y"
                   { (yyval.bsqon) = BSQON_AST_BracketValueNodeCreate(MK_SPOS_R((yylsp[-2]), (yylsp[0])), BSQON_AST_ListCons(BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1]))), NULL)); yyerrok; }
#line 2344 "bsqon.tab.c"
    break;

  case 93: /* bsqonbracketvalue: '[' bsqonvall error ']'  */
#line 276 "bsqon.y"
                             { (yyval.bsqon) = BSQON_AST_BracketValueNodeCreate(MK_SPOS_R((yylsp[-3]), (yylsp[0])), BSQON_AST_ListCompleteParse(BSQON_AST_ListCons(BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1]))), (yyvsp[-2].bsqon_list)))); yyerrok; }
#line 2350 "bsqon.tab.c"
    break;

  case 94: /* bsqonnamevall: bsqonnamevall bsqonnameval_entry  */
#line 280 "bsqon.y"
                                    { (yyval.bsqon_namedlist) = BSQON_AST_NamedListCons((yyvsp[0].bsqon_nameval_entry), (yyvsp[-1].bsqon_namedlist)); }
#line 2356 "bsqon.tab.c"
    break;

  case 95: /* bsqonnamevall: bsqonnameval_entry  */
#line 281 "bsqon.y"
                        { (yyval.bsqon_namedlist) = BSQON_AST_NamedListCons((yyvsp[0].bsqon_nameval_entry), NULL); }
#line 2362 "bsqon.tab.c"
    break;

  case 97: /* bsqon_braceval: bsqon_mapentry  */
#line 285 "bsqon.y"
                             { (yyval.bsqon) = (yyvsp[0].bsqon); }
#line 2368 "bsqon.tab.c"
    break;

  case 98: /* bsqonnameval_entry: "identifier" SYM_EQUALS bsqonval ","  */
#line 289 "bsqon.y"
                                                  { (yyval.bsqon_nameval_entry) = BSQON_AST_NamedListEntryCreate((yyvsp[-3].str), (yyvsp[-1].bsqon)); }
#line 2374 "bsqon.tab.c"
    break;

  case 99: /* bsqonnameval_entry: "identifier" SYM_EQUALS error ","  */
#line 290 "bsqon.y"
                                                 { (yyval.bsqon_nameval_entry) = BSQON_AST_NamedListEntryCreate((yyvsp[-3].str), BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1])))); yyerrok; }
#line 2380 "bsqon.tab.c"
    break;

  case 100: /* bsqonnameval_entry: bsqon_braceval ","  */
#line 291 "bsqon.y"
                              { (yyval.bsqon_nameval_entry) = BSQON_AST_NamedListEntryCreate(NULL, (yyvsp[-1].bsqon)); }
#line 2386 "bsqon.tab.c"
    break;

  case 101: /* bsqonnameval_entry: error ","  */
#line 292 "bsqon.y"
                     { (yyval.bsqon_nameval_entry) = BSQON_AST_NamedListEntryCreate(NULL, BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1])))); yyerrok; }
#line 2392 "bsqon.tab.c"
    break;

  case 102: /* bsqonbracevalue: '{' '}'  */
#line 296 "bsqon.y"
           { (yyval.bsqon) = BSQON_AST_BraceValueNodeCreate(MK_SPOS_R((yylsp[-1]), (yylsp[0])), NULL); }
#line 2398 "bsqon.tab.c"
    break;

  case 103: /* bsqonbracevalue: '{' "identifier" SYM_EQUALS bsqonval '}'  */
#line 297 "bsqon.y"
                                                  { (yyval.bsqon) = BSQON_AST_BraceValueNodeCreate(MK_SPOS_R((yylsp[-4]), (yylsp[0])), BSQON_AST_NamedListCons(BSQON_AST_NamedListEntryCreate((yyvsp[-3].str), (yyvsp[-1].bsqon)), NULL)); }
#line 2404 "bsqon.tab.c"
    break;

  case 104: /* bsqonbracevalue: '{' bsqonnamevall "identifier" SYM_EQUALS bsqonval '}'  */
#line 298 "bsqon.y"
                                                                { (yyval.bsqon) = BSQON_AST_BraceValueNodeCreate(MK_SPOS_R((yylsp[-5]), (yylsp[0])), BSQON_AST_NamedListCompleteParse(BSQON_AST_NamedListCons(BSQON_AST_NamedListEntryCreate((yyvsp[-3].str), (yyvsp[-1].bsqon)), (yyvsp[-4].bsqon_namedlist)))); }
#line 2410 "bsqon.tab.c"
    break;

  case 105: /* bsqonbracevalue: '{' "identifier" SYM_EQUALS error '}'  */
#line 299 "bsqon.y"
                                               { (yyval.bsqon) = BSQON_AST_BraceValueNodeCreate(MK_SPOS_R((yylsp[-4]), (yylsp[0])), BSQON_AST_NamedListCons(BSQON_AST_NamedListEntryCreate((yyvsp[-3].str), BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1])))), NULL)); yyerrok; }
#line 2416 "bsqon.tab.c"
    break;

  case 106: /* bsqonbracevalue: '{' bsqonnamevall "identifier" SYM_EQUALS error '}'  */
#line 300 "bsqon.y"
                                                             { (yyval.bsqon) = BSQON_AST_BraceValueNodeCreate(MK_SPOS_R((yylsp[-5]), (yylsp[0])), BSQON_AST_NamedListCompleteParse(BSQON_AST_NamedListCons(BSQON_AST_NamedListEntryCreate((yyvsp[-3].str), BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1])))), (yyvsp[-4].bsqon_namedlist)))); yyerrok; }
#line 2422 "bsqon.tab.c"
    break;

  case 107: /* bsqonbracevalue: '{' bsqon_braceval '}'  */
#line 301 "bsqon.y"
                            { (yyval.bsqon) = BSQON_AST_BraceValueNodeCreate(MK_SPOS_R((yylsp[-2]), (yylsp[0])), BSQON_AST_NamedListCons(BSQON_AST_NamedListEntryCreate(NULL, (yyvsp[-1].bsqon)), NULL)); }
#line 2428 "bsqon.tab.c"
    break;

  case 108: /* bsqonbracevalue: '{' bsqonnamevall bsqon_braceval '}'  */
#line 302 "bsqon.y"
                                          { (yyval.bsqon) = BSQON_AST_BraceValueNodeCreate(MK_SPOS_R((yylsp[-3]), (yylsp[0])), BSQON_AST_NamedListCompleteParse(BSQON_AST_NamedListCons(BSQON_AST_NamedListEntryCreate(NULL, (yyvsp[-1].bsqon)), (yyvsp[-2].bsqon_namedlist)))); }
#line 2434 "bsqon.tab.c"
    break;

  case 109: /* bsqonbracevalue: '{' error '}'  */
#line 303 "bsqon.y"
                   { (yyval.bsqon) = BSQON_AST_BraceValueNodeCreate(MK_SPOS_R((yylsp[-2]), (yylsp[0])), BSQON_AST_NamedListCons(BSQON_AST_NamedListEntryCreate(NULL, BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1])))), NULL)); yyerrok; }
#line 2440 "bsqon.tab.c"
    break;

  case 110: /* bsqonbracevalue: '{' bsqonnamevall error '}'  */
#line 304 "bsqon.y"
                                 { (yyval.bsqon) = BSQON_AST_BraceValueNodeCreate(MK_SPOS_R((yylsp[-3]), (yylsp[0])), BSQON_AST_NamedListCompleteParse(BSQON_AST_NamedListCons(BSQON_AST_NamedListEntryCreate(NULL, BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1])))), (yyvsp[-2].bsqon_namedlist)))); yyerrok; }
#line 2446 "bsqon.tab.c"
    break;

  case 112: /* bsqonbracketbracevalue: bsqonbracevalue  */
#line 308 "bsqon.y"
                                       { (yyval.bsqon) = (yyvsp[0].bsqon); }
#line 2452 "bsqon.tab.c"
    break;

  case 113: /* bsqontypedvalue: '<' bsqontspec '>' bsqonbracketbracevalue  */
#line 312 "bsqon.y"
                                             { (yyval.bsqon) = BSQON_AST_TypedValueNodeCreate(MK_SPOS_R((yylsp[-3]), (yylsp[0])), (yyvsp[0].bsqon), (yyvsp[-2].bsqon_t)); }
#line 2458 "bsqon.tab.c"
    break;

  case 114: /* bsqontypedvalue: bsqonnominaltype bsqonbracketbracevalue  */
#line 313 "bsqon.y"
                                             { (yyval.bsqon) = BSQON_AST_TypedValueNodeCreate(MK_SPOS_R((yylsp[-1]), (yylsp[0])), (yyvsp[0].bsqon), (yyvsp[-1].bsqon_t)); }
#line 2464 "bsqon.tab.c"
    break;

  case 115: /* bsqontypedvalue: '<' error '>' bsqonbracketbracevalue  */
#line 314 "bsqon.y"
                                          { (yyval.bsqon) = BSQON_AST_TypedValueNodeCreate(MK_SPOS_R((yylsp[-3]), (yylsp[0])), (yyvsp[0].bsqon), BSQON_TYPE_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-2])))); }
#line 2470 "bsqon.tab.c"
    break;

  case 116: /* bsqontypedvalue: error bsqonbracketbracevalue  */
#line 315 "bsqon.y"
                                  { (yyval.bsqon) = BSQON_AST_TypedValueNodeCreate(MK_SPOS_R((yylsp[-1]), (yylsp[0])), (yyvsp[0].bsqon), BSQON_TYPE_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1])))); }
#line 2476 "bsqon.tab.c"
    break;

  case 118: /* bsqonstructvalue: bsqontypedvalue  */
#line 319 "bsqon.y"
                                            { (yyval.bsqon) = (yyvsp[0].bsqon); }
#line 2482 "bsqon.tab.c"
    break;

  case 119: /* bsqonspecialcons: "something" '(' bsqonval ')'  */
#line 323 "bsqon.y"
                                 { (yyval.bsqon) = BSQON_AST_SpecialConsNodeCreate(BSQON_AST_TAG_SomethingCons, MK_SPOS_R((yylsp[-3]), (yylsp[0])), (yyvsp[-1].bsqon), "some"); }
#line 2488 "bsqon.tab.c"
    break;

  case 120: /* bsqonspecialcons: "ok" '(' bsqonval ')'  */
#line 324 "bsqon.y"
                            { (yyval.bsqon) = BSQON_AST_SpecialConsNodeCreate(BSQON_AST_TAG_OkCons, MK_SPOS_R((yylsp[-3]), (yylsp[0])), (yyvsp[-1].bsqon), "ok"); }
#line 2494 "bsqon.tab.c"
    break;

  case 121: /* bsqonspecialcons: "err" '(' bsqonval ')'  */
#line 325 "bsqon.y"
                             { (yyval.bsqon) = BSQON_AST_SpecialConsNodeCreate(BSQON_AST_TAG_ErrCons, MK_SPOS_R((yylsp[-3]), (yylsp[0])), (yyvsp[-1].bsqon), "err"); }
#line 2500 "bsqon.tab.c"
    break;

  case 124: /* bsqonval: bsqonstructvalue  */
#line 329 "bsqon.y"
                                                      { (yyval.bsqon) = (yyvsp[0].bsqon); }
#line 2506 "bsqon.tab.c"
    break;

  case 125: /* bsqonroot: bsqonval  */
#line 337 "bsqon.y"
            { yybsqonval = (yyvsp[0].bsqon); (yyval.bsqon) = (yyvsp[0].bsqon); }
#line 2512 "bsqon.tab.c"
    break;

  case 126: /* bsqonroot: error  */
#line 338 "bsqon.y"
           {yybsqonval = BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[0]))); (yyval.bsqon) = BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[0]))); }
#line 2518 "bsqon.tab.c"
    break;


#line 2522 "bsqon.tab.c"

      default: break;
    }
  /* User semantic actions sometimes alter yychar, and that requires
     that yytoken be updated with the new translation.  We take the
     approach of translating immediately before every use of yytoken.
     One alternative is translating here after every semantic action,
     but that translation would be missed if the semantic action invokes
     YYABORT, YYACCEPT, or YYERROR immediately after altering yychar or
     if it invokes YYBACKUP.  In the case of YYABORT or YYACCEPT, an
     incorrect destructor might then be invoked immediately.  In the
     case of YYERROR or YYBACKUP, subsequent parser actions might lead
     to an incorrect destructor call or verbose syntax error message
     before the lookahead is translated.  */
  YY_SYMBOL_PRINT ("-> $$ =", YY_CAST (yysymbol_kind_t, yyr1[yyn]), &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;

  *++yyvsp = yyval;
  *++yylsp = yyloc;

  /* Now 'shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */
  {
    const int yylhs = yyr1[yyn] - YYNTOKENS;
    const int yyi = yypgoto[yylhs] + *yyssp;
    yystate = (0 <= yyi && yyi <= YYLAST && yycheck[yyi] == *yyssp
               ? yytable[yyi]
               : yydefgoto[yylhs]);
  }

  goto yynewstate;


/*--------------------------------------.
| yyerrlab -- here on detecting error.  |
`--------------------------------------*/
yyerrlab:
  /* Make sure we have latest lookahead translation.  See comments at
     user semantic actions for why this is necessary.  */
  yytoken = yychar == YYEMPTY ? YYSYMBOL_YYEMPTY : YYTRANSLATE (yychar);
  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
      {
        yypcontext_t yyctx
          = {yyssp, yytoken, &yylloc};
        char const *yymsgp = YY_("syntax error");
        int yysyntax_error_status;
        yysyntax_error_status = yysyntax_error (&yymsg_alloc, &yymsg, &yyctx);
        if (yysyntax_error_status == 0)
          yymsgp = yymsg;
        else if (yysyntax_error_status == -1)
          {
            if (yymsg != yymsgbuf)
              YYSTACK_FREE (yymsg);
            yymsg = YY_CAST (char *,
                             YYSTACK_ALLOC (YY_CAST (YYSIZE_T, yymsg_alloc)));
            if (yymsg)
              {
                yysyntax_error_status
                  = yysyntax_error (&yymsg_alloc, &yymsg, &yyctx);
                yymsgp = yymsg;
              }
            else
              {
                yymsg = yymsgbuf;
                yymsg_alloc = sizeof yymsgbuf;
                yysyntax_error_status = YYENOMEM;
              }
          }
        yyerror (yymsgp);
        if (yysyntax_error_status == YYENOMEM)
          YYNOMEM;
      }
    }

  yyerror_range[1] = yylloc;
  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
         error, discard it.  */

      if (yychar <= YYEOF)
        {
          /* Return failure if at end of input.  */
          if (yychar == YYEOF)
            YYABORT;
        }
      else
        {
          yydestruct ("Error: discarding",
                      yytoken, &yylval, &yylloc);
          yychar = YYEMPTY;
        }
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:
  /* Pacify compilers when the user code never invokes YYERROR and the
     label yyerrorlab therefore never appears in user code.  */
  if (0)
    YYERROR;
  ++yynerrs;

  /* Do not reclaim the symbols of the rule whose action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;      /* Each real token shifted decrements this.  */

  /* Pop stack until we find a state that shifts the error token.  */
  for (;;)
    {
      yyn = yypact[yystate];
      if (!yypact_value_is_default (yyn))
        {
          yyn += YYSYMBOL_YYerror;
          if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYSYMBOL_YYerror)
            {
              yyn = yytable[yyn];
              if (0 < yyn)
                break;
            }
        }

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
        YYABORT;

      yyerror_range[1] = *yylsp;
      yydestruct ("Error: popping",
                  YY_ACCESSING_SYMBOL (yystate), yyvsp, yylsp);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END

  yyerror_range[2] = yylloc;
  ++yylsp;
  YYLLOC_DEFAULT (*yylsp, yyerror_range, 2);

  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", YY_ACCESSING_SYMBOL (yyn), yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturnlab;


/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturnlab;


/*-----------------------------------------------------------.
| yyexhaustedlab -- YYNOMEM (memory exhaustion) comes here.  |
`-----------------------------------------------------------*/
yyexhaustedlab:
  yyerror (YY_("memory exhausted"));
  yyresult = 2;
  goto yyreturnlab;


/*----------------------------------------------------------.
| yyreturnlab -- parsing is finished, clean up and return.  |
`----------------------------------------------------------*/
yyreturnlab:
  if (yychar != YYEMPTY)
    {
      /* Make sure we have latest lookahead translation.  See comments at
         user semantic actions for why this is necessary.  */
      yytoken = YYTRANSLATE (yychar);
      yydestruct ("Cleanup: discarding lookahead",
                  yytoken, &yylval, &yylloc);
    }
  /* Do not reclaim the symbols of the rule whose action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
                  YY_ACCESSING_SYMBOL (+*yyssp), yyvsp, yylsp);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif
  if (yymsg != yymsgbuf)
    YYSTACK_FREE (yymsg);
  return yyresult;
}

#line 339 "bsqon.y"


extern FILE* yyin;

size_t isSpecialTypedLiteralIdConflict(const char* txt)
{
   size_t tlen = strlen(txt);
   if(strncmp("none_", txt, 5) == 0  && tlen >= 6 && isupper(txt[5])) {
      return tlen - 4;
   }
   else if(strncmp("true_", txt, 5) == 0  && tlen >= 6 && isupper(txt[5])) {
      return tlen - 4;
   }
   else if(strncmp("false_", txt, 6) == 0  && tlen >= 7 && isupper(txt[6])) {
      return tlen - 5;
   }
   else if(strncmp("nothing_", txt, 8) == 0  && tlen >= 9 && isupper(txt[8])) {
      return tlen - 7;
   }
   else {
      return 0;
   }
}

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
      BSQON_AST_print(yybsqonval);
      //BSQON_TYPE_AST_print(yybsqonval_type);

      printf("\n");
      fflush(stdout);
   }
      
   for(size_t i = 0; i < errorcount; ++i) {
      printf("%s\n", errors[i]);
      fflush(stdout);
   }
}
#else
struct BSQON_AST_Node* parse_from_file(const char* file)
{
   if((yyin = fopen(file, "r")) == NULL) {
      perror(file);
      exit(1);
   }
   
   if(!yyparse()) {
      //todo handle errors here!!!!
      printf("ERROR IN PARSE!\n");
      exit(1);
   }

   return yybsqonval;
}
#endif
