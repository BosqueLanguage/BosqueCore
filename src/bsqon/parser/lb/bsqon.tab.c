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
#line 1 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"

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

#line 100 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"

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
  YYSYMBOL_bsqonletexp = 95,               /* bsqonletexp  */
  YYSYMBOL_bsqonroot = 96                  /* bsqonroot  */
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
#define YYLAST   778

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  63
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  34
/* YYNRULES -- Number of rules.  */
#define YYNRULES  126
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  208

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
       0,   110,   110,   111,   115,   116,   120,   121,   125,   126,
     130,   131,   132,   136,   137,   138,   139,   143,   144,   145,
     146,   147,   151,   152,   153,   154,   155,   159,   160,   161,
     162,   163,   164,   165,   169,   170,   171,   175,   176,   177,
     178,   179,   180,   181,   182,   183,   184,   185,   186,   187,
     188,   189,   190,   191,   192,   193,   194,   195,   196,   197,
     198,   199,   200,   204,   208,   209,   213,   217,   218,   222,
     226,   230,   236,   236,   236,   236,   236,   236,   236,   240,
     241,   242,   243,   247,   248,   252,   253,   257,   258,   259,
     260,   261,   265,   266,   270,   270,   274,   275,   276,   277,
     281,   282,   283,   284,   285,   286,   287,   288,   289,   293,
     293,   297,   298,   299,   300,   304,   304,   308,   309,   310,
     314,   314,   314,   314,   318,   322,   323
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
  "bsqonletexp", "bsqonroot", YY_NULLPTR
};

static const char *
yysymbol_name (yysymbol_kind_t yysymbol)
{
  return yytname[yysymbol];
}
#endif

#define YYPACT_NINF (-94)

#define yypact_value_is_default(Yyn) \
  ((Yyn) == YYPACT_NINF)

#define YYTABLE_NINF (-1)

#define yytable_value_is_error(Yyn) \
  0

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
static const yytype_int16 yypact[] =
{
     291,   -39,   -94,   -94,   -94,   -94,   -57,   -55,   -40,   -94,
     -94,   -94,   -94,   -94,   -94,   -94,   -94,    15,   -94,   -94,
     -94,   -94,    40,    40,   -94,    40,   -94,   -94,   -94,   -94,
     -94,   -94,   -94,   -94,   -14,   -94,    35,   183,   237,    49,
     107,    30,   -94,   -94,   -94,   -94,   -94,   -94,   -94,   -94,
     -94,   -94,   -94,   -94,   -94,   -94,   -94,   146,   -94,   345,
     345,   345,    40,   132,   132,   132,    14,   -94,    95,    11,
      -8,   132,   -94,   -94,   114,   716,   -94,   -94,   399,   -94,
     149,   -11,   102,   159,   -94,   453,    -7,   -94,   163,   134,
     -18,   -94,    40,   -94,   -39,   128,   129,   138,   132,   135,
     127,    21,    44,   -94,   132,   -94,   -94,    39,   -39,    31,
     -94,    55,    27,   179,   -94,   137,   -94,   -39,   -94,   507,
     -94,   720,   -94,     5,   -94,   561,   -94,   -94,   -94,   615,
     677,   184,    -4,   -94,   -94,   -94,   141,   -94,   -94,   132,
     -94,   -94,   -94,   -94,   -94,   148,     3,   145,   -94,   125,
     -31,   -31,   -94,   -94,   -94,   -94,   126,   109,   -94,    84,
     199,   -94,   -94,   -39,   -94,   -94,   -94,   -39,   -94,    93,
       6,   -94,   669,   -94,   -31,   -94,   -94,   -94,   -94,   202,
     -94,   -94,   -94,   108,    23,    85,   -94,   -94,   -94,   -94,
     118,   116,   151,   -94,   -94,   -94,   -94,   119,   100,   -94,
     -94,   345,   -94,   -94,   215,   345,   192,   -94
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
       0,    72,    73,    74,    75,    76,    77,    78,   120,   109,
     110,   115,   116,   122,   121,   125,   123,     0,   114,     0,
       0,     0,     0,    67,    68,    69,     0,    11,     0,     0,
       0,    34,    35,    36,     0,     0,    87,    95,     0,    84,
       0,    94,     0,    65,   100,     0,     0,    93,    94,     0,
       0,   112,     0,     1,     0,     0,     0,     0,    70,     0,
       0,     0,     0,     3,    27,    28,    29,     0,     0,     0,
      17,     0,     0,     0,    22,     0,     7,     0,    86,     0,
      90,     0,    83,    94,    85,     0,    88,    99,   107,     0,
       0,    65,     0,    92,    98,   105,     0,    66,    12,    71,
     117,   118,   119,     5,    15,     0,     0,     0,     2,     0,
       0,     0,     4,    13,   113,    20,     0,     0,    18,     0,
       0,     6,   111,    82,    80,    91,    89,    81,    79,     0,
       0,   108,     0,   106,     0,    33,    32,    16,    14,    31,
      30,    21,    19,     0,     0,     0,    97,   103,    96,   101,
       0,     0,     0,     9,    25,     8,    23,     0,     0,   104,
     102,     0,    26,    24,     0,     0,     0,   124
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
     -94,   175,   -93,   -94,   130,   -12,   -94,   174,   218,   -53,
     -94,   -94,   -94,   -94,   -94,   -94,   -94,   -94,   -94,   -94,
     -94,   177,   -94,   -94,   117,   171,   -94,     1,   -94,   -94,
     -94,     0,   -94,   -94
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_int8 yydefgoto[] =
{
       0,   102,   103,   115,   116,    40,    67,   105,   106,   107,
      74,    41,    42,    43,    44,    45,    46,    47,    48,    77,
      78,    79,    49,    85,    80,    87,    50,    51,    52,    53,
      54,    88,    56,    57
};

/* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule whose
   number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_uint8 yytable[] =
{
      55,   134,    58,    59,   134,    60,   150,   125,   151,   148,
      63,    64,   109,    65,   188,   100,   112,    37,   148,    38,
      61,    34,   145,   125,    71,    69,   150,    70,   151,   101,
     150,   195,   151,   137,   138,   152,    68,    81,    62,   143,
      66,    91,   150,   113,   151,   147,   126,   152,   146,   149,
      98,   114,   135,    92,   104,   173,   156,   104,   157,    95,
      96,    97,   166,    34,   176,   189,    34,    69,   110,    70,
      69,   101,    70,    34,   101,    89,    58,    69,   123,    70,
     139,   101,   196,    58,   158,   183,   197,    34,   155,   104,
     104,    69,    34,    70,   153,    58,    34,   179,   180,   104,
      69,   186,    70,   150,   101,   151,   184,    34,   195,   154,
     127,    69,   150,    70,   151,   101,   193,   152,   162,   164,
     119,   192,    58,    90,   188,   168,   186,   193,   150,   170,
     151,    58,   198,   152,   143,   143,    34,    34,   104,   104,
      69,    69,    70,    70,   101,   101,    93,   104,    99,    37,
     108,    38,   187,   143,   150,    86,   151,   124,    37,   203,
      38,   128,   104,    37,    58,    38,   182,   194,    58,   117,
      58,   201,   191,   104,    37,   200,    38,   199,   202,   129,
     178,   125,   144,   181,    75,   136,   159,   138,   160,   140,
     141,    58,     2,     3,     4,     5,     6,     7,     8,   142,
     177,   204,   132,   174,   172,   206,   185,   151,     9,   175,
      72,    10,    11,    12,    13,    14,    15,    16,    17,    18,
      19,    20,    21,    22,    23,    24,    25,    26,    27,    28,
      29,    30,    31,    32,    33,    34,    35,    36,    82,    37,
      76,    38,   205,    39,   111,   161,     2,     3,     4,     5,
       6,     7,     8,   207,    73,   122,   133,     0,     0,     0,
       0,     0,     9,     0,     0,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    83,    34,
      35,    36,     1,    37,     0,    38,    84,    39,     0,     0,
       2,     3,     4,     5,     6,     7,     8,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     9,     0,     0,    10,
      11,    12,    13,    14,    15,    16,    17,    18,    19,    20,
      21,    22,    23,    24,    25,    26,    27,    28,    29,    30,
      31,    32,    33,    34,    35,    36,    94,    37,     0,    38,
       0,    39,     0,     0,     2,     3,     4,     5,     6,     7,
       8,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       9,     0,     0,    10,    11,    12,    13,    14,    15,    16,
      17,    18,    19,    20,    21,    22,    23,    24,    25,    26,
      27,    28,    29,    30,    31,    32,    33,    34,    35,    36,
     121,    37,     0,    38,     0,    39,     0,     0,     2,     3,
       4,     5,     6,     7,     8,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     9,     0,     0,    10,    11,    12,
      13,    14,    15,    16,    17,    18,    19,    20,    21,    22,
      23,    24,    25,    26,    27,    28,    29,    30,    31,    32,
      33,    34,    35,    36,   130,    37,     0,    38,     0,    39,
       0,     0,     2,     3,     4,     5,     6,     7,     8,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     9,     0,
       0,    10,    11,    12,    13,    14,    15,    16,    17,    18,
      19,    20,    21,    22,    23,    24,    25,    26,    27,    28,
      29,    30,    31,    32,   131,    34,    35,    36,   163,    37,
       0,    38,     0,    39,     0,     0,     2,     3,     4,     5,
       6,     7,     8,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     9,     0,     0,    10,    11,    12,    13,    14,
      15,    16,    17,    18,    19,    20,    21,    22,    23,    24,
      25,    26,    27,    28,    29,    30,    31,    32,    33,    34,
      35,    36,   167,    37,     0,    38,     0,    39,     0,     0,
       2,     3,     4,     5,     6,     7,     8,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     9,     0,     0,    10,
      11,    12,    13,    14,    15,    16,    17,    18,    19,    20,
      21,    22,    23,    24,    25,    26,    27,    28,    29,    30,
      31,    32,    33,    34,    35,    36,   169,    37,     0,    38,
       0,    39,     0,     0,     2,     3,     4,     5,     6,     7,
       8,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       9,     0,     0,    10,    11,    12,    13,    14,    15,    16,
      17,    18,    19,    20,    21,    22,    23,    24,    25,    26,
      27,    28,    29,    30,    31,    32,    33,    34,    35,    36,
     190,    37,     0,    38,     0,    39,     0,     0,     2,     3,
       4,     5,     6,     7,     8,   127,     0,     0,     0,     0,
       0,     0,     0,     0,     9,   119,     0,    10,    11,    12,
      13,    14,    15,    16,    17,    18,    19,    20,    21,    22,
      23,    24,    25,    26,    27,    28,    29,    30,    31,    32,
      33,    34,    35,    36,   118,    37,     0,    38,   118,    39,
       0,     0,     0,    37,   119,    38,   171,     0,   119,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,     0,     0,     0,     0,     0,     0,     0,     0,
       0,     0,    37,   120,    38,     0,    37,   165,    38
};

static const yytype_int16 yycheck[] =
{
       0,     8,     1,    60,     8,    60,     3,    18,     5,   102,
      22,    23,     1,    25,     8,     1,    69,    56,   111,    58,
      60,    52,     1,    18,    36,    56,     3,    58,     5,    60,
       3,     8,     5,    51,    52,     8,     1,    37,    23,     8,
      54,    40,     3,    51,     5,     1,    57,     8,   101,   102,
      62,    59,    59,    23,    66,    59,     1,    69,   111,    59,
      60,    61,    57,    52,    61,    59,    52,    56,    57,    58,
      56,    60,    58,    52,    60,    26,    75,    56,    78,    58,
      92,    60,    59,    82,    57,     1,     1,    52,    57,   101,
     102,    56,    52,    58,    55,    94,    52,   150,   151,   111,
      56,     8,    58,     3,    60,     5,   159,    52,     8,   108,
       8,    56,     3,    58,     5,    60,     8,     8,   117,   119,
      18,   174,   121,    16,     8,   125,     8,     8,     3,   129,
       5,   130,   185,     8,     8,     8,    52,    52,   150,   151,
      56,    56,    58,    58,    60,    60,     0,   159,    16,    56,
      55,    58,    59,     8,     3,    38,     5,     8,    56,    59,
      58,    59,   174,    56,   163,    58,    57,    59,   167,    55,
     169,    20,   172,   185,    56,    59,    58,    59,    59,    20,
      55,    18,    55,    57,     1,    51,     7,    52,    51,    61,
      61,   190,     9,    10,    11,    12,    13,    14,    15,    61,
      55,   201,    85,    62,    20,   205,     7,     5,    25,    61,
      36,    28,    29,    30,    31,    32,    33,    34,    35,    36,
      37,    38,    39,    40,    41,    42,    43,    44,    45,    46,
      47,    48,    49,    50,    51,    52,    53,    54,     1,    56,
      57,    58,    27,    60,    69,   115,     9,    10,    11,    12,
      13,    14,    15,    61,    36,    78,    85,    -1,    -1,    -1,
      -1,    -1,    25,    -1,    -1,    28,    29,    30,    31,    32,
      33,    34,    35,    36,    37,    38,    39,    40,    41,    42,
      43,    44,    45,    46,    47,    48,    49,    50,    51,    52,
      53,    54,     1,    56,    -1,    58,    59,    60,    -1,    -1,
       9,    10,    11,    12,    13,    14,    15,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    25,    -1,    -1,    28,
      29,    30,    31,    32,    33,    34,    35,    36,    37,    38,
      39,    40,    41,    42,    43,    44,    45,    46,    47,    48,
      49,    50,    51,    52,    53,    54,     1,    56,    -1,    58,
      -1,    60,    -1,    -1,     9,    10,    11,    12,    13,    14,
      15,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      25,    -1,    -1,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
       1,    56,    -1,    58,    -1,    60,    -1,    -1,     9,    10,
      11,    12,    13,    14,    15,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    25,    -1,    -1,    28,    29,    30,
      31,    32,    33,    34,    35,    36,    37,    38,    39,    40,
      41,    42,    43,    44,    45,    46,    47,    48,    49,    50,
      51,    52,    53,    54,     1,    56,    -1,    58,    -1,    60,
      -1,    -1,     9,    10,    11,    12,    13,    14,    15,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    25,    -1,
      -1,    28,    29,    30,    31,    32,    33,    34,    35,    36,
      37,    38,    39,    40,    41,    42,    43,    44,    45,    46,
      47,    48,    49,    50,    51,    52,    53,    54,     1,    56,
      -1,    58,    -1,    60,    -1,    -1,     9,    10,    11,    12,
      13,    14,    15,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    25,    -1,    -1,    28,    29,    30,    31,    32,
      33,    34,    35,    36,    37,    38,    39,    40,    41,    42,
      43,    44,    45,    46,    47,    48,    49,    50,    51,    52,
      53,    54,     1,    56,    -1,    58,    -1,    60,    -1,    -1,
       9,    10,    11,    12,    13,    14,    15,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    25,    -1,    -1,    28,
      29,    30,    31,    32,    33,    34,    35,    36,    37,    38,
      39,    40,    41,    42,    43,    44,    45,    46,    47,    48,
      49,    50,    51,    52,    53,    54,     1,    56,    -1,    58,
      -1,    60,    -1,    -1,     9,    10,    11,    12,    13,    14,
      15,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      25,    -1,    -1,    28,    29,    30,    31,    32,    33,    34,
      35,    36,    37,    38,    39,    40,    41,    42,    43,    44,
      45,    46,    47,    48,    49,    50,    51,    52,    53,    54,
       1,    56,    -1,    58,    -1,    60,    -1,    -1,     9,    10,
      11,    12,    13,    14,    15,     8,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    25,    18,    -1,    28,    29,    30,
      31,    32,    33,    34,    35,    36,    37,    38,    39,    40,
      41,    42,    43,    44,    45,    46,    47,    48,    49,    50,
      51,    52,    53,    54,     8,    56,    -1,    58,     8,    60,
      -1,    -1,    -1,    56,    18,    58,    59,    -1,    18,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    56,    57,    58,    -1,    56,    57,    58
};

/* YYSTOS[STATE-NUM] -- The symbol kind of the accessing symbol of
   state STATE-NUM.  */
static const yytype_int8 yystos[] =
{
       0,     1,     9,    10,    11,    12,    13,    14,    15,    25,
      28,    29,    30,    31,    32,    33,    34,    35,    36,    37,
      38,    39,    40,    41,    42,    43,    44,    45,    46,    47,
      48,    49,    50,    51,    52,    53,    54,    56,    58,    60,
      68,    74,    75,    76,    77,    78,    79,    80,    81,    85,
      89,    90,    91,    92,    93,    94,    95,    96,    90,    60,
      60,    60,    23,    68,    68,    68,    54,    69,     1,    56,
      58,    68,    70,    71,    73,     1,    57,    82,    83,    84,
      87,    94,     1,    51,    59,    86,    87,    88,    94,    26,
      16,    90,    23,     0,     1,    94,    94,    94,    68,    16,
       1,    60,    64,    65,    68,    70,    71,    72,    55,     1,
      57,    64,    72,    51,    59,    66,    67,    55,     8,    18,
      57,     1,    84,    94,     8,    18,    57,     8,    59,    20,
       1,    51,    87,    88,     8,    59,    51,    51,    52,    68,
      61,    61,    61,     8,    55,     1,    72,     1,    65,    72,
       3,     5,     8,    55,    90,    57,     1,    72,    57,     7,
      51,    67,    90,     1,    94,    57,    57,     1,    94,     1,
      94,    59,    20,    59,    62,    61,    61,    55,    55,    72,
      72,    57,    57,     1,    72,     7,     8,    59,     8,    59,
       1,    94,    72,     8,    59,     8,    59,     1,    72,    59,
      59,    20,    59,    59,    94,    27,    94,    61
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
      80,    80,    81,    81,    81,    81,    81,    81,    81,    82,
      82,    82,    82,    83,    83,    84,    84,    85,    85,    85,
      85,    85,    86,    86,    87,    87,    88,    88,    88,    88,
      89,    89,    89,    89,    89,    89,    89,    89,    89,    90,
      90,    91,    91,    91,    91,    92,    92,    93,    93,    93,
      94,    94,    94,    94,    95,    96,    96
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
       3,     3,     1,     1,     1,     1,     1,     1,     1,     3,
       3,     3,     3,     2,     1,     2,     2,     2,     3,     4,
       3,     4,     2,     1,     1,     1,     4,     4,     2,     2,
       2,     5,     6,     5,     6,     3,     4,     3,     4,     1,
       1,     4,     2,     4,     2,     1,     1,     4,     4,     4,
       1,     1,     1,     1,    10,     1,     1
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
#line 110 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                               { (yyval.bsqon_t_list) = BSQON_TYPE_AST_ListCons((yyvsp[0].bsqon_t), (yyvsp[-1].bsqon_t_list)); }
#line 1838 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 3: /* bsqontypel: bsqontypel_entry  */
#line 111 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                      { (yyval.bsqon_t_list) = BSQON_TYPE_AST_ListCons((yyvsp[0].bsqon_t), NULL); }
#line 1844 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 4: /* bsqontypel_entry: bsqontype ","  */
#line 115 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                       { (yyval.bsqon_t) = (yyvsp[-1].bsqon_t); }
#line 1850 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 5: /* bsqontypel_entry: error ","  */
#line 116 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                     { (yyval.bsqon_t) = BSQON_TYPE_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1]))); yyerrok; }
#line 1856 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 6: /* bsqonnametypel: bsqonnametypel bsqonnametypel_entry  */
#line 120 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                       { (yyval.bsqon_t_namedlist) = BSQON_TYPE_AST_NamedListCons((yyvsp[0].bsqon_t_nametypel_entry), (yyvsp[-1].bsqon_t_namedlist)); }
#line 1862 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 7: /* bsqonnametypel: bsqonnametypel_entry  */
#line 121 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                          { (yyval.bsqon_t_namedlist) = BSQON_TYPE_AST_NamedListCons((yyvsp[0].bsqon_t_nametypel_entry), NULL); }
#line 1868 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 8: /* bsqonnametypel_entry: "identifier" ":" bsqontype ","  */
#line 125 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                                  { (yyval.bsqon_t_nametypel_entry) = BSQON_TYPE_AST_NamedListEntryCreate((yyvsp[-3].str), (yyvsp[-1].bsqon_t)); }
#line 1874 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 9: /* bsqonnametypel_entry: "identifier" ":" error ","  */
#line 126 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                                { (yyval.bsqon_t_nametypel_entry) = BSQON_TYPE_AST_NamedListEntryCreate((yyvsp[-3].str), BSQON_TYPE_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1])))); yyerrok; }
#line 1880 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 10: /* bsqonnominaltype: "type name"  */
#line 130 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                        { (yyval.bsqon_t) = BSQON_AST_NominalNodeCreate((yyvsp[0].str), NULL); }
#line 1886 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 11: /* bsqonnominaltype: "type name" bsqontermslist  */
#line 131 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                         { (yyval.bsqon_t) = BSQON_AST_NominalNodeCreate((yyvsp[-1].str), (yyvsp[0].bsqon_t_list)); }
#line 1892 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 12: /* bsqonnominaltype: bsqonnominaltype "::" "type name"  */
#line 132 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                                            { (yyval.bsqon_t) = BSQON_AST_NominalExtNodeCreate(BSQON_AST_asNominalNode((yyvsp[-2].bsqon_t)), (yyvsp[0].str)); }
#line 1898 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 13: /* bsqontermslist: '<' bsqontype '>'  */
#line 136 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                     { (yyval.bsqon_t_list) = BSQON_TYPE_AST_ListCons((yyvsp[-1].bsqon_t), NULL); }
#line 1904 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 14: /* bsqontermslist: '<' bsqontypel bsqontype '>'  */
#line 137 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                  { (yyval.bsqon_t_list) = BSQON_TYPE_AST_ListCompleteParse(BSQON_TYPE_AST_ListCons((yyvsp[-1].bsqon_t), (yyvsp[-2].bsqon_t_list))); }
#line 1910 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 15: /* bsqontermslist: '<' error '>'  */
#line 138 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                   { (yyval.bsqon_t_list) = BSQON_TYPE_AST_ListCons(BSQON_TYPE_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1]))), NULL); yyerrok; }
#line 1916 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 16: /* bsqontermslist: '<' bsqontypel error '>'  */
#line 139 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                              { (yyval.bsqon_t_list) = BSQON_TYPE_AST_ListCompleteParse(BSQON_TYPE_AST_ListCons(BSQON_TYPE_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1]))), (yyvsp[-2].bsqon_t_list))); yyerrok; }
#line 1922 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 17: /* bsqontupletype: '[' ']'  */
#line 143 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
           { (yyval.bsqon_t) = BSQON_AST_TupleNodeCreate(NULL); }
#line 1928 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 18: /* bsqontupletype: '[' bsqontype ']'  */
#line 144 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                       { (yyval.bsqon_t) = BSQON_AST_TupleNodeCreate(BSQON_TYPE_AST_ListCons((yyvsp[-1].bsqon_t), NULL)); }
#line 1934 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 19: /* bsqontupletype: '[' bsqontypel bsqontype ']'  */
#line 145 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                  { (yyval.bsqon_t) = BSQON_AST_TupleNodeCreate(BSQON_TYPE_AST_ListCompleteParse(BSQON_TYPE_AST_ListCons((yyvsp[-1].bsqon_t), (yyvsp[-2].bsqon_t_list)))); }
#line 1940 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 20: /* bsqontupletype: '[' error ']'  */
#line 146 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                   { (yyval.bsqon_t) = BSQON_AST_TupleNodeCreate(BSQON_TYPE_AST_ListCons(BSQON_TYPE_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1]))), NULL)); yyerrok; }
#line 1946 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 21: /* bsqontupletype: '[' bsqontypel error ']'  */
#line 147 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                              { (yyval.bsqon_t) = BSQON_AST_TupleNodeCreate(BSQON_TYPE_AST_ListCompleteParse(BSQON_TYPE_AST_ListCons(BSQON_TYPE_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1]))), (yyvsp[-2].bsqon_t_list)))); yyerrok; }
#line 1952 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 22: /* bsqonrecordtype: '{' '}'  */
#line 151 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
           { (yyval.bsqon_t) = BSQON_AST_RecordNodeCreate(NULL); }
#line 1958 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 23: /* bsqonrecordtype: '{' "identifier" ":" bsqontype '}'  */
#line 152 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                                  { (yyval.bsqon_t) = BSQON_AST_RecordNodeCreate(BSQON_TYPE_AST_NamedListCons(BSQON_TYPE_AST_NamedListEntryCreate((yyvsp[-3].str), (yyvsp[-1].bsqon_t)), NULL)); }
#line 1964 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 24: /* bsqonrecordtype: '{' bsqonnametypel "identifier" ":" bsqontype '}'  */
#line 153 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                                                 { (yyval.bsqon_t) = BSQON_AST_RecordNodeCreate(BSQON_TYPE_AST_NamedListCompleteParse(BSQON_TYPE_AST_NamedListCons(BSQON_TYPE_AST_NamedListEntryCreate((yyvsp[-3].str), (yyvsp[-1].bsqon_t)), (yyvsp[-4].bsqon_t_namedlist)))); }
#line 1970 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 25: /* bsqonrecordtype: '{' "identifier" ":" error '}'  */
#line 154 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                              { (yyval.bsqon_t) = BSQON_AST_RecordNodeCreate(BSQON_TYPE_AST_NamedListCons(BSQON_TYPE_AST_NamedListEntryCreate((yyvsp[-3].str), BSQON_TYPE_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1])))), NULL)); yyerrok; }
#line 1976 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 26: /* bsqonrecordtype: '{' bsqonnametypel "identifier" ":" error '}'  */
#line 155 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                                             { (yyval.bsqon_t) = BSQON_AST_RecordNodeCreate(BSQON_TYPE_AST_NamedListCompleteParse(BSQON_TYPE_AST_NamedListCons(BSQON_TYPE_AST_NamedListEntryCreate((yyvsp[-3].str), BSQON_TYPE_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1])))), (yyvsp[-4].bsqon_t_namedlist)))); yyerrok; }
#line 1982 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 27: /* bsqontype: bsqonnominaltype  */
#line 159 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                    { (yyval.bsqon_t) = (yyvsp[0].bsqon_t); }
#line 1988 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 28: /* bsqontype: bsqontupletype  */
#line 160 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                    { (yyval.bsqon_t) = (yyvsp[0].bsqon_t); }
#line 1994 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 29: /* bsqontype: bsqonrecordtype  */
#line 161 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                     { (yyval.bsqon_t) = (yyvsp[0].bsqon_t); }
#line 2000 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 30: /* bsqontype: bsqontype SYM_AMP bsqontype  */
#line 162 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                 { (yyval.bsqon_t) = BSQON_AST_ConjunctionCreate((yyvsp[-2].bsqon_t), (yyvsp[0].bsqon_t)); }
#line 2006 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 31: /* bsqontype: bsqontype SYM_BAR bsqontype  */
#line 163 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                 { (yyval.bsqon_t) = BSQON_AST_UnionCreate((yyvsp[-2].bsqon_t), (yyvsp[0].bsqon_t)); }
#line 2012 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 32: /* bsqontype: '(' bsqontype ')'  */
#line 164 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                       { (yyval.bsqon_t) = (yyvsp[-1].bsqon_t); }
#line 2018 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 33: /* bsqontype: '(' error ')'  */
#line 165 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                   { (yyval.bsqon_t) = BSQON_TYPE_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1]))); yyerrok; }
#line 2024 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 34: /* bsqontspec: bsqonnominaltype  */
#line 169 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                    { (yyval.bsqon_t) = (yyvsp[0].bsqon_t); }
#line 2030 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 35: /* bsqontspec: bsqontupletype  */
#line 170 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                    { (yyval.bsqon_t) = (yyvsp[0].bsqon_t); }
#line 2036 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 36: /* bsqontspec: bsqonrecordtype  */
#line 171 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                     { (yyval.bsqon_t) = (yyvsp[0].bsqon_t); }
#line 2042 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 37: /* bsqonliteral: "none"  */
#line 175 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralSingletonNodeCreate(BSQON_AST_TAG_None, MK_SPOS_S((yylsp[0]))); }
#line 2048 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 38: /* bsqonliteral: "nothing"  */
#line 176 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralSingletonNodeCreate(BSQON_AST_TAG_Nothing, MK_SPOS_S((yylsp[0]))); }
#line 2054 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 39: /* bsqonliteral: "true"  */
#line 177 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralSingletonNodeCreate(BSQON_AST_TAG_True, MK_SPOS_S((yylsp[0]))); }
#line 2060 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 40: /* bsqonliteral: "false"  */
#line 178 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralSingletonNodeCreate(BSQON_AST_TAG_False, MK_SPOS_S((yylsp[0]))); }
#line 2066 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 41: /* bsqonliteral: TOKEN_NAT  */
#line 179 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_Nat, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2072 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 42: /* bsqonliteral: TOKEN_INT  */
#line 180 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_Int, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2078 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 43: /* bsqonliteral: TOKEN_BIG_NAT  */
#line 181 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_BigNat, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2084 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 44: /* bsqonliteral: TOKEN_BIG_INT  */
#line 182 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_BigInt, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2090 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 45: /* bsqonliteral: TOKEN_RATIONAL  */
#line 183 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_Rational, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2096 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 46: /* bsqonliteral: TOKEN_FLOAT  */
#line 184 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_Float, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2102 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 47: /* bsqonliteral: TOKEN_DOUBLE  */
#line 185 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_Decimal, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2108 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 48: /* bsqonliteral: TOKEN_BYTE_BUFFER  */
#line 186 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_ByteBuffer, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2114 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 49: /* bsqonliteral: TOKEN_UUID_V4  */
#line 187 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_UUIDv4, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2120 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 50: /* bsqonliteral: TOKEN_UUID_V7  */
#line 188 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_UUIDv7, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2126 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 51: /* bsqonliteral: TOKEN_SHA_HASH  */
#line 189 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_SHAHashcode, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2132 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 52: /* bsqonliteral: TOKEN_STRING  */
#line 190 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStringNodeCreate(BSQON_AST_TAG_String, MK_SPOS_S((yylsp[0])), (yyvsp[0].bstr)); }
#line 2138 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 53: /* bsqonliteral: TOKEN_ASCII_STRING  */
#line 191 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStringNodeCreate(BSQON_AST_TAG_ASCIIString, MK_SPOS_S((yylsp[0])), (yyvsp[0].bstr)); }
#line 2144 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 54: /* bsqonliteral: TOKEN_PATH_ITEM  */
#line 192 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStringNodeCreate(BSQON_AST_TAG_NakedPath, MK_SPOS_S((yylsp[0])), (yyvsp[0].bstr)); }
#line 2150 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 55: /* bsqonliteral: TOKEN_REGEX  */
#line 193 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStringNodeCreate(BSQON_AST_TAG_Regex, MK_SPOS_S((yylsp[0])), (yyvsp[0].bstr)); }
#line 2156 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 56: /* bsqonliteral: TOKEN_DATE_TIME  */
#line 194 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_DateTime, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2162 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 57: /* bsqonliteral: TOKEN_UTC_DATE_TIME  */
#line 195 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_UTCDateTime, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2168 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 58: /* bsqonliteral: TOKEN_PLAIN_DATE  */
#line 196 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_PlainDate, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2174 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 59: /* bsqonliteral: TOKEN_PLAIN_TIME  */
#line 197 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_PlainTime, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2180 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 60: /* bsqonliteral: TOKEN_LOGICAL_TIME  */
#line 198 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_LogicalTime, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2186 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 61: /* bsqonliteral: TOKEN_TICK_TIME  */
#line 199 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_TickTime, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2192 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 62: /* bsqonliteral: TOKEN_TIMESTAMP  */
#line 200 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_LiteralStandardNodeCreate(BSQON_AST_TAG_Timestamp, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2198 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 63: /* bsqonunspecvar: "unspec identifier"  */
#line 204 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_NameNodeCreate(BSQON_AST_TAG_UnspecIdentifier, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2204 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 64: /* bsqonidentifier: KW_SRC  */
#line 208 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                { (yyval.bsqon) = BSQON_AST_NameNodeCreate(BSQON_AST_TAG_Identifier, MK_SPOS_S((yylsp[0])), "$src"); }
#line 2210 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 65: /* bsqonidentifier: "identifier"  */
#line 209 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                      { (yyval.bsqon) = BSQON_AST_NameNodeCreate(BSQON_AST_TAG_Identifier, MK_SPOS_S((yylsp[0])), (yyvsp[0].str)); }
#line 2216 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 66: /* bsqonscopedidentifier: bsqonnominaltype "::" "identifier"  */
#line 213 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                                      { (yyval.bsqon) = BSQON_AST_ScopedNameNodeCreate(MK_SPOS_R((yylsp[-2]), (yylsp[0])), (yyvsp[-2].bsqon_t), (yyvsp[0].str)); }
#line 2222 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 67: /* bsqonstringof: TOKEN_STRING bsqonnominaltype  */
#line 217 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                 { (yyval.bsqon) = BSQON_AST_StringOfNodeCreate(BSQON_AST_TAG_StringOf, MK_SPOS_R((yylsp[-1]), (yylsp[0])), (yyvsp[-1].bstr), (yyvsp[0].bsqon_t)); }
#line 2228 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 68: /* bsqonstringof: TOKEN_ASCII_STRING bsqonnominaltype  */
#line 218 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                         { (yyval.bsqon) = BSQON_AST_StringOfNodeCreate(BSQON_AST_TAG_ASCIIStringOf, MK_SPOS_R((yylsp[-1]), (yylsp[0])), (yyvsp[-1].bstr), (yyvsp[0].bsqon_t)); }
#line 2234 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 69: /* bsqonpath: TOKEN_PATH_ITEM bsqonnominaltype  */
#line 222 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                    { (yyval.bsqon) = BSQON_AST_PathNodeCreate(MK_SPOS_R((yylsp[-1]), (yylsp[0])), BSQON_AST_asLiteralStringNode(BSQON_AST_LiteralStringNodeCreate(BSQON_AST_TAG_NakedPath, MK_SPOS_S((yylsp[-1])), (yyvsp[-1].bstr))), (yyvsp[0].bsqon_t)); }
#line 2240 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 70: /* bsqontypeliteral: "numberino" SYM_UNDERSCORE bsqonnominaltype  */
#line 226 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                                   {
      yyerror("Missing numeric specifier");
      (yyval.bsqon) = BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-2])));
   }
#line 2249 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 71: /* bsqontypeliteral: bsqonliteral SYM_UNDERSCORE bsqonnominaltype  */
#line 230 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                                  {
      (yyval.bsqon) = BSQON_AST_TypedLiteralNodeCreate(MK_SPOS_R((yylsp[-2]), (yylsp[0])), (yyvsp[-2].bsqon), (yyvsp[0].bsqon_t));
   }
#line 2257 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 78: /* bsqonterminal: bsqontypeliteral  */
#line 236 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                                                                                                          { (yyval.bsqon) = (yyvsp[0].bsqon); }
#line 2263 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 79: /* bsqon_mapentry: bsqonval SYM_ENTRY bsqonval  */
#line 240 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                               { (yyval.bsqon) = BSQON_AST_MapEntryNodeCreate(MK_SPOS_R((yylsp[-2]), (yylsp[0])), (yyvsp[-2].bsqon), (yyvsp[0].bsqon)); }
#line 2269 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 80: /* bsqon_mapentry: error SYM_ENTRY bsqonval  */
#line 241 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                              { (yyval.bsqon) = BSQON_AST_MapEntryNodeCreate(MK_SPOS_R((yylsp[-2]), (yylsp[0])), BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-2]))), (yyvsp[0].bsqon)); yyerrok; }
#line 2275 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 81: /* bsqon_mapentry: bsqonval SYM_ENTRY error  */
#line 242 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                              { (yyval.bsqon) = BSQON_AST_MapEntryNodeCreate(MK_SPOS_R((yylsp[-2]), (yylsp[0])), (yyvsp[-2].bsqon), BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[0])))); yyerrok; }
#line 2281 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 82: /* bsqon_mapentry: error SYM_ENTRY error  */
#line 243 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                           { (yyval.bsqon) = BSQON_AST_MapEntryNodeCreate(MK_SPOS_R((yylsp[-2]), (yylsp[0])), BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-2]))), BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[0])))); yyerrok; }
#line 2287 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 83: /* bsqonvall: bsqonvall bsqonl_entry  */
#line 247 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                          { (yyval.bsqon_list) = BSQON_AST_ListCons((yyvsp[0].bsqon), (yyvsp[-1].bsqon_list)); }
#line 2293 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 84: /* bsqonvall: bsqonl_entry  */
#line 248 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                  { (yyval.bsqon_list) = BSQON_AST_ListCons((yyvsp[0].bsqon), NULL); }
#line 2299 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 85: /* bsqonl_entry: bsqon_braceval ","  */
#line 252 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                            { (yyval.bsqon) = (yyvsp[-1].bsqon); }
#line 2305 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 86: /* bsqonl_entry: error ","  */
#line 253 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                     { (yyval.bsqon) = BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1]))); yyerrok; }
#line 2311 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 87: /* bsqonbracketvalue: '[' ']'  */
#line 257 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
           { (yyval.bsqon) = BSQON_AST_BracketValueNodeCreate(MK_SPOS_R((yylsp[-1]), (yylsp[0])), NULL); }
#line 2317 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 88: /* bsqonbracketvalue: '[' bsqonval ']'  */
#line 258 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                      { (yyval.bsqon) = BSQON_AST_BracketValueNodeCreate(MK_SPOS_R((yylsp[-2]), (yylsp[0])), BSQON_AST_ListCons((yyvsp[-1].bsqon), NULL)); }
#line 2323 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 89: /* bsqonbracketvalue: '[' bsqonvall bsqonval ']'  */
#line 259 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                { (yyval.bsqon) = BSQON_AST_BracketValueNodeCreate(MK_SPOS_R((yylsp[-3]), (yylsp[0])), BSQON_AST_ListCompleteParse(BSQON_AST_ListCons((yyvsp[-1].bsqon), (yyvsp[-2].bsqon_list)))); }
#line 2329 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 90: /* bsqonbracketvalue: '[' error ']'  */
#line 260 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                   { (yyval.bsqon) = BSQON_AST_BracketValueNodeCreate(MK_SPOS_R((yylsp[-2]), (yylsp[0])), BSQON_AST_ListCons(BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1]))), NULL)); yyerrok; }
#line 2335 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 91: /* bsqonbracketvalue: '[' bsqonvall error ']'  */
#line 261 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                             { (yyval.bsqon) = BSQON_AST_BracketValueNodeCreate(MK_SPOS_R((yylsp[-3]), (yylsp[0])), BSQON_AST_ListCompleteParse(BSQON_AST_ListCons(BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1]))), (yyvsp[-2].bsqon_list)))); yyerrok; }
#line 2341 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 92: /* bsqonnamevall: bsqonnamevall bsqonnameval_entry  */
#line 265 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                    { (yyval.bsqon_namedlist) = BSQON_AST_NamedListCons((yyvsp[0].bsqon_nameval_entry), (yyvsp[-1].bsqon_namedlist)); }
#line 2347 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 93: /* bsqonnamevall: bsqonnameval_entry  */
#line 266 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                        { (yyval.bsqon_namedlist) = BSQON_AST_NamedListCons((yyvsp[0].bsqon_nameval_entry), NULL); }
#line 2353 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 95: /* bsqon_braceval: bsqon_mapentry  */
#line 270 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                             { (yyval.bsqon) = (yyvsp[0].bsqon); }
#line 2359 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 96: /* bsqonnameval_entry: "identifier" SYM_EQUALS bsqonval ","  */
#line 274 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                                  { (yyval.bsqon_nameval_entry) = BSQON_AST_NamedListEntryCreate((yyvsp[-3].str), (yyvsp[-1].bsqon)); }
#line 2365 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 97: /* bsqonnameval_entry: "identifier" SYM_EQUALS error ","  */
#line 275 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                                 { (yyval.bsqon_nameval_entry) = BSQON_AST_NamedListEntryCreate((yyvsp[-3].str), BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1])))); yyerrok; }
#line 2371 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 98: /* bsqonnameval_entry: bsqon_braceval ","  */
#line 276 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                              { (yyval.bsqon_nameval_entry) = BSQON_AST_NamedListEntryCreate(NULL, (yyvsp[-1].bsqon)); }
#line 2377 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 99: /* bsqonnameval_entry: error ","  */
#line 277 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                     { (yyval.bsqon_nameval_entry) = BSQON_AST_NamedListEntryCreate(NULL, BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1])))); yyerrok; }
#line 2383 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 100: /* bsqonbracevalue: '{' '}'  */
#line 281 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
           { (yyval.bsqon) = BSQON_AST_BraceValueNodeCreate(MK_SPOS_R((yylsp[-1]), (yylsp[0])), NULL); }
#line 2389 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 101: /* bsqonbracevalue: '{' "identifier" SYM_EQUALS bsqonval '}'  */
#line 282 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                                  { (yyval.bsqon) = BSQON_AST_BraceValueNodeCreate(MK_SPOS_R((yylsp[-4]), (yylsp[0])), BSQON_AST_NamedListCons(BSQON_AST_NamedListEntryCreate((yyvsp[-3].str), (yyvsp[-1].bsqon)), NULL)); }
#line 2395 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 102: /* bsqonbracevalue: '{' bsqonnamevall "identifier" SYM_EQUALS bsqonval '}'  */
#line 283 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                                                { (yyval.bsqon) = BSQON_AST_BraceValueNodeCreate(MK_SPOS_R((yylsp[-5]), (yylsp[0])), BSQON_AST_NamedListCompleteParse(BSQON_AST_NamedListCons(BSQON_AST_NamedListEntryCreate((yyvsp[-3].str), (yyvsp[-1].bsqon)), (yyvsp[-4].bsqon_namedlist)))); }
#line 2401 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 103: /* bsqonbracevalue: '{' "identifier" SYM_EQUALS error '}'  */
#line 284 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                               { (yyval.bsqon) = BSQON_AST_BraceValueNodeCreate(MK_SPOS_R((yylsp[-4]), (yylsp[0])), BSQON_AST_NamedListCons(BSQON_AST_NamedListEntryCreate((yyvsp[-3].str), BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1])))), NULL)); yyerrok; }
#line 2407 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 104: /* bsqonbracevalue: '{' bsqonnamevall "identifier" SYM_EQUALS error '}'  */
#line 285 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                                             { (yyval.bsqon) = BSQON_AST_BraceValueNodeCreate(MK_SPOS_R((yylsp[-5]), (yylsp[0])), BSQON_AST_NamedListCompleteParse(BSQON_AST_NamedListCons(BSQON_AST_NamedListEntryCreate((yyvsp[-3].str), BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1])))), (yyvsp[-4].bsqon_namedlist)))); yyerrok; }
#line 2413 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 105: /* bsqonbracevalue: '{' bsqon_braceval '}'  */
#line 286 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                            { (yyval.bsqon) = BSQON_AST_BraceValueNodeCreate(MK_SPOS_R((yylsp[-2]), (yylsp[0])), BSQON_AST_NamedListCons(BSQON_AST_NamedListEntryCreate(NULL, (yyvsp[-1].bsqon)), NULL)); }
#line 2419 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 106: /* bsqonbracevalue: '{' bsqonnamevall bsqon_braceval '}'  */
#line 287 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                          { (yyval.bsqon) = BSQON_AST_BraceValueNodeCreate(MK_SPOS_R((yylsp[-3]), (yylsp[0])), BSQON_AST_NamedListCompleteParse(BSQON_AST_NamedListCons(BSQON_AST_NamedListEntryCreate(NULL, (yyvsp[-1].bsqon)), (yyvsp[-2].bsqon_namedlist)))); }
#line 2425 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 107: /* bsqonbracevalue: '{' error '}'  */
#line 288 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                   { (yyval.bsqon) = BSQON_AST_BraceValueNodeCreate(MK_SPOS_R((yylsp[-2]), (yylsp[0])), BSQON_AST_NamedListCons(BSQON_AST_NamedListEntryCreate(NULL, BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1])))), NULL)); yyerrok; }
#line 2431 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 108: /* bsqonbracevalue: '{' bsqonnamevall error '}'  */
#line 289 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                 { (yyval.bsqon) = BSQON_AST_BraceValueNodeCreate(MK_SPOS_R((yylsp[-3]), (yylsp[0])), BSQON_AST_NamedListCompleteParse(BSQON_AST_NamedListCons(BSQON_AST_NamedListEntryCreate(NULL, BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1])))), (yyvsp[-2].bsqon_namedlist)))); yyerrok; }
#line 2437 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 110: /* bsqonbracketbracevalue: bsqonbracevalue  */
#line 293 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                       { (yyval.bsqon) = (yyvsp[0].bsqon); }
#line 2443 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 111: /* bsqontypedvalue: '<' bsqontspec '>' bsqonbracketbracevalue  */
#line 297 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                             { (yyval.bsqon) = BSQON_AST_TypedValueNodeCreate(MK_SPOS_R((yylsp[-3]), (yylsp[0])), (yyvsp[0].bsqon), (yyvsp[-2].bsqon_t)); }
#line 2449 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 112: /* bsqontypedvalue: bsqonnominaltype bsqonbracketbracevalue  */
#line 298 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                             { (yyval.bsqon) = BSQON_AST_TypedValueNodeCreate(MK_SPOS_R((yylsp[-1]), (yylsp[0])), (yyvsp[0].bsqon), (yyvsp[-1].bsqon_t)); }
#line 2455 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 113: /* bsqontypedvalue: '<' error '>' bsqonbracketbracevalue  */
#line 299 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                          { (yyval.bsqon) = BSQON_AST_TypedValueNodeCreate(MK_SPOS_R((yylsp[-3]), (yylsp[0])), (yyvsp[0].bsqon), BSQON_TYPE_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-2])))); }
#line 2461 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 114: /* bsqontypedvalue: error bsqonbracketbracevalue  */
#line 300 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                  { (yyval.bsqon) = BSQON_AST_TypedValueNodeCreate(MK_SPOS_R((yylsp[-1]), (yylsp[0])), (yyvsp[0].bsqon), BSQON_TYPE_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[-1])))); }
#line 2467 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 116: /* bsqonstructvalue: bsqontypedvalue  */
#line 304 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                            { (yyval.bsqon) = (yyvsp[0].bsqon); }
#line 2473 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 117: /* bsqonspecialcons: "something" '(' bsqonval ')'  */
#line 308 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                 { (yyval.bsqon) = BSQON_AST_SpecialConsNodeCreate(BSQON_AST_TAG_SomethingCons, MK_SPOS_R((yylsp[-3]), (yylsp[0])), (yyvsp[-1].bsqon), "some"); }
#line 2479 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 118: /* bsqonspecialcons: "ok" '(' bsqonval ')'  */
#line 309 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                            { (yyval.bsqon) = BSQON_AST_SpecialConsNodeCreate(BSQON_AST_TAG_OkCons, MK_SPOS_R((yylsp[-3]), (yylsp[0])), (yyvsp[-1].bsqon), "ok"); }
#line 2485 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 119: /* bsqonspecialcons: "err" '(' bsqonval ')'  */
#line 310 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                             { (yyval.bsqon) = BSQON_AST_SpecialConsNodeCreate(BSQON_AST_TAG_ErrCons, MK_SPOS_R((yylsp[-3]), (yylsp[0])), (yyvsp[-1].bsqon), "err"); }
#line 2491 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 123: /* bsqonval: bsqonletexp  */
#line 314 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                                                    { (yyval.bsqon) = (yyvsp[0].bsqon); }
#line 2497 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 124: /* bsqonletexp: '(' KW_LET "identifier" ':' bsqontype SYM_EQUALS bsqonval KW_IN bsqonval ')'  */
#line 318 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
                                                                                   { (yyval.bsqon) = BSQON_AST_LetInNodeCreate(MK_SPOS_R((yylsp[-9]), (yylsp[0])), (yyvsp[-7].str), (yyvsp[-5].bsqon_t), (yyvsp[-3].bsqon), (yyvsp[-1].bsqon)); }
#line 2503 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 125: /* bsqonroot: bsqonval  */
#line 322 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
            { yybsqonval = (yyvsp[0].bsqon); (yyval.bsqon) = (yyvsp[0].bsqon); }
#line 2509 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;

  case 126: /* bsqonroot: error  */
#line 323 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"
           {yybsqonval = BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[0]))); (yyval.bsqon) = BSQON_AST_ErrorNodeCreate(MK_SPOS_S((yylsp[0]))); }
#line 2515 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"
    break;


#line 2519 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.tab.c"

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

#line 324 "/home/mark/Code/BosqueCore/src/bsqon/parser/lb/bsqon.y"


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
   
   if(!yyparse() || errorcount != 0) {
      return yybsqonval;
   }

   for(size_t i = 0; i < errorcount; ++i) {
      printf("%s\n", errors[i]);
      fflush(stdout);
   }
   exit(1);
}
#endif
