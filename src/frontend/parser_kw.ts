
////////////////////////////////////////////////////////////////////////////////
//Keywords

////
//Global keywords
const KW_recursive_q = "recursive?";
const KW_recursive = "recursive";

const KW_action = "action";
const KW__debug = "_debug";
const KW_abort = "abort";
const KW_assert = "assert";
const KW_bsqon = "bsqon";
const KW_dollarbsqon = "$bsqon";
const KW_do = "do";
const KW_elif = "elif";
const KW_else = "else";
const KW_env = "env";
const KW_err = "err";
const KW_false = "false";
const KW_fn = "fn";
const KW_if = "if";
const KW_implements = "implements";
const KW_let = "let";
const KW_match = "match";
const KW_none = "none";
const KW_ok = "ok";
const KW_option = "option";
const KW_pred = "pred";
const KW_ref = "ref";
const KW_return = "return";
const KW_result = "result";
const KW_some = "some";
const KW_this = "this";
const KW_self = "self";
const KW_switch = "switch";
const KW_then = "then";
const KW_true = "true";
const KW_var = "var";
const KW_yield = "yield";
const KW_under = "_";

const KW_debug = "debug";
const KW_release = "release";
const KW_safety = "safety";
const KW_spec = "spec";
const KW_test = "test";

////
//Declaration keywords
const KW_api = "api";
const KW_as = "as";
const KW_concept = "concept";
const KW_const = "const";
const KW_declare = "declare";
const KW_enum = "enum";
const KW_entity = "entity";
const KW_ensures = "ensures";
const KW_field = "field";
const KW_function = "function";
const KW_invariant = "invariant";
const KW_method = "method";
const KW_namespace = "namespace";
const KW_of = "of";
const KW_provides = "provides";
const KW_requires = "requires";
const KW_in = "in";
const KW_task = "task";
const KW_typedecl = "typedecl";
const KW_datatype = "datatype";
const KW_using = "using";
const KW_validate = "validate";
const KW_when = "when";
const KW_event = "event";
const KW_status = "status";
const KW_resource = "resource";
const KW_validator = "validator";
const KW_predicate = "predicate";

const KW_softcheck = "softcheck";
const KW_errtest = "errtest";
const KW_chktest = "chktest";

//reserved
const KW_operator = "operator";
const KW_type = "type";
const KW_literal = "literal";

const KeywordStrings = [
    KW_recursive_q,
    KW_recursive,
    
    KW_api,
    KW_as,
    KW_action,
    KW_bsqon,
    KW_dollarbsqon,
    KW__debug,
    KW_do,
    KW_abort,
    KW_assert,
    KW_concept,
    KW_const,
    KW_declare,
    KW_debug,
    KW_elif,
    KW_else,
    KW_enum,
    KW_env,
    KW_entity,
    KW_ensures,
    KW_err,
    KW_false,
    KW_field,
    KW_fn,
    KW_function,
    KW_if,
    KW_implements,
    KW_in,
    KW_invariant,
    KW_let,
    KW_literal,
    KW_match,
    KW_method,
    KW_namespace,
    KW_none,
    KW_of,
    KW_ok,
    KW_operator,
    KW_option,
    KW_pred,
    KW_predicate,
    KW_provides,
    KW_ref,
    KW_release,
    KW_return,
    KW_result,
    KW_requires,
    KW_self,
    KW_some,
    KW_safety,
    KW_spec,
    KW_switch,
    KW_task,
    KW_test,
    KW_then,
    KW_this,
    KW_true,
    KW_type,
    KW_typedecl,
    KW_datatype,
    KW_using,
    KW_validate,
    KW_var,
    KW_when,
    KW_yield,
    KW_under,
    KW_event,
    KW_status,
    KW_resource,
    KW_validator,
    KW_softcheck,
    KW_errtest,
    KW_chktest
].sort((a, b) => { return (a.length !== b.length) ? (b.length - a.length) : ((a !== b) ? (a < b ? -1 : 1) : 0); });

////////////////////////////////////////////////////////////////////////////////
//Attributes

const GeneralAttributes = [ 
    "private",
    "internal",
    "hidden",
    "public",

    "sensitive"
];

const APIDeclAttributes = [
    "export",
    "deterministic",
    "idempotent",
];

const InvokeAttributes = [
    "abstract",
    "override",
    "virtual",
];

const AllAttributes = [
    ...GeneralAttributes,
    ...APIDeclAttributes,
    ...InvokeAttributes
].sort((a, b) => { return (a.length !== b.length) ? (b.length - a.length) : ((a !== b) ? (a < b ? -1 : 1) : 0); });

const CoreOnlyAttributes = [
    "__internal",
    "__typedeclable",
    
    "__keycomparable",
    "__numeric",
    "__revalidator",
    "__crevalidator",
    "__pathvalidator",
    
    "__register",
    "__inline",
    "__safe",
    "__assume_safe",
    "__conditional_safe"
].sort((a, b) => { return (a.length !== b.length) ? (b.length - a.length) : ((a !== b) ? (a < b ? -1 : 1) : 0); });

////////////////////////////////////////////////////////////////////////////////
//Symbols

const SYM_lbrack = "[";
const SYM_lparen = "(";
const SYM_lbrace = "{";
const SYM_lbracebar = "{|";
const SYM_rbrack = "]";
const SYM_rparen = ")";
const SYM_rbrace = "}";
const SYM_rbracebar = "|}";
const SYM_langle = "<";
const SYM_rangle = ">";


const SYM_amp = "&";
const SYM_bar = "|";
const SYM_at = "@";
const SYM_atat = "@@";
const SYM_hash = "#";
const SYM_bang = "!";
const SYM_colon = ":";
const SYM_coloncolon = "::";
const SYM_coma = ",";
const SYM_dot = ".";
const SYM_eq = "=";
const SYM_semicolon = ";";
const SYM_question = "?";
const SYM_land = "/\\";
const SYM_lor = "\\/";
const SYM_dotdotdot = "...";
const SYM_HOLE = "$?_";

const SYM_positive = " +";
const SYM_negate = " -";

const SYM_ampamp = " && ";
const SYM_bangeq = " != ";
const SYM_bangeqeq = " !== ";
const SYM_eqeq = " == ";
const SYM_eqeqeq = " === ";
const SYM_bigarrow = " => ";
const SYM_implies = " ==> ";
const SYM_iff = " <==> ";
const SYM_arrow = " -> ";
const SYM_barbar = " || ";
const SYM_plus = " + ";
const SYM_lt = " < ";
const SYM_lteq = " <= ";
const SYM_gt = " > ";
const SYM_gteq = " >= ";
const SYM_minus = " - ";
const SYM_times = " * ";
const SYM_div = " // ";
const SYM_wildcard = "**";

//Reserved
const SYM_questionquestion = "??";

const LeftScanParens = [SYM_lbrack, SYM_lparen, SYM_lbrace, SYM_lbracebar, SYM_langle];
const RightScanParens = [SYM_rbrack, SYM_rparen, SYM_rbrace, SYM_rbracebar, SYM_rangle];

const StandardSymbols = [
    SYM_amp,
    SYM_bar,
    SYM_at,
    SYM_bang,
    SYM_colon,
    SYM_coloncolon,
    SYM_coma,
    SYM_dot,
    SYM_eq,
    SYM_semicolon,
    SYM_question,
    SYM_land,
    SYM_lor,
    SYM_dotdotdot,
    SYM_HOLE,
    SYM_wildcard,

    SYM_atat,
    SYM_hash,
    SYM_questionquestion
].sort((a, b) => { return (a.length !== b.length) ? (b.length - a.length) : ((a !== b) ? (a < b ? -1 : 1) : 0); });

const SpaceRequiredSymbols = [
    SYM_ampamp,
    SYM_bangeq,
    SYM_bangeqeq,
    SYM_eqeq,
    SYM_eqeqeq,
    SYM_bigarrow,
    SYM_implies,
    SYM_iff,
    SYM_arrow,
    SYM_barbar,
    SYM_plus,
    SYM_lt,
    SYM_lteq,
    SYM_gt,
    SYM_gteq,
    SYM_minus,
    SYM_times,
    SYM_div
].sort((a, b) => { return (a.length !== b.length) ? (b.length - a.length) : ((a !== b) ? (a < b ? -1 : 1) : 0); });


const SpaceFrontSymbols = [
    SYM_positive,
    SYM_negate
].sort((a, b) => { return (a.length !== b.length) ? (b.length - a.length) : ((a !== b) ? (a < b ? -1 : 1) : 0); });

const ParenSymbols = [
    ...LeftScanParens,
    ...RightScanParens
].sort((a, b) => { return (a.length !== b.length) ? (b.length - a.length) : ((a !== b) ? (a < b ? -1 : 1) : 0); });

export {
    KeywordStrings,
    GeneralAttributes, APIDeclAttributes, InvokeAttributes, AllAttributes, CoreOnlyAttributes,
    LeftScanParens, RightScanParens,
    SpaceRequiredSymbols, SpaceFrontSymbols, StandardSymbols, ParenSymbols,

    KW_recursive_q,
    KW_recursive,
    
    KW_api,
    KW_as,
    KW_action,
    KW_bsqon,
    KW_dollarbsqon,
    KW__debug,
    KW_do,
    KW_abort,
    KW_assert,
    KW_concept,
    KW_const,
    KW_declare,
    KW_debug,
    KW_elif,
    KW_else,
    KW_enum,
    KW_env,
    KW_entity,
    KW_ensures,
    KW_err,
    KW_false,
    KW_field,
    KW_fn,
    KW_function,
    KW_if,
    KW_implements,
    KW_in,
    KW_invariant,
    KW_let,
    KW_literal,
    KW_match,
    KW_method,
    KW_namespace,
    KW_none,
    KW_of,
    KW_ok,
    KW_operator,
    KW_option,
    KW_pred,
    KW_predicate,
    KW_provides,
    KW_ref,
    KW_release,
    KW_return,
    KW_result,
    KW_requires,
    KW_self,
    KW_some,
    KW_safety,
    KW_spec,
    KW_switch,
    KW_task,
    KW_test,
    KW_then,
    KW_this,
    KW_true,
    KW_type,
    KW_typedecl,
    KW_datatype,
    KW_using,
    KW_validate,
    KW_var,
    KW_when,
    KW_yield,
    KW_under,
    KW_event,
    KW_resource,
    KW_status,
    KW_validator,
    KW_softcheck,
    KW_errtest,
    KW_chktest,

    SYM_lbrack,
    SYM_lparen,
    SYM_lbrace,
    SYM_langle,
    SYM_lbracebar,
    SYM_rbrack,
    SYM_rparen,
    SYM_rbrace,
    SYM_rangle,
    SYM_rbracebar,

    SYM_amp,
    SYM_bar,
    SYM_at,
    SYM_atat,
    SYM_hash,
    SYM_bang,
    SYM_colon,
    SYM_coloncolon,
    SYM_coma,
    SYM_dot,
    SYM_eq,
    SYM_semicolon,
    SYM_question,
    SYM_land,
    SYM_lor,
    SYM_dotdotdot,
    SYM_HOLE,
    SYM_wildcard,

    SYM_positive,
    SYM_negate,

    SYM_ampamp,
    SYM_bangeq,
    SYM_bangeqeq,
    SYM_eqeq,
    SYM_eqeqeq,
    SYM_bigarrow,
    SYM_implies,
    SYM_iff,
    SYM_arrow,
    SYM_barbar,
    SYM_plus,
    SYM_lt,
    SYM_lteq,
    SYM_gt,
    SYM_gteq,
    SYM_minus,
    SYM_times,
    SYM_div
};
