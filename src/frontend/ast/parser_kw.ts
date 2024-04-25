
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
const KW_elif = "elif";
const KW_else = "else";
const KW_env = "env";
const KW_err = "err";
const KW_false = "false";
const KW_fn = "fn";
const KW_if = "if";
const KW_implements = "implements";
const KW_let = "let";
const KW_literal = "literal";
const KW_match = "match";
const KW_none = "none";
const KW_nothing = "nothing";
const KW_ok = "ok";
const KW_pred = "pred";
const KW_ref = "ref";
const KW_return = "return";
const KW_something = "something";
const KW_some = "some";
const KW_type = "type";
const KW_synth = "defer";
const KW_switch = "switch";
const KW_then = "then";
const KW_true = "true";
const KW_var = "var";
const KW_yield = "yield";
const KW_bsqon = "bsqon";

const KW_debug = "debug";
const KW_release = "release";
const KW_safety = "safety";
const KW_spec = "spec";
const KW_test = "test";

////
//Declaration keywords
const KW_api = "api";
const KW_concept = "concept";
const KW_const = "const";
const KW_enum = "enum";
const KW_entity = "entity";
const KW_ensures = "ensures";
const KW_field = "field";
const KW_function = "function";
const KW_import = "import";
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
const KW_example = "example";
const KW_event = "event";
const KW_status = "status";
const KW_validator = "validator";

//reserved
const KW_operator = "operator";

const KeywordStrings = [
    KW_recursive_q,
    KW_recursive,
    
    KW_action,
    KW__debug,
    KW_abort,
    KW_assert,
    KW_callwith,
    KW_concept,
    KW_const,
    KW_debug,
    KW_control,
    KW_effect,
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
    KW_import,
    KW_in,
    KW_invariant,
    KW_let,
    KW_match,
    KW_method,
    KW_namespace,
    KW_none,
    KW_nothing,
    KW_of,
    KW_ok,
    KW_operator,
    KW_pred,
    KW_provides,
    KW_ref,
    KW_release,
    KW_resultwith,
    KW_return,
    KW_result,
    KW_requires,
    KW_something,
    KW_some,
    KW_safety,
    KW_spec,
    KW_synth,
    KW_switch,
    KW_task,
    KW_test,
    KW_then,
    KW_true,
    KW_typedef,
    KW_typedecl,
    KW_datatype,
    KW_using,
    KW_validate,
    KW_var,
    KW_when,

    KW_bsqon,
    KW_example
].sort((a, b) => { return (a.length !== b.length) ? (b.length - a.length) : ((a !== b) ? (a < b ? -1 : 1) : 0); });

const NS_KW = [
    KW_import,
    KW_namespace,
    KW_typedef, KW_typedecl,
    KW_function, KW_const, 
    KW_concept, KW_entity, KW_enum, KW_datatype, KW_task
];

////////////////////////////////////////////////////////////////////////////////
//Attributes

const GeneralAttributes = [ 
    "export",
    "private",
    "internal",
    "hidden"
];

const TypeDeclAttributes = [
    "status",
    "event",

    "__internal",
    "__typedeclable",
    "__constructable",
    "__primitive",
    "__numeric",
    "__typebase",
    "__universal"
];

const APIDeclAttributes = [
    "deterministic",
    "idempotent",
];

const CheckerAttributes = [
    "softcheck",
    "chktest",
    "errtest",

    "debug",
    "release",
    "safety",
    "spec",
    "test"
]

const InvokeAttributes = [
    "abstract",
    "override",
    "virtual",
    
    "__inline",
    "__safe",
    "__assume_safe",
    "__conditional_safe"
];

const SensitiveAttribute = "sensitive";

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

const SYM_at = "@";
const SYM_atat = "@@";
const SYM_hash = "#";
const SYM_percent = "%";
const SYM_amp = "&";
const SYM_ampamp = "&&";
const SYM_bang = "!";
const SYM_bangeq = "!=";
const SYM_bangeqeq = "!==";
const SYM_colon = ":";
const SYM_coloncolon = "::";
const SYM_coma = ",";
const SYM_dot = ".";
const SYM_eq = "=";
const SYM_eqeq = "==";
const SYM_eqeqeq = "===";
const SYM_bigarrow = "=>";
const SYM_implies = "==>";
const SYM_arrow = "->";
const SYM_semicolon = ";";
const SYM_bar = "|";
const SYM_barbar = "||";
const SYM_plus = "+";
const SYM_question = "?";
const SYM_questionquestion = "??";
const SYM_le = "<";
const SYM_leq = "<=";
const SYM_ge = ">";
const SYM_geq = ">=";
const SYM_minus = "-";
const SYM_times = "*";
const SYM_div = "/";
const SYM_land = "/\\";
const SYM_lor = "\\/";

const SymbolStrings = [
    SYM_lbrack,
    SYM_lparen,
    SYM_lbrace,
    SYM_lbracebar,
    SYM_rbrack,
    SYM_rparen,
    SYM_rbrace,
    SYM_rbracebar,

    SYM_at,
    SYM_atat,
    SYM_hash,
    SYM_percent,
    SYM_amp,
    SYM_bang,
    SYM_ampamp,
    SYM_bangeq,
    SYM_bangeqeq,
    SYM_colon,
    SYM_coloncolon,
    SYM_coma,
    SYM_dot,
    SYM_eq,
    SYM_eqeq,
    SYM_eqeqeq,
    SYM_bigarrow,
    SYM_implies,
    SYM_arrow,
    SYM_semicolon,
    SYM_bar,
    SYM_barbar,
    SYM_plus,
    SYM_question,
    SYM_questionquestion,
    SYM_le,
    SYM_leq,
    SYM_ge,
    SYM_geq,
    SYM_minus,
    SYM_times,
    SYM_div,
    SYM_land,
    SYM_lor
].sort((a, b) => { return (a.length !== b.length) ? (b.length - a.length) : ((a !== b) ? (a < b ? -1 : 1) : 0); });

const RegexFollows = new Set<string>([
    KW__debug,
    KW_ensures,
    KW_invariant,
    KW_return,
    KW_requires,
    KW_validate,
    SYM_lbrack,
    SYM_lparen,
    SYM_lbrace,
    SYM_ampamp,
    SYM_bang,
    SYM_bangeq,
    SYM_bangeqeq,
    SYM_coma,
    SYM_eq,
    SYM_eqeq,
    SYM_eqeqeq,
    SYM_bigarrow,
    SYM_implies,
    SYM_barbar,
    SYM_plus,
    SYM_le,
    SYM_leq,
    SYM_ge,
    SYM_geq,
    SYM_minus,
    SYM_times,
    SYM_div
]);

const LeftScanParens = [SYM_lbrack, SYM_lparen, SYM_lbrace, SYM_lbracebar];
const RightScanParens = [SYM_rbrack, SYM_rparen, SYM_rbrace, SYM_rbracebar];

export {
};
