//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";

import { ParserEnvironment, FunctionScope } from "./parser_env";
import { AndTypeSignature, AutoTypeSignature, EphemeralListTypeSignature, FunctionTypeSignature, LiteralTypeSignature, NominalTypeSignature, ParseErrorTypeSignature, ProjectTypeSignature, RecordTypeSignature, TemplateTypeSignature, TupleTypeSignature, TypeSignature, UnionTypeSignature } from "./type_signature";
import { AbortStatement, AccessEnvValue, AccessFormatInfo, AccessNamespaceConstantExpression, AccessStaticFieldExpression, AccessVariableExpression, AssertStatement, BinAddExpression, BinDivExpression, BinKeyEqExpression, BinKeyNeqExpression, BinLogicAndxpression, BinLogicImpliesExpression, BinLogicOrExpression, BinMultExpression, BinSubExpression, BodyImplementation, CallNamespaceFunctionOrOperatorExpression, CallStaticFunctionExpression, ConstantExpressionValue, ConstructorEphemeralValueList, ConstructorPCodeExpression, ConstructorPrimaryExpression, ConstructorRecordExpression, ConstructorTupleExpression, DebugStatement, EmptyStatement, Expression, IfExpression, InvalidExpression, InvalidStatement, LiteralASCIIStringExpression, LiteralASCIITemplateStringExpression, LiteralBoolExpression, LiteralExpressionValue, LiteralFloatPointExpression, LiteralIntegralExpression, LiteralNoneExpression, LiteralNothingExpression, LiteralRationalExpression, LiteralRegexExpression, LiteralStringExpression, LiteralTemplateStringExpression, LiteralTypedPrimitiveConstructorExpression, LiteralTypedStringExpression, LiteralTypeValueExpression, LogicActionAndExpression, LogicActionOrExpression, MapEntryConstructorExpression, MatchExpression, MultiReturnWithDeclarationStatement, NumericEqExpression, NumericGreaterEqExpression, NumericGreaterExpression, NumericLessEqExpression, NumericLessExpression, NumericNeqExpression, PCodeInvokeExpression, PostfixAccessFromIndex, PostfixAccessFromName, PostfixAs, PostfixGetIndexOption, PostfixGetIndexOrNone, PostfixGetPropertyOption, PostfixGetPropertyOrNone, PostfixHasIndex, PostfixHasProperty, PostfixInvoke, PostfixIs, PostfixOp, PostfixOperation, PrefixNegateOp, PrefixNotOp, RecursiveAnnotation, ReturnStatement, SpecialConstructorExpression, Statement, SwitchExpression, TaskCancelRequestedExpression, TaskGetIDExpression, TaskSelfFieldExpression, VariableAssignmentStatement, VariableAssignmentStructuredAssignment, VariableDeclarationStatement, VariableDeclarationStructuredAssignment, VariablePackAssignmentStatement, VariablePackDeclarationStatement } from "./body";
import { Assembly, BuildLevel, FunctionParameter, InvokeDecl, PostConditionDecl, PreConditionDecl, TemplateTermDecl, TypeConditionRestriction } from "./assembly";
import { BSQRegex } from "./bsqregex";

const KW_recursive_q = "recursive?";
const KW_recursive = "recursive";

const KW__debug = "_debug";
const KW_abort = "abort";
const KW_assert = "assert";
const KW_concept = "concept";
const KW_const = "const";
const KW_debug = "debug";
const KW_elif = "elif";
const KW_else = "else";
const KW_enum = "enum";
const KW_env = "environment";
const KW_entity = "entity";
const KW_ensures = "ensures";
const KW_err = "err";
const KW_false = "false";
const KW_field = "field";
const KW_fn = "fn";
const KW_function = "function";
const KW_if = "if";
const KW_import = "import";
const KW_invariant = "invariant";
const KW_let = "let";
const KW_match = "match";
const KW_method = "method";
const KW_namespace = "namespace";
const KW_none = "none";
const KW_nothing = "nothing";
const KW_of = "of";
const KW_ok = "ok";
const KW_operator = "operator";
const KW_pred = "pred";
const KW_provides = "provides";
const KW_ref = "ref";
const KW_release = "release";
const KW_return = "return";
const KW_requires = "requires";
const KW_self = "self";
const KW_something = "something";
const KW_switch = "switch";
const KW_test = "test";
const KW_then = "then";
const KW_true = "true";
const KW_type = "type";
const KW_typedef = "typedef";
const KW_typedecl = "typedecl";
const KW_datatype = "datatype";
const KW_using = "using";
const KW_validate = "validate";
const KW_var = "var";
const KW_when = "when";

const KeywordStrings = [
    KW_recursive_q,
    KW_recursive,
    xxxx
].sort((a, b) => { return (a.length !== b.length) ? (b.length - a.length) : a.localeCompare(b); });

const SYM_lbrack = "[";
const SYM_lparen = "(";
const SYM_lbrace = "{";
const SYM_rbrack = "]";
const SYM_rparen = ")";
const SYM_rbrace = "}";

const SYM_percent = "%";
const SYM_hash = "%";
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
    SYM_rbrack,
    SYM_rparen,
    SYM_rbrace,

    SYM_percent,
    SYM_hash,
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
    SYM_le,
    SYM_leq,
    SYM_ge,
    SYM_geq,
    SYM_minus,
    SYM_times,
    SYM_div,
    SYM_land,
    SYM_lor
].sort((a, b) => { return (a.length !== b.length) ? (b.length - a.length) : a.localeCompare(b); });

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

const LeftScanParens = [SYM_lbrack, SYM_lparen, SYM_lbrace];
const RightScanParens = [SYM_rbrack, SYM_rparen, SYM_rbrace];

const AttributeStrings = [
    "abstract",
    "chktest",
    "debug",
    "errtest",
    "exposed",
    "internal",
    "override",
    "recursive?",
    "recursive",
    "sensitive",
    "private",
    "public",
    "release",
    "test",
    "virtual",
    
    "__chktest",

    "__internal",
    "__typedeclable",
    "__enumable", 
    "__litvaluetype",
    "__constructable",
    "__primitive",
    "__typebase",
    "__safe",
    "__assume_safe",
    "__conditional_safe",
    "__universal"
];

const UnsafeFieldNames = ["is", "as", "isNone", "isSome", "asOrNone", "asOptional", "asResult", "hasProperty", "getPropertyOrNone", "getPropertyOption"]

const TokenStrings = {
    Clear: "[CLEAR]",
    Error: "[ERROR]",

    Numberino: "[LITERAL_NUMBERINO]",
    Int: "[LITERAL_INT]",
    Nat: "[LITERAL_NAT]",
    Float: "[LITERAL_FLOAT]",
    Decimal: "[LITERAL_DECIMAL]",
    BigInt: "[LITERAL_BIGINT]",
    BigNat: "[LITERAL_BIGNAT]",
    Rational: "[LITERAL_RATIONAL]",
    Regex: "[LITERAL_REGEX]",
    
    String: "[LITERAL_STRING]",
    ASCIIString: "[LITERAL_ASCII_STRING]",
    TypedString: "[LITERAL_TYPED_STRING]",

    TemplateString: "[LITERAL_TEMPLATE_STRING]",
    TemplateASCIIString: "[LITERAL_TEMPLATE_ASCII_STRING]",

    //Names
    Namespace: "[NAMESPACE]",
    Type: "[TYPE]",
    ScopeName: "[SCOPE]",
    Template: "[TEMPLATE]",
    Identifier: "[IDENTIFIER]",
    FollowTypeSep: "[FOLLOWTYPE]",

    EndOfStream: "[EOS]"
};

class Token {
    readonly line: number;
    readonly column: number;
    readonly pos: number;
    readonly span: number;

    readonly kind: string;
    readonly data: string | undefined;

    constructor(line: number, column: number, cpos: number, span: number, kind: string, data?: string) {
        this.line = line;
        this.column = column;
        this.pos = cpos;
        this.span = span;

        this.kind = kind;
        this.data = data;
    }
}

class SourceInfo {
    readonly line: number;
    readonly column: number;
    readonly pos: number;
    readonly span: number;

    constructor(line: number, column: number, cpos: number, span: number) {
        this.line = line;
        this.column = column;
        this.pos = cpos;
        this.span = span;
    }
}

type CodeFileInfo = { 
    srcpath: string, 
    filename: string, 
    contents: string
};

function unescapeLiteralString(str: string): string {
    assert(false, "unescapeLiteralString -- implementation");
    return str;
}

class Lexer {
    private static findKeywordString(str: string): string | undefined {
        let imin = 0;
        let imax = KeywordStrings.length;

        while (imin < imax) {
            const imid = Math.floor((imin + imax) / 2);

            const scmpval = (str.length !== KeywordStrings[imid].length) ? (KeywordStrings[imid].length - str.length) : str.localeCompare(KeywordStrings[imid]);
            if (scmpval === 0) {
                return KeywordStrings[imid];
            }
            else if (scmpval < 0) {
                imax = imid;
            }
            else {
                imin = imid + 1;
            }
        }
        return undefined;
    }

    private m_macrodefs: string[];
    private m_namespaceScopes: Set<String> | undefined;

    private m_input: string;
    private m_internTable: Map<string, string>;
    private m_cline: number;
    private m_linestart: number;
    private m_cpos: number;
    private m_tokens: Token[];

    constructor(input: string, macrodefs: string[], namespaceScopes: Set<String> | undefined) {
        this.m_macrodefs = macrodefs;
        this.m_namespaceScopes = namespaceScopes;

        this.m_input = input;
        this.m_internTable = new Map<string, string>();
        this.m_cline = 1;
        this.m_linestart = 0;
        this.m_cpos = 0;
        this.m_tokens = [];
    }

    ////
    //Helpers
    private isInScopeNameMode(): boolean {
        return this.m_namespaceScopes === undefined;
    }

    private static readonly _s_scopenameRe = /(([A-Z][_a-zA-Z0-9]+)::)*([A-Z][_a-zA-Z0-9]+)/y;
    private static readonly _s_typenameRe = /[A-Z][_a-zA-Z0-9]+/y;
    private static readonly _s_istypenameRe = /^[A-Z][_a-zA-Z0-9]+$/y;
    private tryExtractScopeName(): string | undefined {
        if(this.m_namespaceScopes !== undefined) {
            return undefined;
        }

        Lexer._s_scopenameRe.lastIndex = this.m_cpos;
        const m = Lexer._s_scopenameRe.exec(this.m_input);
        if(m === null) {
            return undefined;
        }
        else {
            return m[0];
        }
    }

    private tryExtractNamespaceName(): string | undefined {
        if(this.m_namespaceScopes === undefined) {
            return undefined;
        }

        Lexer._s_scopenameRe.lastIndex = this.m_cpos;
        const m = Lexer._s_scopenameRe.exec(this.m_input);
        if(m === null) {
            return undefined;
        }
        else {
            const fullscope = m[0];
            if(this.m_namespaceScopes.has(fullscope)) {
                return fullscope;
            }
            else {
                let ttrim = fullscope.lastIndexOf(SYM_coloncolon);
                let pscope = fullscope;
                while(ttrim !== -1) {
                    pscope = pscope.substring(0, ttrim);

                    if(this.m_namespaceScopes.has(pscope)) {
                        return pscope;
                    }
                   
                    ttrim = pscope.lastIndexOf(SYM_coloncolon);
                }
                return undefined;
            }
        }
    }

    private tryExtractTypenameName(): string | undefined {
        if(this.m_namespaceScopes === undefined) {
            return undefined;
        }

        Lexer._s_typenameRe.lastIndex = this.m_cpos;
        const m = Lexer._s_typenameRe.exec(this.m_input);
        if(m === null) {
            return undefined;
        }
        else {
            return m[0];
        }
    }

    public isDeclTypeName(str: string): boolean {
        Lexer._s_istypenameRe.lastIndex = 0;
        return Lexer._s_istypenameRe.test(str);
    }

    private isTemplateName(str: string): boolean {
        return str.length === 1 && /^[A-Z]$/.test(str);
    }

    //TODO: we need to make sure that someone doesn't name a local variable "_"
    private isIdentifierName(str: string): boolean {
        return /^([$]?([_a-z]|([_a-z][_a-zA-Z0-9]+)))$/.test(str);
    }

    private recordLexToken(epos: number, kind: string) {
        this.m_tokens.push(new Token(this.m_cline, this.m_cpos - this.m_linestart, this.m_cpos, epos - this.m_cpos, kind, kind)); //set data to kind string
        this.m_cpos = epos;
    }

    private recordLexTokenWData(epos: number, kind: string, data: string) {
        const rdata = this.m_internTable.get(data) || this.m_internTable.set(data, data).get(data);
        this.m_tokens.push(new Token(this.m_cline, this.m_cpos - this.m_linestart, this.m_cpos, epos - this.m_cpos, kind, rdata));
        this.m_cpos = epos;
    }

    private static readonly _s_whitespaceRe = /\s+/y;
    private tryLexWS(): boolean {
        Lexer._s_whitespaceRe.lastIndex = this.m_cpos;
        const m = Lexer._s_whitespaceRe.exec(this.m_input);
        if (m === null) {
            return false;
        }

        for (let i = 0; i < m[0].length; ++i) {
            if (m[0][i] === "\n") {
                this.m_cline++;
                this.m_linestart = this.m_cpos + i + 1;
            }
        }

        this.m_cpos += m[0].length;
        return true;
    }

    private static readonly _s_commentRe = /(\/\/.*)|(\/\*(.|\s)*?\*\/)/uy;
    private tryLexComment(): boolean {
        Lexer._s_commentRe.lastIndex = this.m_cpos;
        const m = Lexer._s_commentRe.exec(this.m_input);
        if (m === null) {
            return false;
        }

        for (let i = 0; i < m[0].length; ++i) {
            if (m[0][i] === "\n") {
                this.m_cline++;
                this.m_linestart = this.m_cpos + i + 1;
            }
        }

        this.m_cpos += m[0].length;
        return true;
    }

    private static readonly _s_intNumberinoRe = /0|[1-9][0-9]*/y;

    private static readonly _s_intRe = /(0|[1-9][0-9]*)i/y;
    private static readonly _s_natRe = /(0|[1-9][0-9]*)n/y;

    private static readonly _s_floatRe = /([0-9]+\.[0-9]+)([eE][-+]?[0-9]+)?f/y;
    private static readonly _s_decimalRe = /([0-9]+\.[0-9]+)([eE][-+]?[0-9]+)?d/y;

    private static readonly _s_bigintRe = /(0|[1-9][0-9]*)I/y;
    private static readonly _s_bignatRe = /(0|[1-9][0-9]*)N/y;
    private static readonly _s_rationalRe = /((0|[1-9][0-9]*)|(0|[1-9][0-9]*)\/([1-9][0-9]*))R/y;

    private tryLexNumber(): boolean {
        Lexer._s_rationalRe.lastIndex = this.m_cpos;
        const mr = Lexer._s_rationalRe.exec(this.m_input);
        if (mr !== null) {
            this.recordLexTokenWData(this.m_cpos + mr[0].length, TokenStrings.Rational, mr[0]);
            return true;
        }

        Lexer._s_bignatRe.lastIndex = this.m_cpos;
        const mbn = Lexer._s_bignatRe.exec(this.m_input);
        if (mbn !== null) {
            this.recordLexTokenWData(this.m_cpos + mbn[0].length, TokenStrings.BigNat, mbn[0]);
            return true;
        }

        Lexer._s_bigintRe.lastIndex = this.m_cpos;
        const mbi = Lexer._s_bigintRe.exec(this.m_input);
        if (mbi !== null) {
            this.recordLexTokenWData(this.m_cpos + mbi[0].length, TokenStrings.BigInt, mbi[0]);
            return true;
        }

        Lexer._s_decimalRe.lastIndex = this.m_cpos;
        const md = Lexer._s_decimalRe.exec(this.m_input);
        if (md !== null) {
            this.recordLexTokenWData(this.m_cpos + md[0].length, TokenStrings.Decimal, md[0]);
            return true;
        }

        Lexer._s_floatRe.lastIndex = this.m_cpos;
        const mf = Lexer._s_floatRe.exec(this.m_input);
        if (mf !== null) {
            this.recordLexTokenWData(this.m_cpos + mf[0].length, TokenStrings.Float, mf[0]);
            return true;
        }

        Lexer._s_natRe.lastIndex = this.m_cpos;
        const mn = Lexer._s_natRe.exec(this.m_input);
        if (mn !== null) {
            this.recordLexTokenWData(this.m_cpos + mn[0].length, TokenStrings.Nat, mn[0]);
            return true;
        }

        Lexer._s_intRe.lastIndex = this.m_cpos;
        const mi = Lexer._s_intRe.exec(this.m_input);
        if (mi !== null) {
            this.recordLexTokenWData(this.m_cpos + mi[0].length, TokenStrings.Int, mi[0]);
            return true;
        }

        Lexer._s_intNumberinoRe.lastIndex = this.m_cpos;
        const inio = Lexer._s_intNumberinoRe.exec(this.m_input);
        if (inio !== null) {
            this.recordLexTokenWData(this.m_cpos + inio[0].length, TokenStrings.Numberino, inio[0]);
            return true;
        }

        return false;
    }

    private static readonly _s_stringRe = /"[^"\\\r\n]*(\\(.|\r?\n)[^"\\\r\n]*)*"/uy;
    private static readonly _s_ascii_stringRe = /ascii{"[^"\\\r\n]*(\\(.|\r?\n)[^"\\\r\n]*)*"}/uy;
    private static readonly _s_typedStringRe = /'[^'\\\r\n]*(\\(.|\r?\n)[^'\\\r\n]*)*'/uy;

    private static readonly _s_template_stringRe = /[$]"[^"\\\r\n]*(\\(.|\r?\n)[^"\\\r\n]*)*"/uy;
    private static readonly _s_ascii_template_stringRe = /ascii{[$]"[^"\\\r\n]*(\\(.|\r?\n)[^"\\\r\n]*)*"}/uy;

    private tryLexString() {
        Lexer._s_template_stringRe.lastIndex = this.m_cpos;
        const template_string_m = Lexer._s_template_stringRe.exec(this.m_input);
        if (template_string_m !== null) {
            this.recordLexTokenWData(this.m_cpos + template_string_m[0].length, TokenStrings.TemplateString, template_string_m[0]);
            return true;
        }

        Lexer._s_ascii_template_stringRe.lastIndex = this.m_cpos;
        const ascii_template_string_m = Lexer._s_ascii_template_stringRe.exec(this.m_input);
        if (ascii_template_string_m !== null) {
            this.recordLexTokenWData(this.m_cpos + ascii_template_string_m[0].length, TokenStrings.TemplateASCIIString, ascii_template_string_m[0]);
            return true;
        }

        Lexer._s_stringRe.lastIndex = this.m_cpos;
        const ms = Lexer._s_stringRe.exec(this.m_input);
        if (ms !== null) {
            this.recordLexTokenWData(this.m_cpos + ms[0].length, TokenStrings.String, ms[0]);
            return true;
        }

        Lexer._s_ascii_stringRe.lastIndex = this.m_cpos;
        const mas = Lexer._s_ascii_stringRe.exec(this.m_input);
        if (mas !== null) {
            this.recordLexTokenWData(this.m_cpos + mas[0].length, TokenStrings.ASCIIString, mas[0]);
            return true;
        }

        Lexer._s_typedStringRe.lastIndex = this.m_cpos;
        const mts = Lexer._s_typedStringRe.exec(this.m_input);
        if (mts !== null) {
            this.recordLexTokenWData(this.m_cpos + mts[0].length, TokenStrings.TypedString, mts[0]);
            return true;
        }

        return false;
    }

    private static readonly _s_regexRe = /\/[^"\\\r\n]*(\\(.)[^"\\\r\n]*)*\//y;
    private tryLexRegex() {
        Lexer._s_regexRe.lastIndex = this.m_cpos;
        const ms = Lexer._s_regexRe.exec(this.m_input);
        if (ms !== null && RegexFollows.has(this.m_tokens[this.m_tokens.length - 1].kind)) {
            this.recordLexTokenWData(this.m_cpos + ms[0].length, TokenStrings.Regex, ms[0]);
            return true;
        }

        return false;
    }

    private static readonly _s_symbolRe = /[\W]+/y;
    private tryLexSymbol() {
        Lexer._s_symbolRe.lastIndex = this.m_cpos;
        const ms = Lexer._s_symbolRe.exec(this.m_input);
        if (ms !== null) {
            const sym = SymbolStrings.find((value) => ms[0].startsWith(value));
            if (sym !== undefined) {
                this.recordLexToken(this.m_cpos + sym.length, sym);
                return true;
            }
        }

        return false;
    }

    private static readonly _s_nameRe = /(recursive\?)|([$]?\w+)/y;
    private tryLexName(): boolean {
        Lexer._s_nameRe.lastIndex = this.m_cpos;
        const m = Lexer._s_nameRe.exec(this.m_input);

        const kwmatch = (m !== null) ? Lexer.findKeywordString(m[0]) : undefined;
        if (kwmatch !== undefined && m !== null) {
            this.recordLexToken(this.m_cpos + m[0].length, kwmatch);
            return true;
        }
        else if (m !== null && this.isIdentifierName(m[0])) {
            const name = m[0];
            const isTypeThing = /^_[A-Z]/.test(name);
            if (isTypeThing) {
                this.recordLexToken(this.m_cpos + 1, TokenStrings.FollowTypeSep);
            }
            else {
                this.recordLexTokenWData(this.m_cpos + name.length, TokenStrings.Identifier, name);
            }
            return true;
        }
        else if (m !== null && this.isTemplateName(m[0])) {
            const name = m[0];
            this.recordLexTokenWData(this.m_cpos + name.length, TokenStrings.Template, name);
            return true;
        }
        else {
            if(this.isInScopeNameMode()) {
                const scopeopt = this.tryExtractScopeName();
                if(scopeopt !== undefined) {
                    this.recordLexTokenWData(this.m_cpos + scopeopt.length, TokenStrings.ScopeName, scopeopt);
                    return true;
                }
                else {
                    this.recordLexToken(this.m_cpos + 1, TokenStrings.Error);
                    return false;
                }
            }
            else {
                const nsopt = this.tryExtractNamespaceName();
                if(nsopt !== undefined) {
                    this.recordLexTokenWData(this.m_cpos + nsopt.length, TokenStrings.Namespace, nsopt);
                    return true;
                }
                else {
                    const topt = this.tryExtractTypenameName();
                    if(topt !== undefined) {
                        this.recordLexTokenWData(this.m_cpos + topt.length, TokenStrings.Type, topt);
                        return true;
                    }
                    else {
                        this.recordLexToken(this.m_cpos + 1, TokenStrings.Error);
                        return false;
                    }
                }
            }
        }
    }

    static isAttributeKW(str: string) {
        return AttributeStrings.indexOf(str) !== -1;
    }

    private static readonly _s_macroRe = /(#if[ ]+([A-Z][_A-Z0-9]*)|#else|#endif)/y;
    tryLexMacroOp(): [string, string | undefined] | undefined {
        Lexer._s_macroRe.lastIndex = this.m_cpos;
        const m = Lexer._s_macroRe.exec(this.m_input);
        if (m === null) {
            return undefined;
        }

        const name = m[0].trim();
        this.m_cpos += m[0].length;

        if(name.slice(0, "#if".length) === "#if") {
            return ["#if", name.slice("#if".length).trim()];
        }
        else {
            return [name, undefined]
        }
    }

    lex(): Token[] {
        if (this.m_tokens.length !== 0) {
            return this.m_tokens;
        }

        let mode: "scan" | "normal" = "normal";
        let macrostack: ("scan" | "normal")[] = []

        this.m_tokens = [];
        while (this.m_cpos < this.m_input.length) {
            if(mode === "scan") {
                const macro = this.tryLexMacroOp();
                if (macro !== undefined) {
                    if (macro[0] === "#if") {
                        macrostack.push("scan")
                    }
                    else if (macro[0] === "#else") {
                        mode = macrostack[macrostack.length - 1];
                    }
                    else {
                        mode = macrostack.pop() as "scan" | "normal";
                    }
                }
                else {
                    const nexthash = this.m_input.indexOf("#", this.m_cpos + 1);
                    if(nexthash === -1) {
                        //ended in dangling macro
                        this.recordLexToken(this.m_input.length, TokenStrings.Error);
                        this.m_cpos = this.m_input.length;
                    }
                    else {
                        const skips = this.m_input.slice(this.m_cpos, nexthash);

                        for (let i = 0; i < skips.length; ++i) {
                            if (skips[i] === "\n") {
                                this.m_cline++;
                                this.m_linestart = this.m_cpos + i + 1;
                            }
                        }

                        this.m_cpos = nexthash;
                    }
                }
            }
            else {
                const macro = this.tryLexMacroOp();
                if(macro !== undefined) {
                    if(macro[0] === "#if") {
                        macrostack.push("normal")
                        if(this.m_macrodefs.includes(macro[1] as string)) {
                            mode = "normal";
                        }
                        else {
                            mode = "scan";
                        }
                    }
                    else if(macro[0] === "#else") {
                        mode = "scan";
                    }
                    else {
                        mode = macrostack.pop() as "scan" | "normal";
                    }
                }
                else {
                    if (this.tryLexWS() || this.tryLexComment()) {
                        //continue
                    }
                    else if (this.tryLexNumber() || this.tryLexString() || this.tryLexRegex() || this.tryLexSymbol() || this.tryLexName()) {
                        //continue
                    }
                    else {
                        this.recordLexToken(this.m_cpos + 1, TokenStrings.Error);
                    }
                }
            }
        }

        this.recordLexToken(this.m_input.length, TokenStrings.EndOfStream);
        return this.m_tokens;
    }
}

class ParseError extends Error {
    constructor(line: number, message?: string) {
        super(`Parse failure on line ${line} -- ${message}`);
        Object.setPrototypeOf(this, new.target.prototype);
    }
}

enum InvokableKind {
    Basic,
    Member,
    PCodeFn,
    PCodePred,
    DynamicOperator
}

class Parser {
    private m_tokens: Token[];
    private m_cpos: number;
    private m_epos: number;

    private m_penv: ParserEnvironment;

    private m_errors: [string, number, string][];
    private m_recoverStack: number[];

    readonly sortedSrcFiles: {fullname: string, shortname: string}[]; 

    constructor(assembly: Assembly, srcFileNames: {fullname: string, shortname: string}[]) {
        this.m_tokens = [];
        this.m_cpos = 0;
        this.m_epos = 0;

        this.m_penv = new ParserEnvironment(assembly);

        this.m_errors = [];
        this.m_recoverStack = [];

        this.sortedSrcFiles = srcFileNames.sort((a, b) => a.fullname.localeCompare(b.fullname));
    }

    private initialize(toks: Token[]) {
        this.m_tokens = toks;
        this.m_cpos = 0;
        this.m_epos = toks.length;
    }

    ////
    //Helpers

    private generateBodyID(sinfo: SourceInfo, srcFile: string, etag?: string): string {
        //Keep consistent with version in type checker!!!
        const sfpos = this.sortedSrcFiles.findIndex((entry) => entry.fullname === srcFile);

        return `${this.sortedSrcFiles[sfpos].shortname}#k${sfpos}${etag !== undefined ? ("_" + etag) : ""}::${sinfo.line}@${sinfo.pos}`;
    }

    private static attributeSetContains(attr: string, attribs: string[]): boolean {
        return attribs.indexOf(attr) !== -1;
    }

    private getCurrentLine(): number {
        return this.m_tokens[this.m_cpos].line;
    }

    private getCurrentSrcInfo(): SourceInfo {
        const tk = this.m_tokens[this.m_cpos];
        return new SourceInfo(tk.line, 0, tk.pos, tk.span);
    }

    private setRecover(pos: number) {
        this.m_recoverStack.push(pos);
    }

    private clearRecover(pos?: number) {
        this.m_recoverStack.pop();
    }

    private processRecover() {
        this.m_cpos = this.m_recoverStack.pop() as number;
    }

    private raiseError(line: number, msg: string) {
        this.m_errors.push([this.m_penv.getCurrentFile(), line, msg]);
        throw new ParseError(line, msg);
    }

    private scanMatchingParens(lp: string, rp: string, sindex?: number): number {
        let pscount = 1;
        for (let pos = this.m_cpos + (sindex || 0) + 1; pos < this.m_epos; ++pos) {
            const tok = this.m_tokens[pos];
            if (tok.kind === lp) {
                pscount++;
            }
            else if (tok.kind === rp) {
                pscount--;
            }
            else {
                //nop
            }

            if (pscount === 0) {
                return pos + 1;
            }
        }

        return this.m_epos;
    }

    private scanCodeParens(): number {
        let pscount = 1;
        for (let pos = this.m_cpos + 1; pos < this.m_epos; ++pos) {
            const tok = this.m_tokens[pos];
            if (LeftScanParens.indexOf(tok.kind) !== -1) {
                pscount++;
            }
            else if (RightScanParens.indexOf(tok.kind) !== -1) {
                pscount--;
            }
            else {
                //nop
            }

            if (pscount === 0) {
                return pos + 1;
            }
        }

        return this.m_epos;
    }

    private scanLParens(cpos: number): number {
        let pscount = 1;
        for (let pos = cpos + 1; pos < this.m_epos; ++pos) {
            const tok = this.m_tokens[pos];
            if (tok.kind === SYM_lparen) {
                pscount++;
            }
            else if (tok.kind === SYM_rparen) {
                pscount--;
            }
            else {
                //nop
            }

            if (pscount === 0) {
                return pos + 1;
            }
        }

        return this.m_epos;
    }

    private setNamespaceAndFile(ns: string, file: string) {
        this.m_penv.setNamespaceAndFile(ns, file);
    }

    private peekToken(pos?: number): string {
        return this.m_tokens[this.m_cpos + (pos || 0)].kind;
    }

    private peekTokenData(pos?: number): string {
        return this.m_tokens[this.m_cpos + (pos || 0)].data as string;
    }

    private testToken(kind: string): boolean {
        return (this.m_cpos !== this.m_epos) && this.m_tokens[this.m_cpos].kind === kind;
    }

    private testFollows(...kinds: string[]): boolean {
        for (let i = 0; i < kinds.length; ++i) {
            if (this.m_cpos + i === this.m_epos || this.m_tokens[this.m_cpos + i].kind !== kinds[i]) {
                return false;
            }
        }

        return true;
    }

    private consumeToken() {
        this.m_cpos++;
    }

    private consumeTokenIf(kind: string) {
        if (this.testToken(kind)) {
            this.consumeToken();
        }
    }

    private testAndConsumeTokenIf(kind: string): boolean {
        const test = this.testToken(kind);
        if (test) {
            this.consumeToken();
        }
        return test;
    }

    private consumeTokenAndGetValue(): string {
        const td = this.m_tokens[this.m_cpos].data;
        this.consumeToken();
        return td as string;
    }

    private ensureToken(kind: string, contextinfo: string) {
        if (!this.testToken(kind)) {
            const found = this.m_tokens[this.m_cpos].data || this.m_tokens[this.m_cpos].kind;
            this.raiseError(this.m_tokens[this.m_cpos].line, `Expected "${kind}" but found "${found}" when trying to parse: ${contextinfo}`);
        }
    }

    private ensureAndConsumeToken(kind: string, contextinfo: string) {
        this.ensureToken(kind, contextinfo);
        this.consumeToken();
    }

    private ensureNotToken(kind: string, contextinfo: string) {
        if (this.testToken(kind)) {
            this.raiseError(this.m_tokens[this.m_cpos].line, `Token "${kind}" was not expected when trying to parse: ${contextinfo}`);
        }
    }

    private scanToken(tok: string): number {
        let pos = this.m_cpos;

        while (pos !== this.m_epos) {
            if (this.m_tokens[pos].kind === tok) {
                return pos;
            }
            pos++;
        }
        return this.m_epos;
    }

    private scanTokenOptions(...toks: string[]): number {
        let pos = this.m_cpos;

        while (pos !== this.m_epos) {
            if (toks.indexOf(this.m_tokens[pos].kind) !== -1) {
                return pos;
            }
            pos++;
        }
        return this.m_epos;
    }

    private parseListOf<T>(contextinfobase: string, start: string, end: string, sep: string, fn: () => T): T[] {
        let result: T[] = [];

        this.ensureAndConsumeToken(start, contextinfobase);
        while (!this.testAndConsumeTokenIf(end)) {
            result.push(fn());
            
            if (this.testAndConsumeTokenIf(sep)) {
                this.ensureNotToken(end, `element in ${contextinfobase} list`);
            }
            else {
                this.ensureToken(end, `element in ${contextinfobase} list`);
            }
        }

        return result;
    }

    private parseEphemeralListOf<T>(fn: () => T): T[] {
        let result: T[] = [];

        while (true) {
            result.push(fn());

            if(!this.testAndConsumeTokenIf(SYM_coma)) {
                break;
            }
        }

        return result;
    }

    parseBuildInfo(cb: BuildLevel): BuildLevel {
        if( this.testToken(KW_debug) || this.testToken(KW_test) || this.testToken(KW_release)) {
            return this.consumeTokenAndGetValue() as "debug" | "test" | "release";
        }
        else {
            return cb;
        }
    }

    ////
    //Misc parsing

    private parseInvokableCommon(ikind: InvokableKind, noBody: boolean, attributes: string[], isrecursive: "yes" | "no" | "cond", terms: TemplateTermDecl[], implicitTemplates: string[], termRestrictions: TypeConditionRestriction | undefined, optSelfRef: boolean, optSelfType: TypeSignature | undefined): InvokeDecl {
        const sinfo = this.getCurrentSrcInfo();
        const srcFile = this.m_penv.getCurrentFile();
        const line = this.getCurrentLine();

        const bodyid = this.generateBodyID(sinfo, srcFile);

        let fparams: FunctionParameter[] = [];
        if (ikind === InvokableKind.Member) {
            fparams.push(new FunctionParameter("this", optSelfType as TypeSignature, undefined));
        }

        let resultInfo = this.m_penv.SpecialAutoSignature;

        const params = this.parseListOf<FunctionParameter>("function declaration", SYM_lparen, SYM_rparen, SYM_coma, () => {
            this.ensureToken(TokenStrings.Identifier, "function parameter");
            const pname = this.consumeTokenAndGetValue();

            let argtype = this.m_penv.SpecialAutoSignature;
            if (this.testAndConsumeTokenIf(SYM_colon)) {
                argtype = this.parseTypeSignature();
            }
            else {
                if (ikind !== InvokableKind.PCodeFn && ikind !== InvokableKind.PCodePred) {
                    this.raiseError(line, "Missing type specifier -- auto typing is only supported for lambda parameter declarations");
                }
            }

            let litexp: LiteralExpressionValue | undefined = undefined;
            if(this.testAndConsumeTokenIf(SYM_eqeq)) {
                if(ikind !== InvokableKind.DynamicOperator) {
                    this.raiseError(line, "Literal match parameters are only allowed on dynamic operator definitions");
                }

                litexp = this.parseLiteralExpression(undefined);
            }

            return new FunctionParameter(pname, argtype, litexp);
        });

        const allTypedParams = params.every((param) => !(param.type instanceof AutoTypeSignature));
        if (this.testAndConsumeTokenIf(SYM_colon)) {
            resultInfo = this.parseResultType(false);
        }
        else {
            if (ikind === InvokableKind.PCodePred && allTypedParams) {
                resultInfo = new NominalTypeSignature("Core", ["Bool"]);
            }

            if (ikind !== InvokableKind.PCodeFn && ikind !== InvokableKind.PCodePred) {
                if(!optSelfRef !== true) {
                    this.raiseError(line, "Cannot have void return unless one of the reciver is by ref");
                }
                resultInfo = this.m_penv.SpecialNoneSignature; //void conversion
            }
        }

        const argNames = new Set<string>(...fparams.map((param) => param.name));
        let preconds: PreConditionDecl[] = [];
        let postconds: PostConditionDecl[] = [];
        let body: BodyImplementation | undefined = undefined;
        let capturedvars = new Set<string>();
        let capturedtemplates = new Set<string>();
        if (noBody) {
            this.ensureAndConsumeToken(SYM_semicolon, "an abstract function declaration");
        }
        else {
            if (ikind === InvokableKind.PCodeFn || ikind === InvokableKind.PCodePred) {
                this.ensureAndConsumeToken(SYM_bigarrow, "a lambda declaration");
            }
            else {
                [preconds, postconds] = this.parsePreAndPostConditions(sinfo, argNames, resultInfo);
            }

            try {
                const boundtemplates = new Set<string>(...terms.map((tt) => tt.name), ...implicitTemplates);
                this.m_penv.pushFunctionScope(new FunctionScope(argNames, boundtemplates, resultInfo, ikind === InvokableKind.PCodeFn || ikind === InvokableKind.PCodePred));
                body = this.parseBody(bodyid, srcFile);
                capturedvars = this.m_penv.getCurrentFunctionScope().getCaptureVars();
                capturedtemplates = this.m_penv.getCurrentFunctionScope().getCaptureTemplates();
                this.m_penv.popFunctionScope();
            }
            catch (ex) {
                this.m_penv.popFunctionScope();
                throw ex;
            }
        }

        if (ikind === InvokableKind.PCodeFn || ikind === InvokableKind.PCodePred) {
            const bbody = body as BodyImplementation;
            return InvokeDecl.createPCodeInvokeDecl(this.m_penv.getCurrentNamespace(), sinfo, this.getCurrentSrcInfo(), bodyid, srcFile, attributes, isrecursive, fparams, resultInfo, capturedvars, capturedtemplates, bbody, ikind === InvokableKind.PCodeFn, ikind === InvokableKind.PCodePred);
        }
        else {
            if(body !== undefined) {
                return InvokeDecl.createStandardInvokeDecl(this.m_penv.getCurrentNamespace(), sinfo, this.getCurrentSrcInfo(), bodyid, srcFile, attributes, isrecursive, terms, termRestrictions, fparams, optSelfRef, resultInfo, preconds, postconds, body);
            }
            else {
                return InvokeDecl.createStandardInvokeDecl(this.m_penv.getCurrentNamespace(), sinfo, this.getCurrentSrcInfo(), bodyid, srcFile, attributes, isrecursive, terms, termRestrictions, fparams, optSelfRef, resultInfo, preconds, postconds, undefined);
            }
        }
    }

    ////
    //Type parsing

    private parseResultType(ispcode: boolean): TypeSignature {
        if(ispcode) {
            return this.parseTypeSignature();
        }
        else {
            const decls = this.parseEphemeralListOf(() => {
                const tdecl = this.parseTypeSignature();
                return tdecl;
            });
    
            return decls.length === 1 ? decls[0] : new EphemeralListTypeSignature(decls);
        }
    } 

    private parseTypeSignature(): TypeSignature {
        return this.parseOrCombinatorType();
    }

    private parseOrCombinatorType(): TypeSignature {
        const ltype = this.parsePostfixTypeReference();
        if (!this.testToken(SYM_bar)) {
            return ltype;
        }
        else {
            this.consumeToken();
            return Parser.orOfTypeSignatures(ltype, this.parseOrCombinatorType());
        }
    }

    private parsePostfixTypeReference(): TypeSignature {
        let roottype = this.parseCombineCombinatorType();
        while (this.testAndConsumeTokenIf(SYM_question)) {
            roottype = this.parseNoneableType(roottype);
        }
        return roottype;
    }

    private parseNoneableType(basetype: TypeSignature): TypeSignature {
        return Parser.orOfTypeSignatures(basetype, this.m_penv.SpecialNoneSignature);
    }

    private parseCombineCombinatorType(): TypeSignature {
        const ltype = this.parseProjectType();
        if (!this.testToken(SYM_amp)) {
            return ltype;
        }
        else {
            this.consumeToken();
            return this.andOfTypeSignatures(ltype, this.parseCombineCombinatorType());
        }
    }

    private parseProjectType(): TypeSignature {
        const ltype = this.parseBaseTypeReference();
        if (!this.testToken(SYM_bang)) {
            return ltype;
        }
        else {
            this.consumeToken();
            const ptype = this.parseNominalType();
            
            return new ProjectTypeSignature(ltype, ptype);
        }
    }

    private parseBaseTypeReference(): TypeSignature {
        switch (this.peekToken()) {
            case TokenStrings.Template: {
                return this.parseTemplateTypeReference();
            }
            case TokenStrings.Namespace:
            case TokenStrings.Type:
                return this.parseNominalType();
            case SYM_lbrack:
                return this.parseTupleType();
            case SYM_lbrace:
                return this.parseRecordType();
            case KW_function:
            case KW_pred:
            case KW_recursive_q:
            case KW_recursive:
                return this.parsePCodeType();
            case SYM_lparen: {
                this.consumeToken();
                const ptype = this.parseTypeSignature();
                this.ensureAndConsumeToken(SYM_rparen, "(TYPE _<- missing paren?");

                return ptype;
            }
            case TokenStrings.ScopeName: {
                //TODO: This is a dummy case for the parse provides call in pass1 where we just need to scan and discard the type info -- we should actually write a better pass for this
                this.consumeToken();
                this.parseTermList();
                return new NominalTypeSignature("Core", ["DummySig"]);
            }
            case SYM_percent: {
                const lve = this.parseLiteralExpression("literal type");
                return new LiteralTypeSignature(lve);
            }
            default: {
                this.raiseError(this.getCurrentLine(), "Could not parse type");
                return new ParseErrorTypeSignature();
            }
        }
    }

    private parseTemplateTypeReference(): TypeSignature {
        const tname = this.consumeTokenAndGetValue();
        this.m_penv.useTemplateType(tname);

        return new TemplateTypeSignature(tname);
    }

    private parseTermList(): TypeSignature[] {
        let terms: TypeSignature[] = [];
        if (this.testToken(SYM_le)) {
            try {
                this.setRecover(this.scanMatchingParens(SYM_le, SYM_ge));
                terms = this.parseListOf<TypeSignature>("template term list", SYM_le, SYM_ge, SYM_coma, () => {
                    return this.parseTypeSignature();
                });

                this.clearRecover();
            }
            catch (ex) {
                this.processRecover();
            }
        }
        return terms;
    }

    private parseNominalType(): TypeSignature {
        let ns: string | undefined = undefined;
        if (this.testToken(TokenStrings.Namespace)) {
            ns = this.consumeTokenAndGetValue();
            this.ensureAndConsumeToken(SYM_coloncolon, "nominal type after namespace");
        }

        const tname = this.consumeTokenAndGetValue();
        ns = this.m_penv.tryResolveNamespace(ns, tname);
        if (ns === undefined) {
            ns = "[Unresolved Error]";
        }

        let tnames: string[] = [tname];
        let terms: TypeSignature[] = this.parseTermList();

        while (this.testFollows(SYM_coloncolon, TokenStrings.Type)) {
            this.ensureAndConsumeToken(SYM_coloncolon, "nominal type after nested type");

            this.ensureToken(TokenStrings.Type, "nominal type after scope operator");
            const stname = this.consumeTokenAndGetValue();
            tnames.push(stname);

            const sterms = this.parseTermList();
            terms = [...terms, ...sterms];
        }

        return new NominalTypeSignature(ns as string, tnames, terms);
    }

    private parseTupleType(): TypeSignature {
        let entries: TypeSignature[] = [];

        try {
            this.setRecover(this.scanMatchingParens(SYM_lbrack, SYM_rbrack));
            entries = this.parseListOf<TypeSignature>("tuple type", SYM_lbrack, SYM_rbrack, SYM_coma, () => {
                const rtype = this.parseTypeSignature();

                return rtype;
            });

            this.clearRecover();
            return new TupleTypeSignature(entries);
        }
        catch (ex) {
            this.processRecover();
            return new ParseErrorTypeSignature();
        }
    }

    private parseRecordType(): TypeSignature {
        let entries: [string, TypeSignature][] = [];

        try {
            this.setRecover(this.scanMatchingParens(SYM_lbrace, SYM_rbrace));

            let pnames = new Set<string>();
            entries = this.parseListOf<[string, TypeSignature]>("record type", SYM_lbrace, SYM_lbrace, SYM_coma, () => {
                this.ensureToken(TokenStrings.Identifier, "record type entry property name");

                const name = this.consumeTokenAndGetValue();
                if(UnsafeFieldNames.includes(name)) {
                    this.raiseError(this.getCurrentLine(), `Property name "${name}" is ambigious with the methods that record may provide`);
                }

                if(pnames.has(name)) {
                    this.raiseError(this.getCurrentLine(), `Duplicate property name "${name}" in record declaration`);
                }
                pnames.add(name);

                this.ensureAndConsumeToken(SYM_colon, "record type property type");
                const rtype = this.parseTypeSignature();

                return [name, rtype];
            });

            this.clearRecover();
            return new RecordTypeSignature(entries);
        }
        catch (ex) {
            this.processRecover();
            return new ParseErrorTypeSignature();
        }
    }

    private parsePCodeType(): TypeSignature {
        let recursive: "yes" | "no" | "cond" = "no";
        if (this.testAndConsumeTokenIf(KW_recursive_q)) {
            recursive = "cond";
        }
        if (this.testAndConsumeTokenIf(KW_recursive)) {
            recursive = "yes";
        }

        const ispred = this.testToken(KW_pred);
        this.consumeToken();

        try {
            this.setRecover(this.scanMatchingParens(SYM_lparen, SYM_rparen));

            const params = this.parseListOf<TypeSignature>("lambda function parameters", SYM_lparen, SYM_rparen, SYM_coma, () => {
                return this.parseTypeSignature();
            });

            this.ensureAndConsumeToken(SYM_arrow, "lambda type reference");
            const resultInfo = this.parseResultType(true);

            this.clearRecover();
            return new FunctionTypeSignature(false, recursive, params, resultInfo, ispred);
        }
        catch (ex) {
            this.processRecover();
            return new ParseErrorTypeSignature();
        }
    }

    private static orOfTypeSignatures(t1: TypeSignature, t2: TypeSignature): TypeSignature {
        const types = [
            ...((t1 instanceof UnionTypeSignature) ? t1.types : [t1]),
            ...((t2 instanceof UnionTypeSignature) ? t2.types : [t2]),
        ];

        return new UnionTypeSignature(types);
    }

    private andOfTypeSignatures(t1: TypeSignature, t2: TypeSignature): TypeSignature {
        const types = [
            ...((t1 instanceof AndTypeSignature) ? t1.types : [t1]),
            ...((t2 instanceof AndTypeSignature) ? t2.types : [t2]),
        ];

        return new AndTypeSignature(types);
    }

    ////
    //Expression parsing
    private parseArguments(lparen: string, rparen: string): Expression[] {
        let args: Expression[] = [];

        try {
            this.setRecover(this.scanMatchingParens(lparen, rparen));

            this.consumeToken();
            while (!this.testAndConsumeTokenIf(rparen)) {
                let exp = this.parseExpression();
                args.push(exp);

                if (this.testAndConsumeTokenIf(SYM_coma)) {
                    this.ensureNotToken(rparen, "argument list after \",\"");
                }
                else {
                    this.ensureToken(rparen, "argument list -- maybe missing a \",\"");
                }
            }

            this.clearRecover();
            return args;
        }
        catch (ex) {
            this.processRecover();
            return [];
        }
    }

    private parseTemplateArguments(): TypeSignature[] {
        try {
            this.setRecover(this.scanMatchingParens(SYM_le, SYM_ge));
            let targs: TypeSignature[] = [];

            this.consumeToken();
            while (!this.testAndConsumeTokenIf(SYM_ge)) {
                targs.push(this.parseTypeSignature());

                if (this.testAndConsumeTokenIf(SYM_coma)) {
                    this.ensureNotToken(SYM_ge, "template argument list after \",\"");
                }
                else {
                    this.ensureToken(SYM_ge, "template argument list -- maybe missing a \",\"");
                }
            }

            this.clearRecover();
            return targs;
        }
        catch (ex) {
            this.processRecover();
            return [];
        }
    }

    private parseRecursiveAnnotation(): RecursiveAnnotation {
        let recursive: "yes" | "no" | "cond" = "no";
        
        this.consumeToken();
        if (!this.testToken(KW_recursive) && !this.testToken(KW_recursive_q)) {
            this.raiseError(this.getCurrentLine(), "Expected recursive annotation");
        }

        this.ensureToken(SYM_rbrack, "recursive annotation");
         
        return recursive;
    }

    private parseConstructorPrimary(otype: TypeSignature): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const args = this.parseArguments(SYM_lbrace, SYM_rbrace);

        return new ConstructorPrimaryExpression(sinfo, otype, args);
    }
    
    private parsePCodeTerm(): Expression {
        const line = this.getCurrentLine();
        const sinfo = this.getCurrentSrcInfo();

        let isrecursive: "yes" | "no" | "cond" = "no";
        if(this.testAndConsumeTokenIf(KW_recursive)) {
            isrecursive = "yes";
        }
        else if(this.testAndConsumeTokenIf(KW_recursive_q)) {
            isrecursive = "cond";
        }
        else {
            isrecursive = "no";
        }

        const ispred = this.testToken(KW_pred);
        this.consumeToken();

        const sig = this.parseInvokableCommon(ispred ? InvokableKind.PCodePred : InvokableKind.PCodeFn, false, [], isrecursive, [], [...this.m_penv.getCurrentFunctionScope().getBoundTemplates()], undefined, false, undefined);
        const someAuto = sig.params.some((param) => param.type instanceof AutoTypeSignature) || (sig.resultType instanceof AutoTypeSignature);
        const allAuto = sig.params.every((param) => param.type instanceof AutoTypeSignature) && (sig.resultType instanceof AutoTypeSignature);
        if (someAuto && !allAuto) {
            this.raiseError(line, "Cannot have mixed of auto propagated and explicit types on lambda arguments/return");
        }

        sig.captureVarSet.forEach((v) => {
            this.m_penv.useLocalVar(v);
        });

        sig.captureTemplateSet.forEach((t) => {
            this.m_penv.useTemplateType(t);
        });

        return new ConstructorPCodeExpression(sinfo, allAuto, sig);
    }

    private parseFollowTypeTag(incontext: string): TypeSignature {
        this.ensureAndConsumeToken(TokenStrings.FollowTypeSep, incontext);

        if (this.testToken(TokenStrings.Template)) {
            return this.parseTemplateTypeReference();
        }
        else {
            const line = this.getCurrentLine();

            let ns: string | undefined = undefined;
            if (this.testToken(TokenStrings.Namespace)) {
                ns = this.consumeTokenAndGetValue();
                this.ensureAndConsumeToken(SYM_coloncolon, "namespace scope resolve");
            }

            const tname = this.consumeTokenAndGetValue();
            const ons = ns;
            ns = this.m_penv.tryResolveNamespace(ns, tname);
            if (ns === undefined) {
                this.raiseError(line, `Could not resolve namespace/type${ns !== undefined ? (" " + ons + SYM_coloncolon + tname) : tname}`);
            }

            return new NominalTypeSignature(ns as string, [tname], []);
        }
    }

    private parseLiteralExpression(incontext: string | undefined): LiteralExpressionValue {
        const sinfo = this.getCurrentSrcInfo();

        try {
            this.m_penv.pushFunctionScope(new FunctionScope(new Set<string>(), this.m_penv.getCurrentFunctionScope().getBoundTemplates(), this.m_penv.SpecialAutoSignature, true));
            const exp = this.parsePrefixExpression();
            const captured = this.m_penv.getCurrentFunctionScope().getCaptureVars();

            if(captured.size !== 0) {
                this.raiseError(sinfo.line, "Cannot reference local variables in literal expression");
            }

            this.m_penv.popFunctionScope();

            return new LiteralExpressionValue(exp);
        }
        catch (ex) {
            this.m_penv.popFunctionScope();
            throw ex;
        }
    }

    private parseConstExpression(capturesok: boolean): ConstantExpressionValue {
        const sinfo = this.getCurrentSrcInfo();

        try {
            this.m_penv.pushFunctionScope(new FunctionScope(new Set<string>(), this.m_penv.getCurrentFunctionScope().getBoundTemplates(), this.m_penv.SpecialAutoSignature, true));
            const exp = this.parseMapEntryConstructorExpression();
            const captured = this.m_penv.getCurrentFunctionScope().getCaptureVars();

            if(!capturesok && captured.size !== 0) {
                this.raiseError(sinfo.line, "Cannot reference local variables in constant expression");
            }

            this.m_penv.popFunctionScope();

            return new ConstantExpressionValue(exp, captured);
        }
        catch (ex) {
            this.m_penv.popFunctionScope();
            throw ex;
        }
    }

    private checkTypeScopeBasedExpressionFollowsParens(): boolean {
        const lpos = this.scanMatchingParens(SYM_lparen, SYM_rparen);
        const ptok = this.peekToken(lpos - this.m_cpos);

        return ptok === "::";
    }

    private parsePrimaryExpression(): Expression {
        const line = this.getCurrentLine();
        const sinfo = this.getCurrentSrcInfo();

        const tk = this.peekToken();
        if (tk === KW_none) {
            this.consumeToken();
            return new LiteralNoneExpression(sinfo);
        }
        else if (tk === KW_nothing) {
            this.consumeToken();
            return new LiteralNothingExpression(sinfo);
        }
        else if (tk === KW_true || tk === KW_false) {
            this.consumeToken();
            return new LiteralBoolExpression(sinfo, tk === KW_true);
        }
        else if (tk === TokenStrings.Int) {
            const istr = this.consumeTokenAndGetValue();
            return new LiteralIntegralExpression(sinfo, istr, this.m_penv.SpecialIntSignature);
        }
        else if (tk === TokenStrings.Nat) {
            const istr = this.consumeTokenAndGetValue();
            return new LiteralIntegralExpression(sinfo, istr, this.m_penv.SpecialNatSignature);
        }
        else if (tk === TokenStrings.Float) {
            const fstr = this.consumeTokenAndGetValue();
            return new LiteralFloatPointExpression(sinfo, fstr, this.m_penv.SpecialFloatSignature);
        }
        else if (tk === TokenStrings.Decimal) {
            const fstr = this.consumeTokenAndGetValue();
            return new LiteralFloatPointExpression(sinfo, fstr, this.m_penv.SpecialDecimalSignature);
        }
        else if (tk === TokenStrings.BigInt) {
            const istr = this.consumeTokenAndGetValue();
            return new LiteralIntegralExpression(sinfo, istr, this.m_penv.SpecialBigIntSignature);
        }
        else if (tk === TokenStrings.BigNat) {
            const istr = this.consumeTokenAndGetValue();
            return new LiteralIntegralExpression(sinfo, istr, this.m_penv.SpecialBigNatSignature);
        }
        else if (tk === TokenStrings.Rational) {
            const istr = this.consumeTokenAndGetValue();
            return new LiteralRationalExpression(sinfo, istr, this.m_penv.SpecialRationalSignature);
        }
        else if (tk === TokenStrings.String) {
            const sstr = this.consumeTokenAndGetValue(); //keep in original format
            return new LiteralStringExpression(sinfo, sstr);
        }
        else if (tk === TokenStrings.ASCIIString) {
            const sstr = this.consumeTokenAndGetValue(); //keep in original format
            return new LiteralASCIIStringExpression(sinfo, sstr.slice("ascii{".length, sstr.length - "ascii{}".length));
        }
        else if (tk === TokenStrings.TypedString) {
            const sstr = this.consumeTokenAndGetValue(); //keep in original format
            const ttype = this.parseFollowTypeTag("typed string");
    
            return new LiteralTypedStringExpression(sinfo, sstr, ttype);
        }
        else if (tk === TokenStrings.TemplateString) {
            const sstr = this.consumeTokenAndGetValue(); //keep in original format
            return new LiteralTemplateStringExpression(sinfo, sstr.slice(1));
        }
        else if (tk === TokenStrings.TemplateASCIIString) {
            const sstr = this.consumeTokenAndGetValue(); //keep in original format
            return new LiteralASCIITemplateStringExpression(sinfo, sstr.slice("ascii{$".length, sstr.length - "ascii{$}".length));
        }
        else if (tk === TokenStrings.Regex) {
            const restr = this.consumeTokenAndGetValue(); //keep in escaped format
            const re = BSQRegex.parse(this.m_penv.getCurrentNamespace(), restr);
            if(typeof(re) === "string") {
                this.raiseError(line, re);
            }

            this.m_penv.assembly.addLiteralRegex(re as BSQRegex);
            return new LiteralRegexExpression(sinfo, re as BSQRegex);
        }
        else if (tk === KW_ok || tk === KW_err || tk === KW_something) {
            this.consumeToken();
            this.ensureAndConsumeToken("(", tk + " constructor");
            let arg = new LiteralNoneExpression(this.getCurrentSrcInfo());
            if(tk === KW_ok || tk === KW_something) {
                arg = this.parseExpression();
            }
            else {
                if(!this.testToken(")")) {
                    arg = this.parseExpression();
                }
            }
            this.ensureAndConsumeToken(")", tk + "constructor -- missing closing \")\"?");

            return new SpecialConstructorExpression(sinfo, tk, arg);
        }
        else if (tk === SYM_percent) {
            this.consumeToken();
            const vtype = this.parseTypeSignature();
            return new LiteralTypeValueExpression(sinfo, vtype);
        }
        else if (tk === KW_env) {
            this.consumeToken();

            let opttype = this.m_penv.SpecialStringSignature;
            if(this.testAndConsumeTokenIf(SYM_le)) {
                opttype = this.parseTypeSignature();
                this.ensureAndConsumeToken(SYM_ge, "");
            }

            this.ensureAndConsumeToken(SYM_lbrack, "environment access");
            this.ensureToken(TokenStrings.String, "environment access");
            const keyname = this.consumeTokenAndGetValue();
            this.ensureToken(SYM_rbrack, "environment access");

            return new AccessEnvValue(sinfo, keyname, opttype);
        }
        else if (tk === KW_self) {
            this.consumeToken();

            this.ensureAndConsumeToken(SYM_dot, "self field access");
            this.ensureNotToken(TokenStrings.Identifier, "self field access");
            const sfname = this.consumeTokenAndGetValue();

            return new TaskSelfFieldExpression(sinfo, sfname);
        }
        else if (tk === TokenStrings.Identifier) {
            let namestr = this.consumeTokenAndGetValue();

            const tryfunctionns = this.m_penv.tryResolveNamespace(undefined, namestr);
            const isvar = this.m_penv.isVarDefinedInAnyScope(namestr) || tryfunctionns === undefined || namestr.startsWith("$");
            if (isvar) {
                const istr = this.m_penv.useLocalVar(namestr);

                if (this.testToken(SYM_lbrack)) {
                    const rec = this.parseRecursiveAnnotation();
                    const args = this.parseArguments(SYM_lparen, SYM_rparen);

                    return new PCodeInvokeExpression(sinfo, istr, rec, args);
                }
                else if (this.testToken(SYM_lparen)) {
                    const args = this.parseArguments(SYM_lparen, SYM_rparen);

                    return new PCodeInvokeExpression(sinfo, istr, "no", args);
                }
                else {
                    return new AccessVariableExpression(sinfo, istr);
                }
            }
            else {
                if (tryfunctionns === undefined) {
                    this.raiseError(line, `Cannot resolve namespace for "${namestr}"`);
                }

                const targs = this.testToken(SYM_le) ? this.parseTemplateArguments() : [];
                const rec = this.testToken(SYM_lbrack) ? this.parseRecursiveAnnotation() : "no";
                const args = this.parseArguments(SYM_lparen, SYM_rparen);

                return new CallNamespaceFunctionOrOperatorExpression(sinfo, tryfunctionns as string, namestr, targs, rec, args);
            }
        }
        else if (tk === KW_fn || this.testFollows(KW_recursive, KW_fn) || this.testFollows(KW_recursive_q, KW_fn) || tk === KW_pred || this.testFollows(KW_recursive, KW_pred) || this.testFollows(KW_recursive_q, KW_pred)) {
            return this.parsePCodeTerm();
        }
        else if (tk === SYM_lparen && !this.checkTypeScopeBasedExpressionFollowsParens()) {
            try {
                this.setRecover(this.scanMatchingParens(SYM_lparen, SYM_rparen));

                this.consumeToken();
                const exp = this.parseExpression();
                this.ensureAndConsumeToken(SYM_rparen, "(Exp _<- Missing \")\"?");

                this.clearRecover();
                return exp;
            }
            catch (ex) {
                this.processRecover();
                return new InvalidExpression(sinfo);
            }
        }
        else if (this.testToken(SYM_lbrack)) {
            const args = this.parseArguments(SYM_lbrack, SYM_rbrack);
            return new ConstructorTupleExpression(sinfo, args);
        }
        else if  (this.testToken(SYM_lbrace)) {
            const args = this.parseArguments(SYM_lbrace, SYM_rbrace);
            return new ConstructorRecordExpression(sinfo, args);
        }
        else if (this.testToken(SYM_land) || this.testToken(SYM_lor)) {
            const op = this.consumeTokenAndGetValue() as "/\\" | "\\/";
            const args = this.parseArguments(SYM_lparen, SYM_rparen);
            if(op === SYM_land) {
                return new LogicActionAndExpression(sinfo, args);
            }
            else {
                return new LogicActionOrExpression(sinfo, args);
            }
        }
        else if (this.testFollows(TokenStrings.Namespace, SYM_coloncolon, TokenStrings.Identifier)) {
            //it is a namespace access of some type
            let ns: string | undefined = this.consumeTokenAndGetValue();
            this.consumeToken();
            const name = this.consumeTokenAndGetValue();

            if(ns === "Task" && (name === "getTaskID" || name === "isCanceled")) {
                if(name === "getTaskID") {
                    return new TaskGetIDExpression(sinfo);
                }
                else {
                    return new TaskCancelRequestedExpression(sinfo);
                }
            }
            else {
                ns = this.m_penv.tryResolveNamespace(ns, name);
                if (ns === undefined) {
                    ns = "[Unresolved Error]";
                }

                if (!this.testToken(SYM_le) && !this.testToken(SYM_lbrack) && !this.testToken(SYM_lparen)) {
                    //just a constant access
                    return new AccessNamespaceConstantExpression(sinfo, ns, name);
                }
                else {
                    const targs = this.testToken(SYM_le) ? this.parseTemplateArguments() : [];
                    const rec = this.testToken(SYM_lbrack) ? this.parseRecursiveAnnotation() : "no";
                    const args = this.parseArguments(SYM_lparen, SYM_rparen);

                    return new CallNamespaceFunctionOrOperatorExpression(sinfo, ns, name, targs, rec, args);
                }
            }
        }
        else if (this.testFollows(TokenStrings.Namespace, SYM_hash, TokenStrings.Identifier)) {
            //it is a namespace access of some formatter info
            let ns: string | undefined = this.consumeTokenAndGetValue();
            this.consumeToken();
            const name = this.consumeTokenAndGetValue();

            ns = this.m_penv.tryResolveNamespace(ns, name);
            if (ns === undefined) {
                ns = "[Unresolved Error]";
            }

            return new AccessFormatInfo(sinfo, ns, name);
        }
        else {
            const ttype = this.parseTypeSignature();

            if (this.testFollows(SYM_coloncolon, TokenStrings.Identifier)) {
                this.consumeToken();
                const name = this.consumeTokenAndGetValue();
                if (!this.testToken(SYM_le) && !this.testToken(SYM_lbrack) && !this.testToken(SYM_lparen) && !this.testToken(SYM_lbrace)) {
                    //just a static access
                    return new AccessStaticFieldExpression(sinfo, ttype, name);
                }
                else {
                    const targs = this.testToken(SYM_le) ? this.parseTemplateArguments() : [];
                    const rec = this.testToken(SYM_lbrack) ? this.parseRecursiveAnnotation() : "no";
                    const args = this.parseArguments(SYM_lparen, SYM_rparen);
                    return new CallStaticFunctionExpression(sinfo, ttype, name, targs, rec, args);
                }
            }
            else if (this.testFollows(SYM_lbrace)) {
                return this.parseConstructorPrimary(ttype);
            }
            else {
                this.raiseError(line, "Unknown token sequence in parsing expression");
                return new InvalidExpression(sinfo);
            }
        }
    }
    
    private literalPrefixStackAndTypedConstructorHandler(ops: ("!" | "+" | "-")[]): [Expression, ("!" | "+" | "-")[]] {
        const sinfo = this.getCurrentSrcInfo();

        let exp = this.parsePrimaryExpression();
        if (this.testToken(TokenStrings.FollowTypeSep)) {
            const ttype = this.parseFollowTypeTag("typed primitive");

            if (exp instanceof LiteralIntegralExpression) {
                return [new LiteralTypedPrimitiveConstructorExpression(sinfo, exp.value, exp.itype, ttype), ops];
            }
            else if (exp instanceof LiteralFloatPointExpression) {
                return [new LiteralTypedPrimitiveConstructorExpression(sinfo, exp.value, exp.fptype, ttype), ops];
            }
            else if (exp instanceof LiteralRationalExpression) {
                return [new LiteralTypedPrimitiveConstructorExpression(sinfo, exp.value, exp.rtype, ttype), ops];
            }
            else {
                this.raiseError(sinfo.line, "Expected literal value -- int, float, or rational");

                return [new InvalidExpression(sinfo), ops];
            }
        }
        else {
            return [exp, ops];
        }
    }

    private parseTupleIndex(): number {
        if(this.testToken(TokenStrings.Numberino)) {
            const niov = this.consumeTokenAndGetValue();
            return Number.parseInt(niov);
        }
        else if(this.testToken(TokenStrings.Int)) {
            const iv = this.consumeTokenAndGetValue();
            return Number.parseInt(iv.substr(0, iv.length - 1));
        }
        else if(this.testToken(TokenStrings.Nat)) {
            const nv = this.consumeTokenAndGetValue();
            return Number.parseInt(nv.substr(0, nv.length - 1));
        }
        else {
            this.raiseError(this.getCurrentSrcInfo().line, "Expected an Int or a Nat literal");
            return -1;
        }
    }

    private handleSpecialCaseMethods(sinfo: SourceInfo, specificResolve: TypeSignature | undefined, name: string): PostfixOperation {
        if (specificResolve !== undefined) {
            this.raiseError(this.getCurrentLine(), "Cannot use specific resolve on special methods");
        }

        const line = sinfo.line;
        if (name === "is") {
            this.ensureAndConsumeToken(SYM_le, "is");
            const istype = this.parseTypeSignature();
            this.ensureAndConsumeToken(SYM_ge, "is");
            this.ensureAndConsumeToken(SYM_lparen, "is");
            this.ensureAndConsumeToken(SYM_rparen, "is");

            return new PostfixIs(sinfo, istype);
        }
        else if (name === "isSome") {
            this.ensureAndConsumeToken(SYM_lparen, "isSome");
            this.ensureAndConsumeToken(SYM_rparen, "isSome");

            return new PostfixIs(sinfo, this.m_penv.SpecialSomeSignature);
        }
        else if (name === "isNone") {
            this.ensureAndConsumeToken(SYM_lparen, "isNone");
            this.ensureAndConsumeToken(SYM_rparen, "isNone");

            return new PostfixIs(sinfo, this.m_penv.SpecialNoneSignature);
        }
        else if (name === "as") {
            this.ensureAndConsumeToken(SYM_le, "as");
            const astype = this.parseTypeSignature();
            this.ensureAndConsumeToken(SYM_ge, "as");
            this.ensureAndConsumeToken(SYM_lparen, "as");
            this.ensureAndConsumeToken(SYM_rparen, "as");

            return new PostfixAs(sinfo, astype);
        }
        else if (name === "hasIndex") {
            this.ensureAndConsumeToken(SYM_le, "hasIndex");
            const idx = this.parseTupleIndex();
            this.ensureAndConsumeToken(SYM_ge, "hasIndex");
            this.ensureAndConsumeToken(SYM_lparen, "hasIndex");
            this.ensureAndConsumeToken(SYM_rparen, "hasIndex");
            return new PostfixHasIndex(sinfo, idx);
        }
        else if (name === "hasProperty") {
            this.ensureAndConsumeToken(SYM_le, "hasProperty");
            this.ensureToken(TokenStrings.Identifier, "hasProperty");
            const pname = this.consumeTokenAndGetValue(); 
            this.ensureAndConsumeToken(SYM_ge, "hasProperty");
            this.ensureAndConsumeToken(SYM_lparen, "hasProperty");
            this.ensureAndConsumeToken(SYM_rparen, "hasProperty");
            return new PostfixHasProperty(sinfo, pname);
        }
        else if (name === "getIndexOrNone") {
            this.ensureAndConsumeToken(SYM_le, "getIndexOrNone");
            const idx = this.parseTupleIndex();
            this.ensureAndConsumeToken(SYM_ge, "getIndexOrNone");
            this.ensureAndConsumeToken(SYM_lparen, "getIndexOrNone");
            this.ensureAndConsumeToken(SYM_rparen, "getIndexOrNone");
            return new PostfixGetIndexOrNone(sinfo, idx);
        }
        else if (name === "getIndexOption") {
            this.ensureAndConsumeToken(SYM_le, "getIndexOption");
            const idx = this.parseTupleIndex();
            this.ensureAndConsumeToken(SYM_ge, "getIndexOption");
            this.ensureAndConsumeToken(SYM_lparen, "getIndexOption");
            this.ensureAndConsumeToken(SYM_rparen, "getIndexOption");
            return new PostfixGetIndexOption(sinfo, idx);
        }
        else if (name === "getPropertyOrNone") {
            this.ensureAndConsumeToken(SYM_le, "getPropertyOrNone");
            this.ensureToken(TokenStrings.Identifier, "getPropertyOrNone");
            const pname = this.consumeTokenAndGetValue(); 
            this.ensureAndConsumeToken(SYM_ge, "getPropertyOrNone");
            this.ensureAndConsumeToken(SYM_lparen, "getPropertyOrNone");
            this.ensureAndConsumeToken(SYM_rparen, "getPropertyOrNone");
            return new PostfixGetPropertyOrNone(sinfo, pname);
        }
        else if (name === "getPropertyOption") {
            this.ensureAndConsumeToken(SYM_le, "getPropertyOption");
            this.ensureToken(TokenStrings.Identifier, "getPropertyOption");
            const pname = this.consumeTokenAndGetValue(); 
            this.ensureAndConsumeToken(SYM_ge, "getPropertyOption");
            this.ensureAndConsumeToken(SYM_lparen, "getPropertyOption");
            this.ensureAndConsumeToken(SYM_rparen, "getPropertyOption");
            return new PostfixGetPropertyOption(sinfo, pname);
        }
        else {
            this.raiseError(line, "unknown special operation");
            return (undefined as unknown) as PostfixOperation;
        }
    }

    private parsePostfixExpression(pfxops: ("!" | "+" | "-")[]): [Expression, ("!" | "+" | "-")[]] {
        const rootinfo = this.getCurrentSrcInfo();
        let [rootexp, remainingops] = this.literalPrefixStackAndTypedConstructorHandler(pfxops);

        let ops: PostfixOperation[] = [];
        while (true) {
            const sinfo = this.getCurrentSrcInfo();

            if (this.testToken(SYM_dot)) {
                this.consumeToken();

                if (this.testToken(TokenStrings.Numberino)) {
                    const index = this.parseTupleIndex();
                    ops.push(new PostfixAccessFromIndex(sinfo, index));
                }
                else {
                    let specificResolve: TypeSignature | undefined = undefined;
                    if (this.testToken(TokenStrings.Namespace) || this.testToken(TokenStrings.Type) || this.testToken(TokenStrings.Template)) {
                        specificResolve = this.parseTypeSignature();
                        this.ensureAndConsumeToken(SYM_coloncolon, "type resolution specfier for postfix \".\" access");
                    }

                    this.ensureToken(TokenStrings.Identifier, "postfix \".\" access");
                    const name = this.consumeTokenAndGetValue();

                    if (name === "as" || name === "is" || name === "isSome" || name === "isNone"
                        || name === "hasIndex" || name === "getIndexOrNone" || name === "getIndexOption" 
                        || name === "hasProperty" || name === "getPropertyOrNone" || name === "getPropertyOption") {
                        ops.push(this.handleSpecialCaseMethods(sinfo, specificResolve, name));
                    }
                    else if (!(this.testToken(SYM_le) || this.testToken(SYM_lbrack) || this.testToken(SYM_lparen))) {
                        if (specificResolve !== undefined) {
                            this.raiseError(this.getCurrentLine(), "Encountered named access but given type resolver (only valid on method calls)");
                        }

                        ops.push(new PostfixAccessFromName(sinfo, name));
                    }
                    else {
                        if (this.testToken(SYM_le)) {
                            const nextnonlptokenidx = this.peekToken(1) === SYM_lparen ? this.scanLParens(this.m_cpos + 1) : this.m_cpos + 1;
                            if(nextnonlptokenidx === this.m_epos) {
                                this.raiseError(this.getCurrentLine(), "Truncated statement?");
                            }

                            const followtoken = this.m_tokens[nextnonlptokenidx].kind;
                            if (followtoken === TokenStrings.Namespace || followtoken === TokenStrings.Type || followtoken === TokenStrings.Template || followtoken ===  SYM_lbrack || followtoken === SYM_lbrace || followtoken === SYM_percent) {
                                const terms = this.parseTemplateArguments();
                                const rec = this.testToken(SYM_lbrack) ? this.parseRecursiveAnnotation() : "no";

                                const args = this.parseArguments(SYM_lparen, SYM_rparen);
                                ops.push(new PostfixInvoke(sinfo, specificResolve, name, terms, rec, args));
                            }
                            else {
                                if (specificResolve !== undefined) {
                                    this.raiseError(this.getCurrentLine(), "Encountered named access but given type resolver (only valid on method calls)");
                                }

                                ops.push(new PostfixAccessFromName(sinfo, name));
                            }
                        }
                        else {
                            const rec = this.testToken(SYM_lbrack) ? this.parseRecursiveAnnotation() : "no";

                            const args = this.parseArguments(SYM_lparen, SYM_rparen);
                            ops.push(new PostfixInvoke(sinfo, specificResolve, name, [], rec, args));
                        }
                    }
                }
            }
            else {
                if (ops.length === 0) {
                    return [rootexp, remainingops];
                }
                else {
                    return [new PostfixOp(rootinfo, rootexp, ops), remainingops];
                }
            }
        }
    }

    private parseStatementExpression(ops: ("!" | "+" | "-")[]): [Expression, ("!" | "+" | "-")[]] {
        if (this.testToken("if")) {
            return [this.parseIfExpression(), ops];
        }
        else if (this.testToken("switch")) {
            return [this.parseSwitchExpression(), ops];
        }
        else if (this.testToken("match")) {
            return [this.parseMatchExpression(), ops];
        }
        else {
            return this.parsePostfixExpression(ops);
        }
    }

    private prefixStackApplicationHandler(sinfo: SourceInfo, ops: ("!" | "+" | "-")[]): Expression {
        let [exp, remainingops] = this.parseStatementExpression(ops);
        
        for (let i = 0; i < remainingops.length; ++i) {
            const op = remainingops[i];

            if (op === SYM_bang) {
                exp = new PrefixNotOp(sinfo, exp);
            }
            else if (op === SYM_minus) {
                exp = new PrefixNegateOp(sinfo, exp);
            }
            else {
                return exp;
            }
        }

        return exp;
    }

    private parsePrefixExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();

        let ops:  ("!" | "+" | "-")[] = [];
        while(this.testToken(SYM_bang) || this.testToken(SYM_plus) || this.testToken(SYM_minus)) {
            ops.push(this.consumeTokenAndGetValue() as "!" | "+" | "-");
        }

        return this.prefixStackApplicationHandler(sinfo, ops.reverse());
    }

    private isMultiplicativeFollow(): boolean {
        if(this.testToken(SYM_times) || this.testToken(SYM_div)) {
            return true;
        }
        else {
            return false;
        }
    }

    private parseMultiplicativeExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parsePrefixExpression();

        if(!this.isMultiplicativeFollow()) {
            return exp;
        }
        else {
            let aexp: Expression = exp;
            while (this.isMultiplicativeFollow()) {
                const op = this.consumeTokenAndGetValue();

                const lhs = aexp;
                const rhs = this.parsePrefixExpression();
                if(op === SYM_times) {
                    return new BinMultExpression(sinfo, lhs, rhs);
                }
                else {
                    return new BinDivExpression(sinfo, lhs, rhs);
                }
            }

            return aexp;
        }
    }

    private isAdditiveFollow(): boolean {
        if(this.testToken(SYM_plus) || this.testToken(SYM_minus)) {
            return true;
        }
        else {
            return false;
        }
    }

    private parseAdditiveExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseMultiplicativeExpression();

        if(!this.isAdditiveFollow()) {
            return exp;
        }
        else {
            let aexp: Expression = exp;
            while (this.isAdditiveFollow()) {
                const op = this.consumeTokenAndGetValue();
                    
                const lhs = aexp;
                const rhs = this.parseMultiplicativeExpression();
                if(op === SYM_plus) {
                    return new BinAddExpression(sinfo, lhs, rhs);
                }
                else {
                    return new BinSubExpression(sinfo, lhs, rhs);
                }
            }

            return aexp;
        }
    }

    private parseRelationalExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseAdditiveExpression();

        if (this.testAndConsumeTokenIf(SYM_eqeqeq)) {
            return new BinKeyEqExpression(sinfo, exp, this.parseRelationalExpression());
        }
        else if(this.testAndConsumeTokenIf(SYM_bangeqeq)) {
            return new BinKeyNeqExpression(sinfo, exp, this.parseRelationalExpression());
        }
        else if(this.testAndConsumeTokenIf(SYM_eqeq)) {
            return new NumericEqExpression(sinfo, exp, this.parseRelationalExpression());
        }
        else if(this.testAndConsumeTokenIf(SYM_bangeq)) {
            return new NumericNeqExpression(sinfo, exp, this.parseRelationalExpression());
        }
        else if(this.testAndConsumeTokenIf(SYM_le)) {
            return new NumericLessExpression(sinfo, exp, this.parseRelationalExpression());
        }
        else if(this.testAndConsumeTokenIf(SYM_leq)) {
            return new NumericLessEqExpression(sinfo, exp, this.parseRelationalExpression());
        }
        else if(this.testAndConsumeTokenIf(SYM_ge)) {
            return new NumericGreaterExpression(sinfo, exp, this.parseRelationalExpression());
        }
        else if(this.testAndConsumeTokenIf(SYM_geq)) {
            return new NumericGreaterEqExpression(sinfo, exp, this.parseRelationalExpression());
        }
        else {
            return exp;
        }
    }

    private parseAndExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseRelationalExpression();

        if (this.testAndConsumeTokenIf(SYM_ampamp)) {
            return new BinLogicAndxpression(sinfo, exp, this.parseAndExpression());
        }
        else {
            return exp;
        }
    }

    private parseOrExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseAndExpression();

        if (this.testAndConsumeTokenIf(SYM_barbar)) {
            return new BinLogicOrExpression(sinfo, exp, this.parseOrExpression());
        }
        else {
            return exp;
        }
    }

    private parseImpliesExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();
        const exp = this.parseOrExpression();

        if (this.testAndConsumeTokenIf(SYM_implies)) {
            return new BinLogicImpliesExpression(sinfo, exp, this.parseImpliesExpression());
        }
        else {
            return exp;
        }
    }

    private parseMapEntryConstructorExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();

        const lexp = this.parseImpliesExpression();   
        if(this.testAndConsumeTokenIf("=>")) {
            const rexp = this.parseImpliesExpression();
        
            return new MapEntryConstructorExpression(sinfo, lexp, rexp);
        }
        else {
            return lexp;
        }
    }

    private parseIfExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();

        let conds: {cond: Expression, value: Expression}[] = [];

        this.consumeToken();
        this.ensureAndConsumeToken(SYM_lparen, "if expression test condition");
        const iftest = this.parseExpression();
        this.ensureAndConsumeToken(SYM_rparen, "if expression test condition");

        this.ensureAndConsumeToken(KW_then, "if expression value")
        const ifbody = this.parseExpression();
        conds.push({ cond: iftest, value: ifbody });

        while (this.testAndConsumeTokenIf(KW_elif)) {
            this.ensureAndConsumeToken(SYM_lparen, "elif expression test condition");
            const eliftest = this.parseExpression();
            this.ensureAndConsumeToken(SYM_rparen, "elif expression test condition");

            this.ensureAndConsumeToken(KW_then, "elif expression value")
            const elifbody = this.parseExpression();

            conds.push({ cond: eliftest, value: elifbody });
        }

        this.ensureAndConsumeToken(KW_else, "if expression else value");
        const elsebody = this.parseExpression();

        return new IfExpression(sinfo, conds, elsebody);
    }

    private parseSwitchLiteralGuard(): LiteralExpressionValue | undefined {
        if (this.testToken(TokenStrings.Identifier)) {
            const tv = this.consumeTokenAndGetValue();
            if (tv !== "_") {
                this.raiseError(this.getCurrentSrcInfo().line, "Expected wildcard match");
            }

            return undefined;
        }
        else {
            return this.parseLiteralExpression("switch literal guard");
        }
    }

    private parseSwitchExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();

        this.ensureAndConsumeToken(KW_switch, "switch expression dispatch value");

        this.ensureAndConsumeToken(SYM_lparen, "switch expression dispatch value");
        const mexp = this.parseExpression();
        this.ensureAndConsumeToken(SYM_rparen, "switch expression dispatch value");

        let entries: { condlit: LiteralExpressionValue | undefined, value: Expression }[] = [];
        this.ensureAndConsumeToken(SYM_lbrace, "switch expression options");
        
        const swlit = this.parseSwitchLiteralGuard();
        this.ensureAndConsumeToken(SYM_bigarrow, "switch expression entry");
        const swvalue = this.parseExpression();

        entries.push({ condlit: swlit, value: swvalue });
        while (this.testToken(SYM_bar)) {
            this.consumeToken();

            const swlitx = this.parseSwitchLiteralGuard();
            this.ensureAndConsumeToken(SYM_bigarrow, "switch expression entry");
            const swvaluex = this.parseExpression();

            entries.push({ condlit: swlitx, value: swvaluex });
        }
        this.ensureAndConsumeToken(SYM_rbrace, "switch expression options");

        return new SwitchExpression(sinfo, mexp, entries);
    }

    private parseMatchTypeGuard(): TypeSignature | undefined {
        if (this.testToken(TokenStrings.Identifier)) {
            const tv = this.consumeTokenAndGetValue();
            if (tv !== "_") {
                this.raiseError(this.getCurrentSrcInfo().line, "Expected wildcard match");
            }

            return undefined;
        }
        else {
            return this.parseTypeSignature();
        }
    }

    private parseMatchExpression(): Expression {
        const sinfo = this.getCurrentSrcInfo();

        this.ensureAndConsumeToken(KW_match, "match expression dispatch value");

        this.ensureAndConsumeToken(SYM_lparen, "match expression dispatch value");
        const mexp = this.parseExpression();
        this.ensureAndConsumeToken(SYM_rparen, "match expression dispatch value");
 
        let entries: { mtype: TypeSignature | undefined, value: Expression }[] = [];
        this.ensureAndConsumeToken(SYM_lbrace, "switch expression options");

        const mtype = this.parseMatchTypeGuard();
        this.ensureAndConsumeToken(SYM_bigarrow, "switch expression entry");
        const mvalue = this.parseExpression();

        entries.push({ mtype: mtype, value: mvalue });
        while (this.testToken(SYM_bar)) {
            this.consumeToken();
            
            const mtypex = this.parseMatchTypeGuard();
            this.ensureAndConsumeToken(SYM_bigarrow, "switch expression entry");
            const mvaluex = this.parseExpression();


            entries.push({ mtype: mtypex, value: mvaluex });
        }
        this.ensureAndConsumeToken(SYM_rbrace, "switch expression options");

        return new MatchExpression(sinfo, mexp, entries);
    }

    private parseExpression(): Expression {
        return this.parseMapEntryConstructorExpression();
    }

    ////
    //Statement parsing

    parseAssignmentVarInfo(sinfo: SourceInfo, vars: "let" | "var" | undefined): {name: string, vtype: TypeSignature} | undefined {
        this.ensureToken(TokenStrings.Identifier, "assignment statement");
        const name = this.consumeTokenAndGetValue();

        if (name === "_") {
            return undefined;
        }
        else {
            let itype = this.m_penv.SpecialAutoSignature;
            if (this.testAndConsumeTokenIf(":")) {
                itype = this.parseTypeSignature();
            }

            if (vars !== undefined) {
                return {name: name, vtype: itype};
            }
            else {
                if (!this.m_penv.getCurrentFunctionScope().isVarNameDefined(name)) {
                    this.raiseError(sinfo.line, `Variable "${name}" is not defined in scope`);
                }

                if (!(itype instanceof AutoTypeSignature)) {
                    this.raiseError(sinfo.line, `Cannot redeclare type of variable "${name}" on assignment`);
                }

                return {name: name, vtype: itype};
            }
        }
    }

    private parseTaskRunStatement(sinfo: SourceInfo, vv: {name: string, pos: number, vtype: TypeSignature}, assigncount: number): Statement {
        this.consumeToken();
        this.ensureAndConsumeToken(SYM_coloncolon, "Task run statement");
        this.ensureToken(TokenStrings.Identifier, "Task run statement");

        const name = this.consumeTokenAndGetValue();

        let argpack: {argn: string, argv: Expression}[] = [];
        if(this.testToken(SYM_lbrack)) {
            this.parseListOf("Task Run arguments", SYM_lbrack, SYM_rbrack, SYM_coma, () => {
                const argn = this.ensureAndConsumeToken(TokenStrings.Identifier, "Task Run argument name");
                this.ensureAndConsumeToken("=", "Task run argument");
                const argv = this.parseExpression();

                return {argn: argn, argv: argv};
            });
        }

        const terms = this.parseTemplateArguments();
        const args = this.parseArguments(SYM_lparen, SYM_rparen);

        if(name === "run") {
            if(terms.length === 1) {
                //x = Task::rin<T>(args)
            }
            else {
                //Distinguish on number of vars on lhs????

                if(assigncount === 1) {
                    //x, y = Task::run<T, U>([...], [...])
                }
                else {
                    //x = Task::dash<T, U>([...], [...]) <-- race for first done
                }
            }
        }
        else if (name === "all") {
            //x: List<V> = Task::all<T>(List<U>) <-- result list all done
        }
        else if (name === "race") {
            //x: Result<T, E> = Task::race<T>(List<U>) <-- result list all done
        }
        else {
            this.raiseError();
            return new InvalidStatement(sinfo);
        }
    }

    private parseLineStatement(): Statement {
        const line = this.getCurrentLine();
        const sinfo = this.getCurrentSrcInfo();

        const tk = this.peekToken();
        if (tk === SYM_semicolon) {
            this.consumeToken();
            return new EmptyStatement(sinfo);
        }
        else if (tk === KW_let || tk === KW_var) {
            this.consumeToken();
            const isConst = tk === KW_let;

            const assigns = this.parseEphemeralListOf(() => {
                return this.parseAssignmentVarInfo(this.getCurrentSrcInfo(), isConst ? KW_let : KW_var);
            });

            if(assigns.every((aa) => aa === undefined)) {
                this.raiseError(sinfo.line, "Vacuous variable declaration");
            }
                
            let vars: {name: string, pos: number, vtype: TypeSignature}[] = [];
            for(let i = 0; i < assigns.length; ++i) {
                let assign = assigns[i];

                if (assign !== undefined) {
                    if (this.m_penv.getCurrentFunctionScope().isVarNameDefined(assign.name)) {
                        this.raiseError(line, "Variable name is already defined");
                    }
                    this.m_penv.getCurrentFunctionScope().defineLocalVar(assign.name);

                    vars.push({ name: assign.name, pos: i, vtype: assign.vtype });
                }
            }

            const hasassign = this.testAndConsumeTokenIf(SYM_eq);
            if(hasassign && this.testToken(TokenStrings.Namespace) && this.peekTokenData() === "Task") {
                xxxx; //check for canceled expressoin here

                return this.parseTaskRunStatement(sinfo, vars[0]);
            }
            else {
                let exp: Expression | undefined = undefined;
                if(hasassign) {
                    exp = this.parseExpression();
                }

                if ((exp === undefined && isConst)) {
                    this.raiseError(line, "Const variable declaration must include an assignment to the variable");
                }

                this.ensureAndConsumeToken(SYM_semicolon, "assignment statement");

                if (vars.length === 1) {
                    if (exp !== undefined) {
                        this.raiseError(line, "Mismatch between variables declared and values provided");
                    }

                    const sexp = exp !== undefined ? exp : undefined;
                    return new VariableDeclarationStatement(sinfo, vars[0].name, isConst, vars[0].vtype, sexp);
                }
                else {
                    return new MultiReturnWithDeclarationStatement(sinfo, isConst, vars, exp);
                }
            }
        }
        else if (tk === TokenStrings.Identifier) {
            let decls = new Set<string>();
            const assigns = this.parseEphemeralListOf(() => {
                return this.parseStructuredAssignment(this.getCurrentSrcInfo(), undefined, decls);
            });

            if(assigns.length === 0 || (assigns.length === 1 && !(assigns[0] instanceof VariableAssignmentStructuredAssignment))) {
                this.raiseError(sinfo.line, "Vacuous variable assignment");
            }
            
            let vars: string[] = [];
            for(let i = 0; i < assigns.length; ++i) {
                if (assigns[i] instanceof IgnoreTermStructuredAssignment) {
                    vars.push("_");
                }
                else if(assigns[i] instanceof VariableAssignmentStructuredAssignment) {
                    const av = assigns[i] as VariableAssignmentStructuredAssignment;

                    if (!this.m_penv.getCurrentFunctionScope().isVarNameDefined(av.vname)) {
                        this.raiseError(line, "Variable name is not defined");
                    }

                    vars.push(av.vname);
                }
                else {
                    this.raiseError(sinfo.line, "Cannot have structured multi-assigns");
                }
            }

            this.ensureAndConsumeToken(SYM_eq, "assignment statement");

            let exps: Expression[] = this.parseEphemeralListOf(() => {
                return this.parseExpression();
            });
            this.ensureAndConsumeToken(SYM_semicolon, "assignment statement");

            if(vars.length === 1) {
                if (exps.length !== 1) {
                    this.raiseError(line, "Mismatch between variables assigned and values provided");
                }

                return new VariableAssignmentStatement(sinfo, vars[0], exps[0]); 
            }
            else {
                return new VariablePackAssignmentStatement(sinfo, vars, exps);
            }
        }
        else if (tk === KW_return) {
            this.consumeToken();

            if(this.testAndConsumeTokenIf(SYM_semicolon)) {
                return new ReturnStatement(sinfo, [new LiteralNoneExpression(sinfo)]);
            }
            else {
                const exps = this.parseEphemeralListOf(() => this.parseExpression());

                this.ensureAndConsumeToken(SYM_semicolon, "return statement");
                return new ReturnStatement(sinfo, exps);
            }
        }
        else if (tk === KW_abort) {
            this.consumeToken();

            this.ensureAndConsumeToken(SYM_semicolon, "abort statement");
            return new AbortStatement(sinfo);
        }
        else if (tk === KW_assert) {
            this.consumeToken();

            const level = this.parseBuildInfo("release");
            const exp = this.parseExpression();

            this.ensureAndConsumeToken(SYM_semicolon, "assert statement");
            return new AssertStatement(sinfo, exp, level);
        }
        else if (tk === KW__debug) {
            this.consumeToken();

            let value = undefined;
            if (this.testToken("(")) {
                this.consumeToken();
                value = this.parseExpression();
                this.ensureAndConsumeToken(SYM_rparen, "_debug statement");
            }

            this.ensureAndConsumeToken(SYM_semicolon, "_debug statement");
            return new DebugStatement(sinfo, value);
        }
        else if (tk === KW_ref) {
            //it is a namespace function call
            let ns: string | undefined = this.consumeTokenAndGetValue();
            this.consumeToken();
            const name = this.consumeTokenAndGetValue();

            ns = this.m_penv.tryResolveNamespace(ns, name);
            if (ns === undefined) {
                ns = "[Unresolved Error]";
            }

            const targs = this.testToken("<") ? this.parseTemplateArguments() : new TemplateArguments([]);
            const rec = this.testToken("[") ? this.parseRecursiveAnnotation() : "no";
            const args = this.parseArguments("(", ")");

            return new NakedCallStatement(sinfo, new CallNamespaceFunctionOrOperatorExpression(sinfo, ns, name, targs, rec, args, "std"));
        }
        else {
            //Task, Events, Log, etc.

            //we should find a type (nominal here) and it is a static invoke or a structured assign
            const ttype = this.parseTypeSignature();

            if (this.testToken("{")) {
                let decls = new Set<string>();
                const assigns = this.parseListOf<[string | undefined, StructuredAssignementPrimitive]>("{", "}", ",", () => {
                    if (this.testFollows(TokenStrings.Identifier, "=")) {
                        this.ensureToken(TokenStrings.Identifier);
                        const name = this.consumeTokenAndGetValue();
    
                        this.ensureAndConsumeToken("=");
                        const subg = this.parsePrimitiveStructuredAssignment(this.getCurrentSrcInfo(), undefined, decls);
    
                        return [name, subg];
                    }
                    else {
                        const subg = this.parsePrimitiveStructuredAssignment(this.getCurrentSrcInfo(), undefined, decls);
    
                        return [undefined, subg];
                    }
                })[0];

                const assign = new NominalStructuredAssignment(ttype, assigns);
                decls.forEach((dv) => {
                    if (this.m_penv.getCurrentFunctionScope().isVarNameDefined(dv)) {
                        this.raiseError(line, "Variable name is already defined");
                    }
                    this.m_penv.getCurrentFunctionScope().defineLocalVar(dv, dv, false);
                });

                this.ensureAndConsumeToken("=");
                const exp = this.parseExpression();
                this.ensureAndConsumeToken(";");

                return new StructuredVariableAssignmentStatement(sinfo, false, assign, exp);
            }
            else if(this.testFollows("::", TokenStrings.Identifier)) {
                this.consumeToken();
                const name = this.consumeTokenAndGetValue();
                const targs = this.testToken("<") ? this.parseTemplateArguments() : new TemplateArguments([]);
                const rec = this.testToken("[") ? this.parseRecursiveAnnotation() : "no";
                const args = this.parseArguments("(", ")");

                return new NakedCallStatement(sinfo, new CallStaticFunctionOrOperatorExpression(sinfo, ttype, name, targs, rec, args, "std"));
            }
            else if(this.testFollows("::", TokenStrings.Operator)) {
                this.consumeToken();
                const name = this.consumeTokenAndGetValue();
                const rec = this.testToken("[") ? this.parseRecursiveAnnotation() : "no";
                const args = this.parseArguments("(", ")");

                return new NakedCallStatement(sinfo, new CallStaticFunctionOrOperatorExpression(sinfo, ttype, name, new TemplateArguments([]), rec, args, "std"));
            }
            else {
                this.raiseError(line, "Unknown statement structure");

                return new InvalidStatement(sinfo);
            }
        }
    }

    private parseBlockStatement(): BlockStatement {
        const sinfo = this.getCurrentSrcInfo();

        this.m_penv.getCurrentFunctionScope().pushLocalScope();
        let stmts: Statement[] = [];
        try {
            this.setRecover(this.scanMatchingParens("{", "}"));

            this.consumeToken();
            while (!this.testAndConsumeTokenIf("}")) {
                stmts.push(this.parseStatement());
            }

            this.m_penv.getCurrentFunctionScope().popLocalScope();

            if (stmts.length === 0) {
                this.raiseError(this.getCurrentLine(), "No empty blocks -- requires at least ';'");
            }

            this.clearRecover();
            return new BlockStatement(sinfo, stmts);
        }
        catch (ex) {
            this.m_penv.getCurrentFunctionScope().popLocalScope();
            this.processRecover();
            return new BlockStatement(sinfo, [new InvalidStatement(sinfo)]);
        }
    }

    private parseIfElseStatement(): Statement {
        const sinfo = this.getCurrentSrcInfo();

        let conds: CondBranchEntry<BlockStatement>[] = [];

        this.ensureAndConsumeToken("if");
        this.ensureAndConsumeToken("(");
        const iftest = this.parseExpression();
        this.ensureAndConsumeToken(")");
        const ifbody = this.parseBlockStatement();

        conds.push(new CondBranchEntry<BlockStatement>(iftest, ifbody));

        while (this.testAndConsumeTokenIf("elif")) {
            this.ensureAndConsumeToken("(");
            const eliftest = this.parseExpression();
            this.ensureAndConsumeToken(")");
            const elifbody = this.parseBlockStatement();

            conds.push(new CondBranchEntry<BlockStatement>(eliftest, elifbody));
        }

        const elsebody = this.testAndConsumeTokenIf("else") ? this.parseBlockStatement() : undefined;

        return new IfElseStatement(sinfo, new IfElse<BlockStatement>(conds, elsebody));
    }

    private parseSwitchGuard(sinfo: SourceInfo): SwitchGuard {
        this.consumeTokenIf("|");
        
        if (this.testToken(TokenStrings.Identifier)) {
            const tv = this.consumeTokenAndGetValue();
            if (tv !== "_") {
                this.raiseError(sinfo.line, "Expected wildcard match");
            }

            return new WildcardSwitchGuard();
        }
        else {
            const lexp = this.parseLiteralExpression();
            return new LiteralSwitchGuard(lexp);
        }
    }

    private parseMatchGuard(sinfo: SourceInfo): [MatchGuard, Set<string>] {
        this.consumeTokenIf("|");
        
        if (this.testToken(TokenStrings.Identifier)) {
            const tv = this.consumeTokenAndGetValue();
            if (tv !== "_") {
                this.raiseError(sinfo.line, "Expected wildcard match");
            }

            return [new WildcardMatchGuard(), new Set<string>()];
        }
        else {
            if(this.testToken("[")) {
                let decls = new Set<string>();
                if (this.testFollows("[", TokenStrings.Identifier)) {
                    const assign = this.parseStructuredAssignment(this.getCurrentSrcInfo(), "let", decls);
                    return [new StructureMatchGuard(assign, decls), decls];
                }
                else {
                    const oftype = this.parseTupleType();
                    return [new TypeMatchGuard(oftype), decls];
                }
            }
            else if(this.testToken("{")) {
                let decls = new Set<string>();
                if (this.testFollows("{", TokenStrings.Identifier, "=")) {
                    const assign = this.parseStructuredAssignment(this.getCurrentSrcInfo(), "let", decls);
                    return [new StructureMatchGuard(assign, decls), decls];
                }
                else {
                    const oftype = this.parseRecordType();
                    return [new TypeMatchGuard(oftype), decls];
                }
            }
            else {
                let decls = new Set<string>();
                const oftype = this.parseTypeSignature();

                if (this.testToken("{")) {
                    const assigns = this.parseListOf<[string | undefined, StructuredAssignementPrimitive]>("{", "}", ",", () => {
                        if (this.testFollows(TokenStrings.Identifier, "=")) {
                            this.ensureToken(TokenStrings.Identifier);
                            const name = this.consumeTokenAndGetValue();

                            this.ensureAndConsumeToken("=");
                            const subg = this.parsePrimitiveStructuredAssignment(this.getCurrentSrcInfo(), "let", decls);

                            return [name, subg];
                        }
                        else {
                            const subg = this.parsePrimitiveStructuredAssignment(this.getCurrentSrcInfo(), "let", decls);

                            return [undefined, subg];
                        }
                    })[0];

                    const assign = new NominalStructuredAssignment(oftype, assigns);
                    return [new StructureMatchGuard(assign, decls), decls];
                }
                else {
                    return [new TypeMatchGuard(oftype), decls];
                }
            }
        }
    }

    private parseSwitchEntry<T>(sinfo: SourceInfo, tailToken: string, actionp: () => T): MatchEntry<T> {
        const guard = this.parseSwitchGuard(sinfo);
        this.ensureAndConsumeToken("=>");
        const action = actionp();

        const isokfollow = this.testToken(tailToken) || this.testToken("|");
        if(!isokfollow) {
            this.raiseError(this.getCurrentLine(), "Unknown token at end of match entry");
        }

        return new SwitchEntry<T>(guard, action);
    }

    private parseMatchEntry<T>(sinfo: SourceInfo, tailToken: string, actionp: () => T): MatchEntry<T> {
        const [guard, decls] = this.parseMatchGuard(sinfo);
        this.ensureAndConsumeToken("=>");

        if (decls.size !== 0) {
            this.m_penv.getCurrentFunctionScope().pushLocalScope();
            decls.forEach((dv) => {
                if (this.m_penv.getCurrentFunctionScope().isVarNameDefined(dv)) {
                    this.raiseError(sinfo.line, "Variable name is already defined");
                }
                this.m_penv.getCurrentFunctionScope().defineLocalVar(dv, dv, false);
            });
        }

        const action = actionp();

        if(decls.size !== 0) {
            this.m_penv.getCurrentFunctionScope().popLocalScope();
        }

        const isokfollow = this.testToken(tailToken) || this.testToken("|");
        if(!isokfollow) {
            this.raiseError(this.getCurrentLine(), "Unknown token at end of match entry");
        }

        return new MatchEntry<T>(guard, action);
    }

    private parseStatementActionInBlock(): BlockStatement {
        if(this.testToken("{")) {
            return this.parseBlockStatement();
        }
        else {
            return new BlockStatement(this.getCurrentSrcInfo(), [this.parseLineStatement()]);
        }
    }

    private parseSwitchStatement(): Statement {
        const sinfo = this.getCurrentSrcInfo();

        this.ensureAndConsumeToken("switch");

        this.ensureAndConsumeToken("(");
        const mexp = this.parseExpression();
        this.ensureAndConsumeToken(")");

        try {
            this.m_penv.getCurrentFunctionScope().pushLocalScope();
            this.m_penv.getCurrentFunctionScope().defineLocalVar("$switch", `$switch_@${sinfo.pos}`, true);

            let entries: MatchEntry<BlockStatement>[] = [];
            this.ensureAndConsumeToken("{");
            entries.push(this.parseSwitchEntry<BlockStatement>(this.getCurrentSrcInfo(), "}", () => this.parseStatementActionInBlock()));
            while (this.testToken("|")) {
                entries.push(this.parseSwitchEntry<BlockStatement>(this.getCurrentSrcInfo(), "}", () => this.parseStatementActionInBlock()));
            }
            this.ensureAndConsumeToken("}");

            return new SwitchStatement(sinfo, mexp, entries);
        }
        finally {
            this.m_penv.getCurrentFunctionScope().popLocalScope();
        }
    }

    private parseMatchStatement(): Statement {
        const sinfo = this.getCurrentSrcInfo();

        this.ensureAndConsumeToken("match");

        this.ensureAndConsumeToken("(");
        const mexp = this.parseExpression();
        this.ensureAndConsumeToken(")");

        try {
            this.m_penv.getCurrentFunctionScope().pushLocalScope();
            this.m_penv.getCurrentFunctionScope().defineLocalVar("$match", `$match_@${sinfo.pos}`, true);

            let entries: MatchEntry<BlockStatement>[] = [];
            this.ensureAndConsumeToken("{");
            entries.push(this.parseMatchEntry<BlockStatement>(this.getCurrentSrcInfo(), "}", () => this.parseStatementActionInBlock()));
            while (this.testToken("|")) {
                entries.push(this.parseMatchEntry<BlockStatement>(this.getCurrentSrcInfo(), "}", () => this.parseStatementActionInBlock()));
            }
            this.ensureAndConsumeToken("}");

            return new MatchStatement(sinfo, mexp, entries);
        }
        finally {
            this.m_penv.getCurrentFunctionScope().popLocalScope();
        }
    }

    private parseStatement(): Statement {
        if (this.testToken("if")) {
            return this.parseIfElseStatement();
        }
        else if (this.testToken("switch")) {
            return this.parseSwitchStatement();
        }
        else if (this.testToken("match")) {
            return this.parseMatchStatement();
        }
        else {
            return this.parseLineStatement();
        }
    }

    private parseBody(bodyid: string, file: string): BodyImplementation {
        if(this.testToken("=")) {
            this.consumeToken();
            const iname = this.consumeTokenAndGetValue();
            this.ensureAndConsumeToken(";")
            
            return new BodyImplementation(bodyid, file, iname);
        }
        else if (this.testToken("{")) {
            return new BodyImplementation(bodyid, file, this.parseBlockStatement());
        }
        else {
            return new BodyImplementation(bodyid, file, this.parseExpression());
        }
    }

    ////
    //Decl parsing

    private parseAttributes(): string[] {
        let attributes: string[] = [];
        while (Lexer.isAttributeKW(this.peekTokenData())) {
            attributes.push(this.consumeTokenAndGetValue());
        }
        return attributes;
    }

    private parseTemplateConstraint(hasconstraint: boolean): TypeSignature {
        if(!hasconstraint) {
            return this.m_penv.SpecialAnySignature;
        }
        else {
            return this.parseTypeSignature();
        }
    }

    private parseTermDeclarations(): TemplateTermDecl[] {
        let terms: TemplateTermDecl[] = [];
        if (this.testToken("<")) {
            terms = this.parseListOf<TemplateTermDecl>("<", ">", ",", () => {
                this.ensureToken(TokenStrings.Template);
                const templatename = this.consumeTokenAndGetValue();

                const isunique = this.testToken(TokenStrings.Identifier) && this.peekTokenData() === "unique";
                if(isunique) {
                    this.consumeToken();
                }

                const isgrounded = this.testToken(TokenStrings.Identifier) && this.peekTokenData() === "grounded";
                if(isgrounded) {
                    this.consumeToken();
                }

                const tconstraint = this.parseTemplateConstraint(!this.testToken(",") && !this.testToken(">") && !this.testToken("="));

                let isinfer = false;
                let defaulttype: TypeSignature | undefined = undefined;
                if (this.testAndConsumeTokenIf("=")) {
                    if (this.testAndConsumeTokenIf("?")) {
                        isinfer = true;
                    }
                    else {
                        defaulttype = this.parseTypeSignature();
                    }
                }

                return new TemplateTermDecl(templatename, isunique, isgrounded, tconstraint, isinfer, defaulttype);
            })[0];
        }
        return terms;
    }

    private parseSingleTermRestriction(): TemplateTypeRestriction {
        this.ensureToken(TokenStrings.Template);
        const templatename = this.consumeTokenAndGetValue();

        const isunique = this.testToken(TokenStrings.Identifier) && this.peekTokenData() === "unique";
        if(isunique) {
            this.consumeToken();
        }
        
        const isgrounded = this.testToken(TokenStrings.Identifier) && this.peekTokenData() === "grounded";
        if(isgrounded) {
            this.consumeToken();
        }

        const tconstraint = this.parseTemplateConstraint(true);

        return new TemplateTypeRestriction(new TemplateTypeSignature(templatename), isunique, isgrounded, tconstraint);
    }

    private parseTermRestrictionList(): TemplateTypeRestriction[] {
        const trl = this.parseSingleTermRestriction();
        if (this.testAndConsumeTokenIf("&&")) {
            const ands = this.parseTermRestrictionList();
            return [trl, ...ands];
        }
        else {
            return [trl];
        }
    }

    private parseTermRestriction(parencheck: boolean): TypeConditionRestriction | undefined {
        if(parencheck && !this.testToken("{")) {
            return undefined;
        }
        this.testAndConsumeTokenIf("{");

        if(parencheck) {
            this.testAndConsumeTokenIf("when");
        }
        
        const trl = this.parseTermRestrictionList();

        if(parencheck) {
            this.ensureAndConsumeToken("}");
        }

        return new TypeConditionRestriction(trl);
    }

    private parsePreAndPostConditions(sinfo: SourceInfo, argnames: Set<string>, rtype: TypeSignature): [PreConditionDecl[], PostConditionDecl[]] {
        let preconds: PreConditionDecl[] = [];
        try {
            this.m_penv.pushFunctionScope(new FunctionScope(new Set<string>(argnames), rtype, false));
            while (this.testToken("requires") || this.testToken("validate")) {
                const isvalidate = this.testToken("validate");
                this.consumeToken();
                
                let level: BuildLevel = "release";
                if (!isvalidate) {
                    level = this.parseBuildInfo(level);
                }

                const exp = this.parseOfExpression();

                let err = new LiteralNoneExpression(sinfo);
                if (this.testAndConsumeTokenIf("else")) {
                    err = this.parseExpression();
                }

                preconds.push(new PreConditionDecl(sinfo, isvalidate, level, exp, err));

                this.ensureAndConsumeToken(";");
            }
        } finally {
            this.m_penv.popFunctionScope();
        }

        let postconds: PostConditionDecl[] = [];
        try {
            this.m_penv.pushFunctionScope(new FunctionScope(argnames, rtype, false));
            while (this.testToken("ensures")) {
                this.consumeToken();

                const level = this.parseBuildInfo("release");
                const exp = this.parseExpression();

                postconds.push(new PostConditionDecl(sinfo, level, exp));

                this.ensureAndConsumeToken(";");
            }
        } finally {
            this.m_penv.popFunctionScope();
        }

        return [preconds, postconds];
    }

    private parseNamespaceDep(): {fromns: string, asns: string} {
        //import NS;
        //import NS as NS;

        this.ensureAndConsumeToken("import");
        this.ensureToken(TokenStrings.ScopeName);
        const fromns = this.consumeTokenAndGetValue();

        let nsp = {fromns: fromns, asns: fromns}; //case of import NS;
        if(this.testToken(TokenStrings.Identifier)) {
            const nn = this.consumeTokenAndGetValue();
            if(nn !== "as") {
                this.raiseError(this.getCurrentLine(), "Expected keyword 'as'");
            }

            this.ensureToken(TokenStrings.ScopeName);
            const asns = this.consumeTokenAndGetValue();

            nsp = {fromns: fromns, asns: asns};
        }
        
        this.ensureAndConsumeToken(";");

        return nsp;
    }

    private parseNamespaceUsing(currentDecl: NamespaceDeclaration) {
        //import NS;
        //import NS as NS;

        this.ensureAndConsumeToken("import");
        this.ensureToken(TokenStrings.Namespace);
        const fromns = this.consumeTokenAndGetValue();

        let asns = fromns; //case of import NS;
        if(this.testToken(TokenStrings.Identifier)) {
            const nn = this.consumeTokenAndGetValue();
            if(nn !== "as") {
                this.raiseError(this.getCurrentLine(), "Expected keyword 'as'");
            }

            this.ensureToken(TokenStrings.Namespace);
            asns = this.consumeTokenAndGetValue();
        }
        
        this.ensureAndConsumeToken(";");

        const ffns = this.m_penv.assembly.getNamespace(fromns);
        const names = [...ffns.declaredNames];

        //
        //TODO: Packaging!!!!
        //
        //Our versioning trick is going to be looking at the imported types and signatures (including transative dependencies). We will split up the 
        //package dependencies into "public" and "internal" -- internal dependencies can be resolved by finding a satisfying version OR cloning. The 
        //public dependences can be part of the exported signatures and must be resolved by finding satifying versions with other packages. 
        //
        //The full NS SHOULD include a part like packageVN, where N is the major version number of the root package. This will allow multiple 
        //coexisting major versions of a package to be used in an application. Versioning must specify a major number or MajorX+, the others 
        //can be *, X+, X-Y, or X-
        //Good design practice would be put the public API type decls in one package and the API sigs + impls in thier own -- this way changing 
        //an API sig only forces updates to that package and the types + impl can be shared with the older versions if needed.
        //

        currentDecl.usings.push(new NamespaceUsing(fromns, asns, names));
    }

    private parseNamespaceTypedef(currentDecl: NamespaceDeclaration) {
        //typedef NAME<T...> = TypeConstraint;

        const attributes = this.parseAttributes();

        this.ensureAndConsumeToken("typedef");
        this.ensureToken(TokenStrings.Type);
        const tyname = this.consumeTokenAndGetValue();

        if (currentDecl.checkDeclNameClash(currentDecl.ns, tyname)) {
            this.raiseError(this.getCurrentLine(), "Collision between typedef and other names");
        }

        const terms = this.parseTermDeclarations();

        this.ensureAndConsumeToken("=");
        const rpos = this.scanToken(";");
        if (rpos === this.m_epos) {
            this.raiseError(this.getCurrentLine(), "Missing ; on typedef");
        }

        const btype = this.parseTypeSignature();
        this.consumeToken();

        currentDecl.typeDefs.set((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + tyname, new NamespaceTypedef(attributes, currentDecl.ns, tyname, terms, btype));
    }

    private parseProvides(iscorens: boolean, endtoken: string[]): [TypeSignature, TypeConditionRestriction | undefined][] {
        let provides: [TypeSignature, TypeConditionRestriction | undefined][] = [];
        if (this.testAndConsumeTokenIf("provides")) {
            while (!endtoken.some((tok) => this.testToken(tok))) {
                this.consumeTokenIf(",");

                const pv = this.parseTypeSignature();
                let res: TypeConditionRestriction | undefined = undefined;
                if(this.testAndConsumeTokenIf("when")) {
                    res = this.parseTermRestriction(false);
                }
                provides.push([pv, res]);
            }
        }
        
        if (!iscorens) {
            provides.push([new NominalTypeSignature("Core", ["Object"]), undefined]);
        }

        return provides;
    }

    private parseConstMember(staticMembers: StaticMemberDecl[], allMemberNames: Set<string>, attributes: string[]) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] const NAME: T = exp;
        this.ensureAndConsumeToken("const");

        this.ensureToken(TokenStrings.Identifier);
        const sname = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(":");
        const stype = this.parseTypeSignature();

        this.ensureAndConsumeToken("=");
        const value = this.parseConstExpression(false);

        this.ensureAndConsumeToken(";");

        if (allMemberNames.has(sname)) {
            this.raiseError(this.getCurrentLine(), "Collision between const and other names");
        }

        allMemberNames.add(sname);
        staticMembers.push(new StaticMemberDecl(sinfo, this.m_penv.getCurrentFile(), attributes, sname, stype, value));
    }

    private parseStaticFunction(staticFunctions: StaticFunctionDecl[], allMemberNames: Set<string>, attributes: string[]) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] function NAME<T where C...>(params): type [requires...] [ensures...] { ... }
        this.ensureAndConsumeToken("function");
        const termRestrictions = this.parseTermRestriction(true);

        this.ensureToken(TokenStrings.Identifier);
        const fname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        let recursive: "yes" | "no" | "cond" = "no";
        if (Parser.attributeSetContains("recursive", attributes) || Parser.attributeSetContains("recursive?", attributes)) {
            recursive = Parser.attributeSetContains("recursive", attributes) ? "yes" : "cond";
        }
        const sig = this.parseInvokableCommon(InvokableKind.Basic, Parser.attributeSetContains("abstract", attributes), attributes, recursive, terms, termRestrictions);

        if (allMemberNames.has(fname)) {
            this.raiseError(this.getCurrentLine(), "Collision between static and other names");
        }
        allMemberNames.add(fname);

        staticFunctions.push(new StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), fname, sig));
    }

    private parseStaticOperator(staticOperators: StaticOperatorDecl[], allMemberNames: Set<string>, attributes: string[]) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] operator NAME(params): type [requires...] [ensures...] { ... }
        this.ensureAndConsumeToken("operator");
        const termRestrictions = this.parseTermRestriction(true);

        if(!this.testToken(TokenStrings.Identifier) && !this.testToken(TokenStrings.Operator)) {
            this.raiseError(sinfo.line, "Expected valid name for operator");
        }

        const fname = this.consumeTokenAndGetValue();
        let recursive: "yes" | "no" | "cond" = "no";
        if (Parser.attributeSetContains("recursive", attributes) || Parser.attributeSetContains("recursive?", attributes)) {
            recursive = Parser.attributeSetContains("recursive", attributes) ? "yes" : "cond";
        }

        const ikind = attributes.includes("dynamic") ? InvokableKind.DynamicOperator : InvokableKind.StaticOperator;
        const sig = this.parseInvokableCommon(ikind, Parser.attributeSetContains("abstract", attributes), attributes, recursive, [], termRestrictions);

        if (allMemberNames.has(fname)) {
            this.raiseError(this.getCurrentLine(), "Collision between static and other names");
        }
        allMemberNames.add(fname);

        staticOperators.push(new StaticOperatorDecl(sinfo, this.m_penv.getCurrentFile(), fname, sig));
    }

    private parseMemberField(memberFields: MemberFieldDecl[], allMemberNames: Set<string>, attributes: string[]) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] field NAME: T = exp;
        this.ensureAndConsumeToken("field");

        this.ensureToken(TokenStrings.Identifier);
        const fname = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(":");
        const stype = this.parseTypeSignature();
        let value: ConstantExpressionValue | undefined = undefined;

        if (this.testAndConsumeTokenIf("=")) {
            value = this.parseConstExpression(true);
        }

        this.ensureAndConsumeToken(";");

        if (allMemberNames.has(fname)) {
            this.raiseError(this.getCurrentLine(), "Collision between const and other names");
        }

        memberFields.push(new MemberFieldDecl(sinfo, this.m_penv.getCurrentFile(), attributes, fname, stype, value));
    }

    private parseMemberMethod(thisRef: "ref" | undefined, thisType: TypeSignature, memberMethods: MemberMethodDecl[], allMemberNames: Set<string>, attributes: string[]) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] [ref] method NAME<T where C...>(params): type [requires...] [ensures...] { ... }
        const refrcvr = this.testAndConsumeTokenIf("ref");
        this.ensureAndConsumeToken("method");
        const termRestrictions = this.parseTermRestriction(true);

        this.ensureToken(TokenStrings.Identifier);
        const mname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        let recursive: "yes" | "no" | "cond" = "no";
        if (Parser.attributeSetContains("recursive", attributes) || Parser.attributeSetContains("recursive?", attributes)) {
            recursive = Parser.attributeSetContains("recursive", attributes) ? "yes" : "cond";
        }
        const sig = this.parseInvokableCommon(InvokableKind.Member, Parser.attributeSetContains("abstract", attributes), attributes, recursive, terms, termRestrictions, thisRef, thisType);

        allMemberNames.add(mname);

        memberMethods.push(new MemberMethodDecl(sinfo, this.m_penv.getCurrentFile(), mname, refrcvr, sig));
    }

    private parseInvariantsInto(invs: InvariantDecl[], vdates: ValidateDecl[]) {
        try {
            this.m_penv.pushFunctionScope(new FunctionScope(new Set<string>(), new NominalTypeSignature("Core", ["Bool"]), false));
            while (this.testToken("invariant") || this.testToken("validate")) {
                if(this.testToken("validate")) {
                    this.consumeToken();

                    const sinfo = this.getCurrentSrcInfo();
                    const exp = this.parseConstExpression(true);

                    vdates.push(new ValidateDecl(sinfo, exp));
                }
                else {
                    this.consumeToken();

                    const level = this.parseBuildInfo("release");
                    const sinfo = this.getCurrentSrcInfo();
                    const exp = this.parseConstExpression(true);

                    invs.push(new InvariantDecl(sinfo, level, exp));
                }

                this.ensureAndConsumeToken(";");
            }
        } finally {
            this.m_penv.popFunctionScope();
        }
    }

    private parseOOPMembersCommon(thisType: TypeSignature, currentNamespace: NamespaceDeclaration, currentTypeNest: string[], currentTermNest: TemplateTermDecl[], 
        nestedEntities: Map<string, EntityTypeDecl>, invariants: InvariantDecl[], validates: ValidateDecl[],
        staticMembers: StaticMemberDecl[], staticFunctions: StaticFunctionDecl[], staticOperators: StaticOperatorDecl[], 
        memberFields: MemberFieldDecl[], memberMethods: MemberMethodDecl[]) {
        let allMemberNames = new Set<string>();
        while (!this.testToken("}")) {
            const attributes = this.parseAttributes();

            if(this.testToken("entity")) {
                this.parseObject(currentNamespace, nestedEntities, currentTypeNest, currentTermNest);
            }
            else if (this.testToken("invariant") || this.testToken("validate")) {
                this.parseInvariantsInto(invariants, validates);
            }
            else if (this.testToken("const")) {
                this.parseConstMember(staticMembers, allMemberNames, attributes);
            }
            else if (this.testToken("function")) {
                this.parseStaticFunction(staticFunctions, allMemberNames, attributes);
            }
            else if (this.testToken("operator")) {
                this.parseStaticOperator(staticOperators, allMemberNames, attributes);
            }
            else if (this.testToken("field")) {
                this.parseMemberField(memberFields, allMemberNames, attributes);
            }
            else {
                this.ensureToken("method");

                const thisRef = attributes.find((attr) => attr === "ref") as "ref" | undefined;
                this.parseMemberMethod(thisRef, thisType, memberMethods, allMemberNames, attributes);
            }
        }
    }

    private parseConcept(currentDecl: NamespaceDeclaration) {
        const line = this.getCurrentLine();

        //[attr] concept NAME[T where C...] provides {...}
        const attributes = this.parseAttributes();

        const sinfo = this.getCurrentSrcInfo();
        this.ensureAndConsumeToken("concept");
        this.ensureToken(TokenStrings.Type);

        const cname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        const provides = this.parseProvides(currentDecl.ns === "Core", ["{"]);

        try {
            this.setRecover(this.scanCodeParens());
            this.ensureAndConsumeToken("{");

            const thisType = new NominalTypeSignature(currentDecl.ns, [cname], terms.map((term) => new TemplateTypeSignature(term.name)));

            const invariants: InvariantDecl[] = [];
            const validates: ValidateDecl[] = [];
            const staticMembers: StaticMemberDecl[] = [];
            const staticFunctions: StaticFunctionDecl[] = [];
            const staticOperators: StaticOperatorDecl[] = [];
            const memberFields: MemberFieldDecl[] = [];
            const memberMethods: MemberMethodDecl[] = [];
            const nestedEntities = new Map<string, EntityTypeDecl>();
            this.parseOOPMembersCommon(thisType, currentDecl, [cname], [...terms], nestedEntities, invariants, validates, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods);

            this.ensureAndConsumeToken("}");

            if (currentDecl.checkDeclNameClash(currentDecl.ns, cname)) {
                this.raiseError(line, "Collision between concept and other names");
            }

            this.clearRecover();

            if(currentDecl.ns === "Core") {
                if(cname === "Result") {
                    attributes.push("__result_type");
                }
                else if(cname === "Option") {
                    attributes.push("__option_type");
                }
                else {
                    //not special
                }
            }

            const cdecl = new ConceptTypeDecl(sinfo, this.m_penv.getCurrentFile(), attributes, currentDecl.ns, cname, terms, provides, invariants, validates, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods, nestedEntities);
            currentDecl.concepts.set(cname, cdecl);
            this.m_penv.assembly.addConceptDecl((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + cname, cdecl);
        }
        catch (ex) {
            this.processRecover();
        }
    }

    private parseObject(currentDecl: NamespaceDeclaration, enclosingMap: Map<string, EntityTypeDecl> | undefined, currentTypeNest: string[], currentTermNest: TemplateTermDecl[]) {
        const line = this.getCurrentLine();

        //[attr] object NAME[T where C...] provides {...}
        const attributes = this.parseAttributes();

        const sinfo = this.getCurrentSrcInfo();
        this.ensureAndConsumeToken("entity");
        this.ensureToken(TokenStrings.Type);

        const ename = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        const provides = this.parseProvides(currentDecl.ns === "Core", ["{"]);

        try {
            this.setRecover(this.scanCodeParens());
            this.ensureAndConsumeToken("{");

            const thisType = new NominalTypeSignature(currentDecl.ns, [...currentTypeNest, ename], [...terms, ...currentTermNest].map((term) => new TemplateTypeSignature(term.name)));

            const invariants: InvariantDecl[] = [];
            const validates: ValidateDecl[] = [];
            const staticMembers: StaticMemberDecl[] = [];
            const staticFunctions: StaticFunctionDecl[] = [];
            const staticOperators: StaticOperatorDecl[] = [];
            const memberFields: MemberFieldDecl[] = [];
            const memberMethods: MemberMethodDecl[] = [];
            const nestedEntities = new Map<string, EntityTypeDecl>();
            this.parseOOPMembersCommon(thisType, currentDecl, [...currentTypeNest, ename], [...currentTermNest, ...terms], nestedEntities, invariants, validates, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods);

            this.ensureAndConsumeToken("}");

            if (currentDecl.checkDeclNameClash(currentDecl.ns, [...currentTypeNest, ename].join("::"))) {
                this.raiseError(line, "Collision between object and other names");
            }

            if(currentDecl.ns === "Core") {
                if(ename === "StringOf") {
                    attributes.push("__stringof_type");
                }
                else if(ename === "DataString") {
                    attributes.push("__datastring_type");
                }
                else if(ename === "DataBuffer") {
                    attributes.push("__databuffer_type");
                }
                else if(ename === "Ok") {
                    attributes.push("__ok_type");
                }
                else if(ename === "Err") {
                    attributes.push("__err_type");
                }
                else if(ename === "Nothing") {
                    attributes.push("__nothing_type");
                }
                else if(ename === "Something") {
                    attributes.push("__something_type");
                }
                else if(ename === "HavocSequence") {
                    attributes.push("__havoc_type");
                }
                else if(ename === "List") {
                    attributes.push("__list_type");
                }
                else if(ename === "Stack") {
                    attributes.push("__stack_type");
                }
                else if(ename === "Queue") {
                    attributes.push("__queue_type");
                }
                else if(ename === "Set") {
                    attributes.push("__set_type");
                }
                else if(ename === "Map") {
                    attributes.push("__map_type");
                }
                else if(ename === "SeqList") {
                    attributes.push("__seqlist_type");
                }
                else if(ename === "SeqMap") {
                    attributes.push("__seqmap_type");
                }
                else {
                    //not special
                }
            }

            this.clearRecover();

            const fename = [...currentTypeNest, ename].join("::");
            const feterms = [...currentTermNest, ...terms];

            const edecl = new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), attributes, currentDecl.ns, fename, feterms, provides, invariants, validates, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods, nestedEntities);
            this.m_penv.assembly.addObjectDecl((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + fename, edecl);
            currentDecl.objects.set(ename, edecl);
            
            if(enclosingMap !== undefined) {
                enclosingMap.set(ename, edecl);
            }
        }
        catch (ex) {
            this.processRecover();
        }
    }

    private parseEnum(currentDecl: NamespaceDeclaration) {
        const line = this.getCurrentLine();

        //[attr] enum NAME {...} [& {...}]
        const attributes = this.parseAttributes();

        const sinfo = this.getCurrentSrcInfo();

        const sfpos = this.sortedSrcFiles.findIndex((entry) => entry.fullname === this.m_penv.getCurrentFile());
        if(sfpos === -1) {
            this.raiseError(sinfo.line, "Source name not registered");
        }   

        this.ensureAndConsumeToken("enum");
        this.ensureToken(TokenStrings.Type);

        const ename = this.consumeTokenAndGetValue();
        const etype = new NominalTypeSignature(currentDecl.ns, [ename]);
        
        if (currentDecl.checkDeclNameClash(currentDecl.ns, ename)) {
            this.raiseError(line, "Collision between object and other names");
        }

        try {
            this.setRecover(this.scanCodeParens());

            const enums = this.parseListOf<string>("{", "}", ",", () => {
                this.ensureToken(TokenStrings.Identifier);
                return this.consumeTokenAndGetValue();
            })[0];
            
            const provides = [
                [new NominalTypeSignature("Core", ["Some"]), undefined],
                [new NominalTypeSignature("Core", ["KeyType"]), undefined], 
                [new NominalTypeSignature("Core", ["APIType"]), undefined]
            ] as [TypeSignature, TypeConditionRestriction | undefined][];

            const invariants: InvariantDecl[] = [];
            const validates: ValidateDecl[] = [];
            const staticMembers: StaticMemberDecl[] = [];
            const staticFunctions: StaticFunctionDecl[] = [];
            const staticOperators: StaticOperatorDecl[] = [];
            const memberFields: MemberFieldDecl[] = [];
            const memberMethods: MemberMethodDecl[] = [];
    
            for(let i = 0; i < enums.length; ++i) {
                const exp = new LiteralIntegralExpression(sinfo, i.toString() + "n", this.m_penv.SpecialNatSignature);
                const enminit = new ConstructorPrimaryExpression(sinfo, etype, new Arguments([new PositionalArgument(undefined, false, exp)]));
                const enm = new StaticMemberDecl(sinfo, this.m_penv.getCurrentFile(), ["__enum"], enums[i], etype, new ConstantExpressionValue(enminit, new Set<string>()));
                staticMembers.push(enm);
            }

            if(this.testAndConsumeTokenIf("&")) {
                this.setRecover(this.scanCodeParens());
                this.ensureAndConsumeToken("{");
    
                const thisType = new NominalTypeSignature(currentDecl.ns, [ename], []);
    
                const nestedEntities = new Map<string, EntityTypeDecl>();
                this.parseOOPMembersCommon(thisType, currentDecl, [ename], [], nestedEntities, invariants, validates, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods);
    
                this.ensureAndConsumeToken("}");
    
                this.clearRecover();
            }

            if (currentDecl.checkDeclNameClash(currentDecl.ns, ename)) {
                this.raiseError(line, "Collision between object and other names");
            }

            if(invariants.length !== 0) {
                this.raiseError(line, "Cannot have invariant function on Enum types");
            }

            attributes.push("__enum_type", "__constructable");

            this.clearRecover();
            currentDecl.objects.set(ename, new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), attributes, currentDecl.ns, ename, [], provides, invariants, validates, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods, new Map<string, EntityTypeDecl>()));
            this.m_penv.assembly.addObjectDecl((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + ename, currentDecl.objects.get(ename) as EntityTypeDecl);
        }
        catch (ex) {
            this.processRecover();
        }
    }

    private parseTypeDecl(currentDecl: NamespaceDeclaration) {
        const line = this.getCurrentLine();
        const attributes = this.parseAttributes();

        const sinfo = this.getCurrentSrcInfo();
       
        this.ensureAndConsumeToken("typedecl");

        const iname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        if (currentDecl.checkDeclNameClash(currentDecl.ns, iname)) {
            this.raiseError(line, "Collision between object and other names");
        }

        const sfpos = this.sortedSrcFiles.findIndex((entry) => entry.fullname === this.m_penv.getCurrentFile());
        if(sfpos === -1) {
            this.raiseError(sinfo.line, "Source name not registered");
        }
        
        const bodyid = `k${sfpos}#${this.sortedSrcFiles[sfpos].shortname}::${sinfo.line}@${sinfo.pos}`;

        this.ensureAndConsumeToken("=");
        if (this.testToken(TokenStrings.Regex)) {
            //[attr] typedecl NAME = regex;
            if (terms.length !== 0) {
                this.raiseError(line, "Cannot have template terms on Validator type");
            }

            const vregex = this.consumeTokenAndGetValue();
            this.consumeToken();

            const re = BSQRegex.parse(this.m_penv.getCurrentNamespace(), vregex);
            if (typeof (re) === "string") {
                this.raiseError(this.getCurrentLine(), re);
            }

            const validator = new StaticMemberDecl(sinfo, this.m_penv.getCurrentFile(), [], "vregex", new NominalTypeSignature("Core", ["Regex"]), new ConstantExpressionValue(new LiteralRegexExpression(sinfo, re as BSQRegex), new Set<string>()));
            const param = new FunctionParameter("arg", new NominalTypeSignature("Core", ["String"]), false, undefined, undefined, undefined);

            const acceptsid = this.generateBodyID(sinfo, this.m_penv.getCurrentFile(), "accepts");
            const acceptsbody = new BodyImplementation(`${this.m_penv.getCurrentFile()}::${sinfo.pos}`, this.m_penv.getCurrentFile(), "validator_accepts");
            const acceptsinvoke = new InvokeDecl("Core", sinfo, sinfo, acceptsid, this.m_penv.getCurrentFile(), ["__safe"], "no", [], undefined, [param], undefined, undefined, new NominalTypeSignature("Core", ["Bool"]), [], [], false, false, new Set<string>(), acceptsbody);
            const accepts = new StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), "accepts", acceptsinvoke);
            const provides = [[new NominalTypeSignature("Core", ["Some"]), undefined], [new NominalTypeSignature("Core", ["Validator"]), undefined]] as [TypeSignature, TypeConditionRestriction | undefined][];
            const validatortype = new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), ["__validator_type", ...attributes], currentDecl.ns, iname, [], provides, [], [], [validator], [accepts], [], [], [], new Map<string, EntityTypeDecl>());

            currentDecl.objects.set(iname, validatortype);
            this.m_penv.assembly.addObjectDecl((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + iname, currentDecl.objects.get(iname) as EntityTypeDecl);
            this.m_penv.assembly.addValidatorRegex((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + iname, re as BSQRegex);
        }
        else {
            //[attr] typedecl NAME = PRIMITIVE [& {...}];

            if (terms.length !== 0) {
                this.raiseError(line, "Cannot have template terms on Typed Primitive type");
            }
            const idval = this.parseNominalType() as NominalTypeSignature;

            let provides = [[new NominalTypeSignature("Core", ["Some"]), undefined], [new NominalTypeSignature("Core", ["APIType"]), undefined]] as [TypeSignature, TypeConditionRestriction | undefined][];
            provides.push([new NominalTypeSignature("Core", ["KeyType"]), new TypeConditionRestriction([new TemplateTypeRestriction(idval, false, false, new NominalTypeSignature("Core", ["KeyType"]))])]);

            const invariants: InvariantDecl[] = [];
            const validates: ValidateDecl[] = [];
            const staticMembers: StaticMemberDecl[] = [];
            const staticFunctions: StaticFunctionDecl[] = [];
            const staticOperators: StaticOperatorDecl[] = [];
            const memberFields: MemberFieldDecl[] = [];
            const memberMethods: MemberMethodDecl[] = [];

            let implicitops: string[][] = [];

            const ttname = idval.tnames[0];
            if(ttname === "Int" || ttname === "Nat" || ttname === "BigInt" || ttname === "BigNat" || ttname === "Float" || ttname === "Decimal" || ttname === "Rational") {
                implicitops = [["t", "==", "t", "Bool"], ["t", "!=", "t", "Bool"]];

                if (attributes.includes("orderable")) {
                    provides.push([new NominalTypeSignature("Core", ["Orderable"]), undefined]);

                    implicitops = [...implicitops, ["t", "<", "t", "Bool"], ["t", ">", "t", "Bool"], ["t", "<=", "t", "Bool"], ["t", ">=", "t", "Bool"]];
                }

                if (attributes.includes("algebraic")) {
                    provides.push([new NominalTypeSignature("Core", ["Algebraic"]), undefined]);

                    implicitops = [...implicitops, ["+", "t", "t"], ["t", "+", "t", "t"], ["-", "t", "t"], ["t", "-", "t", "t"], ["t", "*", "u", "t"], ["u", "*", "t", "t"], ["t", "/", "t", "u"], ["t", "/", "u", "t"]];
                }

                ["zero", "one"].forEach((sf) => {
                    const ttype = new NominalTypeSignature(currentDecl.ns, [iname], []);

                    const cexp = new ConstructorPrimaryExpression(sinfo, ttype, new Arguments([new PositionalArgument(undefined, false, new AccessStaticFieldExpression(sinfo, idval, sf))]));
                    const sfdecl = new StaticMemberDecl(sinfo, this.m_penv.getCurrentFile(), [], sf, ttype, new ConstantExpressionValue(cexp, new Set<string>()));

                    staticMembers.push(sfdecl);
                });
            }
            else if(ttname === "StringOf") {
                //TODO: what operations do we want to forward by default (or config)
            }
            else if(ttname === "DataString") {
                //TODO: what operations do we want to forward by default (or config)
            }
            else if(ttname === "DateTime") {
                //TODO: what operations do we want to forward by default (or config)
            }
            else if(ttname === "UTCDateTime") {
                //TODO: what operations do we want to forward by default (or config)
            }
            else if(ttname === "CalendarDate") {
                //TODO: what operations do we want to forward by default (or config)
            }
            else if(ttname === "TickTime") {
                //TODO: what operations do we want to forward by default (or config)
            }
            else if(ttname === "LogicalTime") {
                //TODO: what operations do we want to forward by default (or config)
            }
            else if(ttname === "ISOTimeStamp") {
                //TODO: what operations do we want to forward by default (or config)
            }
            else if(ttname === "UUID4") {
                //TODO: what operations do we want to forward by default (or config)
            }
            else if(ttname === "UUID7") {
                //TODO: what operations do we want to forward by default (or config)
            }
            else if(ttname === "SHAContentHash") {
                //TODO: what operations do we want to forward by default (or config)
            }
            else {
                //must be geo-coordinate
                
                //TODO: what operations do we want to forward by default (or config)
            }

            implicitops.forEach((op) => {
                const ns = this.m_penv.assembly.getNamespace("Core");

                const isprefix = op[0] !== "t" && op[0] !== "u";
                const opstr = isprefix ? op[0] : op[1];

                const ttype = new NominalTypeSignature(currentDecl.ns, [iname], []);

                let params: FunctionParameter[] = [];
                let bexp: Expression = new LiteralNoneExpression(sinfo);

                if (isprefix) {
                    const ptype = op[1] === "t" ? ttype : idval;
                    params = [new FunctionParameter("l", ptype, false, undefined, undefined, undefined)];
                    const laccess = new AccessVariableExpression(sinfo, "l");
                    const aexp = (op[1] === "t") ?
                        new PostfixOp(sinfo, laccess, [new PostfixInvoke(sinfo, false, undefined, "value", new TemplateArguments([]), "no", new Arguments([]))])
                        : laccess;

                    bexp = new CallNamespaceFunctionOrOperatorExpression(sinfo, "Core", op[0], new TemplateArguments([]), "no", new Arguments([new PositionalArgument(undefined, false, aexp)]), "prefix");
                }
                else {
                    const lptype = op[0] === "t" ? ttype : idval;
                    const rptype = op[2] === "t" ? ttype : idval;
                    params = [new FunctionParameter("l", lptype, false, undefined, undefined, undefined), new FunctionParameter("r", rptype, false, undefined, undefined, undefined)];

                    const laccess = new AccessVariableExpression(sinfo, "l");
                    const lexp = (op[0] === "t") ?
                        new PostfixOp(sinfo, laccess, [new PostfixInvoke(sinfo, false, undefined, "value", new TemplateArguments([]), "no", new Arguments([]))])
                        : laccess;

                    const raccess = new AccessVariableExpression(sinfo, "r");
                    const rexp = (op[2] === "t") ?
                        new PostfixOp(sinfo, raccess, [new PostfixInvoke(sinfo, false, undefined, "value", new TemplateArguments([]), "no", new Arguments([]))])
                        : raccess;

                    bexp = new CallNamespaceFunctionOrOperatorExpression(sinfo, "Core", op[1], new TemplateArguments([]), "no", new Arguments([new PositionalArgument(undefined, false, lexp), new PositionalArgument(undefined, false, rexp)]), "infix");
                }

                let resultType: TypeSignature = new NominalTypeSignature("Core", ["Bool"]);
                const resstr = op[op.length - 1];
                if (resstr === "t") {
                    resultType = ttype;
                }
                else if (resstr === "u") {
                    resultType = idval;
                }
                else {
                    //already set to bool
                }

                if (resstr === "t") {
                    bexp = new ConstructorPrimaryExpression(sinfo, ttype, new Arguments([new PositionalArgument(undefined, false, bexp)]));
                }

                const bodyid = this.generateBodyID(sinfo, this.m_penv.getCurrentFile(), opstr);
                const body = new BodyImplementation(bodyid, this.m_penv.getCurrentFile(), new BlockStatement(sinfo, [new ReturnStatement(sinfo, [bexp])]));
                const sig = InvokeDecl.createStandardInvokeDecl("Core", sinfo, sinfo, bodyid, this.m_penv.getCurrentFile(), [isprefix ? "prefix" : "infix"], "no", [], undefined, params, undefined, undefined, resultType, [], [], body);


                if (!ns.operators.has(opstr)) {
                    ns.operators.set(opstr, []);
                }
                (ns.operators.get(opstr) as NamespaceOperatorDecl[]).push(new NamespaceOperatorDecl(sinfo, this.m_penv.getCurrentFile(), "Core", opstr, sig));
            });

            if (this.testAndConsumeTokenIf("&")) {
                this.setRecover(this.scanCodeParens());
                this.ensureAndConsumeToken("{");

                const thisType = new NominalTypeSignature(currentDecl.ns, [iname], []);

                const nestedEntities = new Map<string, EntityTypeDecl>();
                this.parseOOPMembersCommon(thisType, currentDecl, [iname], [], nestedEntities, invariants, validates, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods);

                this.ensureAndConsumeToken("}");

                if (currentDecl.checkDeclNameClash(currentDecl.ns, iname)) {
                    this.raiseError(line, "Collision between concept and other names");
                }

                this.clearRecover();
            }
            else {
                this.ensureAndConsumeToken(";");
            }

            const vparam = new FunctionParameter("v", idval, false, undefined, undefined, undefined);

            const valueid = this.generateBodyID(sinfo, this.m_penv.getCurrentFile(), "value");
            const valuebody = new BodyImplementation(`${bodyid}_value`, this.m_penv.getCurrentFile(), "special_extract");
            const valuedecl = new InvokeDecl("Core", sinfo, sinfo, valueid, this.m_penv.getCurrentFile(), ["__safe"], "no", [], undefined, [vparam], undefined, undefined, idval, [], [], false, false, new Set<string>(), valuebody);
            const value = new MemberMethodDecl(sinfo, this.m_penv.getCurrentFile(), "value", false, valuedecl);

            memberMethods.push(value);

            attributes.push("__typedprimitive", "__constructable");

            currentDecl.objects.set(iname, new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), attributes, currentDecl.ns, iname, [], provides, invariants, validates, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods, new Map<string, EntityTypeDecl>()));
            this.m_penv.assembly.addObjectDecl((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + iname, currentDecl.objects.get(iname) as EntityTypeDecl);
        }
    }

    private parseDataTypeDecl(currentDecl: NamespaceDeclaration) {
        const line = this.getCurrentLine();
        const sinfo = this.getCurrentSrcInfo();
       
        this.ensureAndConsumeToken("datatype");

        const iname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        if (currentDecl.checkDeclNameClash(currentDecl.ns, iname)) {
            this.raiseError(line, "Collision between object and other names");
        }

        const sfpos = this.sortedSrcFiles.findIndex((entry) => entry.fullname === this.m_penv.getCurrentFile());
        if (sfpos === -1) {
            this.raiseError(sinfo.line, "Source name not registered");
        }

        //[attr] typedecl NAME<...> [provides ... ] [using {...}] of
        // Foo {...}
        // | ...
        // [& {...}] | ;

        const concepttype = new NominalTypeSignature(currentDecl.ns, [iname]);

        const provides = this.parseProvides(currentDecl.ns === "Core", ["of", "using"]);

        let complexheader = false;
        const cinvariants: InvariantDecl[] = [];
        const cvalidates: ValidateDecl[] = [];
        const cstaticMembers: StaticMemberDecl[] = [];
        const cstaticFunctions: StaticFunctionDecl[] = [];
        const cstaticOperators: StaticOperatorDecl[] = [];
        let cusing: MemberFieldDecl[] = [];
        const cmemberMethods: MemberMethodDecl[] = [];
        if (this.testAndConsumeTokenIf("using")) {
            if (this.testFollows("{", TokenStrings.Identifier) && !Lexer.isAttributeKW(this.peekTokenData(1))) {
                cusing = this.parseListOf<MemberFieldDecl>("{", "}", ",", () => {
                    const mfinfo = this.getCurrentSrcInfo();

                    this.ensureToken(TokenStrings.Identifier);
                    const name = this.consumeTokenAndGetValue();
                    this.ensureAndConsumeToken(":");

                    const ttype = this.parseTypeSignature();

                    let dvalue: ConstantExpressionValue | undefined = undefined;
                    if (this.testAndConsumeTokenIf("=")) {
                        dvalue = this.parseConstExpression(false);
                    }

                    return new MemberFieldDecl(mfinfo, this.m_penv.getCurrentFile(), [], name, ttype, dvalue);
                })[0];
            }
            else {
                complexheader = true;
                const thisType = new NominalTypeSignature(currentDecl.ns, [iname], []);

                const nestedEntities = new Map<string, EntityTypeDecl>();
                this.parseOOPMembersCommon(thisType, currentDecl, [iname], [], nestedEntities, cinvariants, cvalidates, cstaticMembers, cstaticFunctions, cstaticOperators, cusing, cmemberMethods);
            }
        }

        this.ensureAndConsumeToken("of");

        const edecls: EntityTypeDecl[] = [];
        while (!this.testToken(";") && !this.testToken("&")) {
            if (this.testToken("|")) {
                this.consumeToken();
            }
            let esinfo = this.getCurrentSrcInfo();

            this.ensureToken(TokenStrings.Type);
            const ename = this.consumeTokenAndGetValue();
            if (currentDecl.checkDeclNameClash(currentDecl.ns, ename)) {
                this.raiseError(line, "Collision between object and other names");
            }

            const invariants: InvariantDecl[] = [];
            const validates: ValidateDecl[] = [];
            const staticMembers: StaticMemberDecl[] = [];
            const staticFunctions: StaticFunctionDecl[] = [];
            const staticOperators: StaticOperatorDecl[] = [];
            let memberFields: MemberFieldDecl[] = [];
            const memberMethods: MemberMethodDecl[] = [];
            if (this.testToken("{")) {
                if (this.testFollows("{", TokenStrings.Identifier) && !Lexer.isAttributeKW(this.peekTokenData(1))) {
                    memberFields = this.parseListOf<MemberFieldDecl>("{", "}", ",", () => {
                        const mfinfo = this.getCurrentSrcInfo();

                        this.ensureToken(TokenStrings.Identifier);
                        const name = this.consumeTokenAndGetValue();
                        this.ensureAndConsumeToken(":");

                        const ttype = this.parseTypeSignature();

                        let dvalue: ConstantExpressionValue | undefined = undefined;
                        if (this.testAndConsumeTokenIf("=")) {
                            dvalue = this.parseConstExpression(false);
                        }

                        return new MemberFieldDecl(mfinfo, this.m_penv.getCurrentFile(), [], name, ttype, dvalue);
                    })[0];
                }
                else {
                    const thisType = new NominalTypeSignature(currentDecl.ns, [ename], []);

                    const nestedEntities = new Map<string, EntityTypeDecl>();
                    this.parseOOPMembersCommon(thisType, currentDecl, [ename], [], nestedEntities, invariants, validates, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods);
                }
            }

            const eprovides = [[concepttype, undefined]] as [TypeSignature, TypeConditionRestriction | undefined][];
            const edecl = new EntityTypeDecl(esinfo, this.m_penv.getCurrentFile(), ["__adt_entity_type"], currentDecl.ns, ename, terms, eprovides, invariants, validates, staticMembers, staticFunctions, staticOperators, memberFields, memberMethods, new Map<string, EntityTypeDecl>());

            edecls.push(edecl);
            currentDecl.objects.set(ename, edecl);
            this.m_penv.assembly.addObjectDecl((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + ename, currentDecl.objects.get(ename) as EntityTypeDecl);
        }

        if (this.testAndConsumeTokenIf("&")) {
            this.setRecover(this.scanCodeParens());
            this.ensureAndConsumeToken("{");

            if (complexheader) {
                this.raiseError(this.getCurrentLine(), "Cannot define complex ADT++ concept in multiple parts");
            }

            const thisType = new NominalTypeSignature(currentDecl.ns, [iname], []);

            const nestedEntities = new Map<string, EntityTypeDecl>();
            const memberFields: MemberFieldDecl[] = [];
            this.parseOOPMembersCommon(thisType, currentDecl, [iname], [], nestedEntities, cinvariants, cvalidates, cstaticMembers, cstaticFunctions, cstaticOperators, memberFields, cmemberMethods);

            if (cusing.length !== 0 && memberFields.length !== 0) {
                this.raiseError(this.getCurrentLine(), "Cannot define fields in multiple places in ADT++ decl");
            }
            cusing = [...cusing, ...memberFields];

            this.ensureAndConsumeToken("}");

            if (currentDecl.checkDeclNameClash(currentDecl.ns, iname)) {
                this.raiseError(line, "Collision between concept and other names");
            }

            this.clearRecover();
        }
        else {
            this.ensureAndConsumeToken(";");
        }

        const cdecl = new ConceptTypeDecl(sinfo, this.m_penv.getCurrentFile(), ["__adt_concept_type"], currentDecl.ns, iname, terms, provides, cinvariants, cvalidates, cstaticMembers, cstaticFunctions, cstaticOperators, cusing, cmemberMethods, new Map<string, EntityTypeDecl>());
        currentDecl.concepts.set(iname, cdecl);
        this.m_penv.assembly.addConceptDecl((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + iname, cdecl);
    }

    private parseNamespaceConst(currentDecl: NamespaceDeclaration) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] const NAME = exp;
        const attributes = this.parseAttributes();

        this.ensureAndConsumeToken("const");
        this.ensureToken(TokenStrings.Identifier);
        const gname = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(":");
        const gtype = this.parseTypeSignature();

        this.ensureAndConsumeToken("=");
        const value = this.parseConstExpression(false);

        this.ensureAndConsumeToken(";");

        if (currentDecl.checkDeclNameClash(currentDecl.ns, gname)) {
            this.raiseError(this.getCurrentLine(), "Collision between global and other names");
        }

        currentDecl.consts.set(gname, new NamespaceConstDecl(sinfo, this.m_penv.getCurrentFile(), attributes, currentDecl.ns, gname, gtype, value));
    }

    private parseNamespaceFunction(currentDecl: NamespaceDeclaration) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] function NAME<T where C...>(params): type [requires...] [ensures...] { ... }
        const attributes = this.parseAttributes();

        this.ensureAndConsumeToken("function");
        this.ensureToken(TokenStrings.Identifier);
        const fname = this.consumeTokenAndGetValue();

        const terms = this.parseTermDeclarations();
        let recursive: "yes" | "no" | "cond" = "no";
        if (Parser.attributeSetContains("recursive", attributes) || Parser.attributeSetContains("recursive?", attributes)) {
            recursive = Parser.attributeSetContains("recursive", attributes) ? "yes" : "cond";
        }
        const sig = this.parseInvokableCommon(InvokableKind.Basic, false, attributes, recursive, terms, undefined);

        currentDecl.functions.set(fname, new NamespaceFunctionDecl(sinfo, this.m_penv.getCurrentFile(), currentDecl.ns, fname, sig));
    }

    private parseNamespaceOperator(currentDecl: NamespaceDeclaration) {
        const sinfo = this.getCurrentSrcInfo();

        //[attr] operator [NS ::] NAME(params): type [requires...] [ensures...] { ... }
        const attributes = this.parseAttributes();

        this.ensureAndConsumeToken("operator");
        if (this.testToken("+") || this.testToken("-") || this.testToken("*") || this.testToken("/") ||
            this.testToken("==") || this.testToken("!=") || this.testToken("<") || this.testToken(">") || this.testToken("<=") || this.testToken(">=")) {
            const fname = this.consumeTokenAndGetValue();

            let recursive: "yes" | "no" | "cond" = "no";
            if (Parser.attributeSetContains("recursive", attributes) || Parser.attributeSetContains("recursive?", attributes)) {
                recursive = Parser.attributeSetContains("recursive", attributes) ? "yes" : "cond";
            }

            const ns = this.m_penv.assembly.getNamespace("Core");
            const sig = this.parseInvokableCommon(InvokableKind.StaticOperator, attributes.includes("abstract"), attributes, recursive, [], undefined);

            if (!ns.operators.has(fname)) {
                ns.operators.set(fname, []);
            }
            (ns.operators.get(fname) as NamespaceOperatorDecl[]).push(new NamespaceOperatorDecl(sinfo, this.m_penv.getCurrentFile(), "Core", fname, sig));
        }
        else {
            if(!this.testToken(TokenStrings.Identifier) && !this.testToken(TokenStrings.Operator)) {
                this.raiseError(sinfo.line, "Expected valid name for operator");
            }

            const fname = this.consumeTokenAndGetValue();

            let recursive: "yes" | "no" | "cond" = "no";
            if (Parser.attributeSetContains("recursive", attributes) || Parser.attributeSetContains("recursive?", attributes)) {
                recursive = Parser.attributeSetContains("recursive", attributes) ? "yes" : "cond";
            }

            let ns = currentDecl;
            if(this.testToken(TokenStrings.Namespace)) {
                let nns: string | undefined = this.consumeTokenAndGetValue();
                this.ensureAndConsumeToken("::");

                nns = this.m_penv.tryResolveNamespace(nns, fname);
                if (nns === undefined) {
                    nns = "[Unresolved Error]";
                }

                ns = this.m_penv.assembly.getNamespace(nns);
            }

            const isabstract = OOPTypeDecl.attributeSetContains("abstract", attributes);
            const ikind = attributes.includes("dynamic") ? InvokableKind.DynamicOperator : InvokableKind.StaticOperator;
            const sig = this.parseInvokableCommon(ikind, isabstract, attributes, recursive, [], undefined);

            if (!ns.operators.has(fname)) {
                ns.operators.set(fname, []);
            }
            (ns.operators.get(fname) as NamespaceOperatorDecl[]).push(new NamespaceOperatorDecl(sinfo, this.m_penv.getCurrentFile(), ns.ns, fname, sig));
        }
    }

    private parseEndOfStream() {
        this.ensureAndConsumeToken(TokenStrings.EndOfStream);
    }

    ////
    //Public methods
    parseCompilationUnitGetNamespaceDeps(file: string, contents: string, macrodefs: string[]): {ns: string, deps: string[], remap: Map<string, string>} | undefined {
        this.setNamespaceAndFile("[No Namespace]", file);

        const lexer = new Lexer(contents, macrodefs, undefined);
        this.initialize(lexer.lex());

        //namespace NS; ...
        this.ensureAndConsumeToken("namespace");
        this.ensureToken(TokenStrings.ScopeName);
        const ns = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(";");

        this.setNamespaceAndFile(ns, file);

        let deps: string[] = [];
        let remap = new Map<string, string>();
        while (this.m_cpos < this.m_epos) {
            try {
                this.m_cpos = this.scanTokenOptions("import");
                if (this.m_cpos === this.m_epos) {
                    break;
                }

                const dep = this.parseNamespaceDep();
                deps.push(dep.fromns);
                remap.set(dep.asns, dep.fromns);
            }
            catch(ex) {
                return undefined;
            }
        }

        return {ns: ns, deps: deps, remap: remap};
    }

    parseCompilationUnitPass1(file: string, contents: string, macrodefs: string[]): boolean {
        this.setNamespaceAndFile("[No Namespace]", file);

        const lexer = new Lexer(contents, macrodefs, undefined);
        this.initialize(lexer.lex());

        //namespace NS; ...
        this.ensureAndConsumeToken("namespace");
        this.ensureToken(TokenStrings.ScopeName);
        const ns = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(";");

        this.setNamespaceAndFile(ns, file);
        const nsdecl = this.m_penv.assembly.ensureNamespace(ns);

        let parseok = true;
        while (this.m_cpos < this.m_epos) {
            try {
                this.m_cpos = this.scanTokenOptions("function", "operator", "const", "typedef", "concept", "entity", "enum", "typedecl", "datatype");
                if (this.m_cpos === this.m_epos) {
                    const tokenIndexBeforeEOF = this.m_cpos - 2;
                    if (tokenIndexBeforeEOF >= 0 && tokenIndexBeforeEOF < this.m_tokens.length) {
                        const tokenBeforeEOF = this.m_tokens[tokenIndexBeforeEOF];
                        if (tokenBeforeEOF.kind === TokenStrings.Error) {
                            this.raiseError(tokenBeforeEOF.line, `Expected */ but found EOF`);
                        }
                    }
                    break;
                }

                if (this.testToken("function")  || this.testToken("const")) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.Identifier);
                    const fname = this.consumeTokenAndGetValue();
                    if (nsdecl.declaredNames.has(fname)) {
                        this.raiseError(this.getCurrentLine(), "Duplicate definition of name");
                    }

                    nsdecl.declaredNames.add(fname);
                }
                else if (this.testToken("operator")) {
                    this.consumeToken();
                    if (this.testToken("+") || this.testToken("-") || this.testToken("*") || this.testToken("/")
                        || this.testToken("==") || this.testToken("!=") || this.testToken("<") || this.testToken(">") || this.testToken("<=") || this.testToken(">=")) {
                        const fname = this.consumeTokenAndGetValue();
                        
                        const nscore = this.m_penv.assembly.getNamespace("Core");
                        nscore.declaredNames.add(fname);
                    }
                    else {
                        let nns = ns;
                        if (this.testToken(TokenStrings.ScopeName)) {
                            nns = this.consumeTokenAndGetValue();
                            this.ensureAndConsumeToken("::");
                        }

                        const fname = this.consumeTokenAndGetValue();
                        
                        if (nns === ns) {
                            nsdecl.declaredNames.add(fname);
                        }
                    }
                }
                else if (this.testToken("typedef")) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.ScopeName);
                    const tname = this.consumeTokenAndGetValue();

                    if (!lexer.isDeclTypeName(tname)) {
                        this.raiseError(this.getCurrentLine(), "Not a valid type name to define");
                    }
                    if (nsdecl.declaredNames.has(tname)) {
                        this.raiseError(this.getCurrentLine(), "Duplicate definition of name");
                    }
                    nsdecl.declaredNames.add(tname);
                }
                else if (this.testToken("typedecl")) {            
                    this.consumeToken();

                    this.ensureToken(TokenStrings.ScopeName);
                    const tname = this.consumeTokenAndGetValue();

                    if (!lexer.isDeclTypeName(tname)) {
                        this.raiseError(this.getCurrentLine(), "Not a valid type name to define");
                    }
                    if (nsdecl.declaredNames.has(tname)) {
                        this.raiseError(this.getCurrentLine(), "Duplicate definition of name");
                    }
                    nsdecl.declaredNames.add(tname);

                    this.ensureAndConsumeToken("=");
                    if (this.testToken(TokenStrings.Regex)) {
                        this.consumeToken();
                        this.ensureAndConsumeToken(";");
                    }
                    else {
                        if (this.testAndConsumeTokenIf("&")) {
                            this.ensureToken("{"); //we should be at the opening left paren 
                            this.m_cpos = this.scanCodeParens(); //scan to the closing paren
                        }
                    }
                }
                else if (this.testToken("datatype")) {            
                    this.consumeToken();

                    this.ensureToken(TokenStrings.ScopeName);
                    const tname = this.consumeTokenAndGetValue();

                    if (!lexer.isDeclTypeName(tname)) {
                        this.raiseError(this.getCurrentLine(), "Not a valid type name to define");
                    }
                    if (nsdecl.declaredNames.has(tname)) {
                        this.raiseError(this.getCurrentLine(), "Duplicate definition of name");
                    }
                    nsdecl.declaredNames.add(tname);

                    //[attr] typedecl NAME<...> [provides ... ] [using {...}] of
                    // Foo {...}
                    // | ...
                    // [& {...}] | ;

                    this.parseProvides(false /*Doesn't matter since we arejust scanning*/, ["of", "using"]);

                    if (this.testAndConsumeTokenIf("using")) {
                        this.ensureToken("{"); //we should be at the opening left paren 
                        this.m_cpos = this.scanCodeParens(); //scan to the closing paren
                    }

                    this.ensureAndConsumeToken("of");

                    while (!this.testToken(";") && !this.testToken("&")) {
                        if (this.testToken("|")) {
                            this.consumeToken();
                        }

                        this.ensureToken(TokenStrings.ScopeName);
                        const ename = this.consumeTokenAndGetValue();

                        if (!lexer.isDeclTypeName(ename)) {
                            this.raiseError(this.getCurrentLine(), "Not a valid type name to define");
                        }
                        if (nsdecl.declaredNames.has(ename)) {
                            this.raiseError(this.getCurrentLine(), "Duplicate definition of name");
                        }
                        nsdecl.declaredNames.add(ename);

                        if (this.testToken("{")) {
                            this.m_cpos = this.scanCodeParens(); //scan to the closing paren
                        }
                    }

                    if (this.testAndConsumeTokenIf("&")) {
                        this.ensureToken("{"); //we should be at the opening left paren 
                        this.m_cpos = this.scanCodeParens(); //scan to the closing paren
                    }
                    else {
                        this.ensureAndConsumeToken(";");
                    }
                }
                else if (this.testToken("enum")) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.ScopeName);
                    const tname = this.consumeTokenAndGetValue();

                    if (!lexer.isDeclTypeName(tname)) {
                        this.raiseError(this.getCurrentLine(), "Not a valid type name to define");
                    }
                    if (nsdecl.declaredNames.has(tname)) {
                        this.raiseError(this.getCurrentLine(), "Duplicate definition of name");
                    }
                    nsdecl.declaredNames.add(tname);

                    this.ensureToken("{"); //we should be at the opening left paren 
                    this.m_cpos = this.scanCodeParens(); //scan to the closing paren

                    if (this.testToken("&")) {
                        this.ensureToken("{"); //we should be at the opening left paren 
                        this.m_cpos = this.scanCodeParens(); //scan to the closing paren
                    }
                }
                else if (this.testToken("concept") || this.testToken("entity")) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.ScopeName);
                    const tname = this.consumeTokenAndGetValue();

                    if (!lexer.isDeclTypeName(tname)) {
                        this.raiseError(this.getCurrentLine(), "Not a valid type name to define");
                    }
                    if (nsdecl.declaredNames.has(tname)) {
                        this.raiseError(this.getCurrentLine(), "Duplicate definition of name");
                    }
                    nsdecl.declaredNames.add(tname);

                    this.parseTermDeclarations();
                    this.parseProvides(ns === "Core", ["{"]);
            
                    this.ensureToken("{"); //we should be at the opening left paren 
                    this.m_cpos = this.scanCodeParens(); //scan to the closing paren
                }
                else {
                    this.raiseError(this.getCurrentLine(), "Failed to parse top-level namespace declaration");
                }
            }
            catch (ex) {
                this.m_cpos++;
                parseok = false;
            }
        }

        return parseok;
    }

    parseCompilationUnitPass2(file: string, contents: string, macrodefs: string[], namespacestrings: Set<string>): boolean {
        this.setNamespaceAndFile("[No Namespace]", file);
        const lexer = new Lexer(contents, macrodefs, namespacestrings);
        this.initialize(lexer.lex());

        //namespace NS; ...
        this.ensureAndConsumeToken("namespace");
        this.ensureToken(TokenStrings.Namespace);
        const ns = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(";");

        this.setNamespaceAndFile(ns, file);
        const nsdecl = this.m_penv.assembly.ensureNamespace(ns);

        let importok = true;
        let parseok = true;
        while (this.m_cpos < this.m_epos) {
            const rpos = this.scanTokenOptions("function", "operator", "const", "import", "typedef", "concept", "entity", "enum", "typedecl", "datatype", TokenStrings.EndOfStream);

            try {
                if (rpos === this.m_epos) {
                    break;
                }

                const tk = this.m_tokens[rpos].kind;
                importok = importok && tk === "import";
                if (tk === "import") {
                    if (!importok) {
                        this.raiseError(this.getCurrentLine(), "Using statements must come before other declarations");
                    }

                    this.parseNamespaceUsing(nsdecl);
                }
                else if (tk === "function") {
                    this.parseNamespaceFunction(nsdecl);
                }
                else if (tk === "operator") {
                    this.parseNamespaceOperator(nsdecl);
                }
                else if (tk === "const") {
                    this.parseNamespaceConst(nsdecl);
                }
                else if (tk === "typedef") {
                    this.parseNamespaceTypedef(nsdecl);
                }
                else if (tk === "concept") {
                    this.parseConcept(nsdecl);
                }
                else if (tk === "entity") {
                    this.parseObject(nsdecl, undefined, [], []);
                }
                else if (tk === "enum") {
                    this.parseEnum(nsdecl);
                }
                else if (tk === "typedecl") {
                    this.parseTypeDecl(nsdecl);
                }
                else if (tk === "datatype") {
                    this.parseDataTypeDecl(nsdecl);
                }
                else if (tk === TokenStrings.EndOfStream) {
                    this.parseEndOfStream();
                }
                else {
                    this.raiseError(this.getCurrentLine(), "Invalid top-level definiton");
                }
            }
            catch (ex) {
                this.m_cpos = rpos + 1;
                parseok = false;
            }
        }

        return parseok;
    }

    getParseErrors(): [string, number, string][] | undefined {
        return this.m_errors.length !== 0 ? this.m_errors : undefined;
    }
}

function cleanCommentsStringsFromFileContents(str: string): string {
    const commentRe = /(\/\/.*)|(\/\*(.|\s)*?\*\/)/ug;
    const stringRe = /"[^"\\\r\n]*(\\(.|\r?\n)[^"\\\r\n]*)*"/ug;
    const typedStringRe = /'[^'\\\r\n]*(\\(.|\r?\n)[^'\\\r\n]*)*'/ug;

    return str
        .replace(commentRe, "")
        .replace(stringRe, "\"\"")
        .replace(typedStringRe, "''");
}

export { 
    CodeFileInfo, SourceInfo, ParseError, Parser,
    unescapeLiteralString,
    cleanCommentsStringsFromFileContents
};
