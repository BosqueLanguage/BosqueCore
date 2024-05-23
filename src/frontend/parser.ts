
import {strict as assert} from "assert";

import { LocalVariableDefinitionInfo, ParserEnvironment, StandardScopeInfo } from "./parser_env";
import { AndTypeSignature, AutoTypeSignature, EListTypeSignature, ErrorTypeSignature, FullyQualifiedNamespace, FunctionParameter, LambdaTypeSignature, NominalTypeSignature, NoneableTypeSignature, RecordTypeSignature, RecursiveAnnotation, TemplateTypeSignature, TupleTypeSignature, TypeSignature, UnionTypeSignature } from "./type";
import { AbortStatement, AbstractBodyImplementation, AccessNamespaceConstantExpression, AccessVariableExpression, ArgumentList, ArgumentValue, AssertStatement, BinAddExpression, BinDivExpression, BinKeyEqExpression, BinKeyNeqExpression, BinLogicAndExpression, BinLogicIFFExpression, BinLogicImpliesExpression, BinLogicOrExpression, BinMultExpression, BinSubExpression, BinderInfo, BlockStatement, BodyImplementation, BuiltinBodyImplementation, ConstantExpressionValue, ConstructorEListExpression, ConstructorLambdaExpression, DebugStatement, EmptyStatement, ErrorExpression, ErrorStatement, Expression, ExpressionBodyImplementation, ExpressionTag, ITest, ITestErr, ITestLiteral, ITestNone, ITestNothing, ITestOk, ITestSome, ITestSomething, ITestType, IfElifElseStatement, IfElseStatement, IfExpression, IfStatement, IfTest, LiteralExpressionValue, LiteralPathExpression, LiteralRegexExpression, LiteralSimpleExpression, LiteralSingletonExpression, LiteralTemplateStringExpression, LiteralTypeDeclFloatPointValueExpression, LiteralTypeDeclIntegralValueExpression, LiteralTypeDeclValueExpression, LiteralTypedStringExpression, MapEntryConstructorExpression, MatchStatement, NamedArgumentValue, NumericEqExpression, NumericGreaterEqExpression, NumericGreaterExpression, NumericLessEqExpression, NumericLessExpression, NumericNeqExpression, PositionalArgumentValue, PostfixAsConvert, PostfixIsTest, PostfixOp, PostfixOperation, PredicateUFBodyImplementation, PrefixNegateOpExpression, PrefixNotOpExpression, RefArgumentValue, ReturnStatement, SpreadArgumentValue, StandardBodyImplementation, Statement, SwitchStatement, SynthesisBodyImplementation, ValidateStatement, VariableAssignmentStatement, VariableDeclarationStatement, VariableInitializationStatement, VariableMultiAssignmentStatement, VariableMultiDeclarationStatement, VariableMultiInitializationStatement, VariableRetypeStatement } from "./body";
import { APIResultTypeDecl, AbstractNominalTypeDecl, Assembly, ConstMemberDecl, DeclarationAttibute, FunctionInvokeDecl, InternalConceptTypeDecl, InvariantDecl, InvokeExample, InvokeExampleDeclFile, InvokeExampleDeclInline, InvokeTemplateTermDecl, InvokeTemplateTypeRestriction, InvokeTemplateTypeRestrictionClause, InvokeTemplateTypeRestrictionClauseSubtype, InvokeTemplateTypeRestrictionClauseUnify, LambdaDecl, MemberFieldDecl, MethodDecl, NamespaceDeclaration, NamespaceFunctionDecl, NamespaceTypedef, NamespaceUsing, PostConditionDecl, PreConditionDecl, ResultTypeDecl, TaskActionDecl, TaskMethodDecl, TypeFunctionDecl, TypeTemplateTermDecl, ValidateDecl } from "./assembly";
import { BuildLevel, SourceInfo } from "./build_decls";
import { AllAttributes, KW__debug, KW_abort, KW_action, KW_as, KW_assert, KW_chktest, KW_concept, KW_const, KW_debug, KW_elif, KW_else, KW_ensures, KW_entity, KW_err, KW_errtest, KW_example, KW_false, KW_field, KW_fn, KW_function, KW_if, KW_invariant, KW_let, KW_match, KW_method, KW_namespace, KW_none, KW_nothing, KW_ok, KW_pred, KW_predicate, KW_provides, KW_recursive, KW_recursive_q, KW_ref, KW_release, KW_requires, KW_return, KW_safety, KW_self, KW_some, KW_something, KW_spec, KW_switch, KW_test, KW_then, KW_this, KW_true, KW_type, KW_under, KW_using, KW_validate, KW_var, KW_when, KeywordStrings, LeftScanParens, ParenSymbols, RightScanParens, SYM_HOLE, SYM_amp, SYM_ampamp, SYM_arrow, SYM_at, SYM_bang, SYM_bangeq, SYM_bangeqeq, SYM_bar, SYM_barbar, SYM_bigarrow, SYM_colon, SYM_coloncolon, SYM_coma, SYM_div, SYM_dotdotdot, SYM_eq, SYM_eqeq, SYM_eqeqeq, SYM_gt, SYM_gteq, SYM_iff, SYM_implies, SYM_langle, SYM_lbrace, SYM_lbrack, SYM_lparen, SYM_lt, SYM_lteq, SYM_minus, SYM_negate, SYM_plus, SYM_positive, SYM_question, SYM_rangle, SYM_rbrace, SYM_rbrack, SYM_rparen, SYM_semicolon, SYM_times, SpaceFrontSymbols, SpaceRequiredSymbols, StandardSymbols } from "./parser_kw";

const { accepts, inializeLexer, lexFront } = require("@bosque/jsbrex");

type ParsePhase = number;
const ParsePhase_RegisterNamespaces: ParsePhase = 1;
const ParsePhase_RegisterTypes: ParsePhase = 2;
const ParsePhase_CompleteParse: ParsePhase = 3;

function isParsePhase_Enabled(phase: ParsePhase, current: ParsePhase): boolean {
    return phase === current;
}

const TokenStrings = {
    Clear: "[CLEAR]",
    Error: "[ERROR]",
    Recover: "[RECOVER]",

    DocComment: "[DOC_COMMENT]",

    NumberinoInt: "[LITERAL_NUMBERINO_INT]",
    NumberinoFloat: "[LITERAL_NUMBERINO_FLOAT]",

    TaggedNumberinoInt: "[LITERAL_TAGGED_NUMBERINO_INT]",
    TaggedNumberinoFloat: "[LITERAL_TAGGED_NUMBERINO_FLOAT]",
    TaggedNumberinoRational: "[LITERAL_TAGGED_NUMBERINO_RATIONAL]",

    TaggedBoolean: "[LITERAL_TAGGED_BOOLEAN]",

    Nat: "[LITERAL_NAT]",
    Int: "[LITERAL_INT]",
    BigNat: "[LITERAL_BIGNAT]",
    BigInt: "[LITERAL_BIGINT]",
    Float: "[LITERAL_FLOAT]",
    Decimal: "[LITERAL_DECIMAL]",
    Rational: "[LITERAL_RATIONAL]",
    DecimalDegree: "[LITERAL_DECIMAL_DEGREE]",
    LatLong: "[LITERAL_LATLONG]",
    Complex: "[LITERAL_COMPLEX]",
    
    ByteBuffer: "[LITERAL_BYTEBUFFER]",
    UUIDValue: "[LITERAL_UUID]",
    ShaHashcode: "[LITERAL_SHA]",

    String: "[LITERAL_STRING]",
    ASCIIString: "[LITERAL_ASCII_STRING]",
    TemplateString: "[LITERAL_TEMPLATE_STRING]",
    TemplateASCIIString: "[LITERAL_TEMPLATE_ASCII_STRING]",

    Regex: "[LITERAL_REGEX]",
    PathItem: "[LITERAL_PATH_ITEM]",

    DateTime: "[LITERAL_DATETIME]",
    UTCDateTime: "[LITERAL_UTC_DATETIME]",
    PlainDate: "[LITERAL_PLAIN_DATE]",
    PlainTime: "[LITERAL_PLAIN_TIME]",
    TickTime: "[LITERAL_TICK_TIME]",
    LogicalTime: "[LITERAL_LOGICAL_TIME]",
    Timestamp: "[LITERAL_TIMESTAMP]",

    DeltaDateTime: "[LITERAL_DELTA_DATETIME]",
    DeltaUTCDateTime: "[LITERAL_DELTA_UTC_DATETIME]",
    DeltaPlainDate: "[LITERAL_DELTA_PLAIN_DATE]",
    DeltaPlainTime: "[LITERAL_DELTA_PLAIN_TIME]",
    DeltaSeconds: "[LITERAL_DELTA_SECONDS]",
    DeltaTickTime: "[LITERAL_DELTA_TICK_TIME]",
    DeltaLogicalTime: "[LITERAL_DELTA_LOGICAL_TIME]",
    DeltaTimestamp: "[LITERAL_DELTA_TIMESTAMP]",

    //Names
    Template: "[TEMPLATE]",
    IdentifierName: "[IDENTIFIER]",
    Attribute: "[ATTRIBUTE]",

    EndOfStream: "[EOS]"
};


const NAMESPACE_DECL_FIRSTS = [
    TokenStrings.Attribute,
    KW_recursive, KW_recursive_q, 
    KW_function, KW_predicate, 
    KW_namespace, KW_api,
    KW_const,
    KW_enum, KW_type, KW_typedecl, KW_entity, KW_concept, KW_typedecl, KW_datatype, KW_task,
    KW_event, KW_status,
    KW_validator,
    KW_errtest, KW_chktest
].sort((a, b) => { return (a.length !== b.length) ? (b.length - a.length) : ((a !== b) ? (a < b ? -1 : 1) : 0); });

const TYPE_DECL_FIRSTS = [
    TokenStrings.Attribute,
    KW_recursive, KW_recursive_q, 
    KW_ref,
    KW_field, KW_const, KW_invariant, KW_validate, 
    KW_function, KW_method, KW_action,
    KW_entity
].sort((a, b) => { return (a.length !== b.length) ? (b.length - a.length) : ((a !== b) ? (a < b ? -1 : 1) : 0); });

const PRIMITIVE_TYPE_NAMES = [

];

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

    getSourceInfo(): SourceInfo {
        return new SourceInfo(this.line, this.column, this.pos, this.span);
    }
}

class ParserError {
    readonly sinfo: SourceInfo;
    readonly message: string;

    constructor(sinfo: SourceInfo, message: string) {
        this.sinfo = sinfo;
        this.message = message;
    }

}

enum LexerStateScanMode {
    Enabled,
    EnabledIf,
    EnabledElse,
    Disabled,
    DisabledIf,
    DisabledElse
}

class LexerState {
    readonly modetag: string;
    readonly scanmode: LexerStateScanMode;

    readonly epos: number;

    cline: number;
    linestart: number;
    cpos: number;
    tokens: Token[];
    errors: ParserError[] = [];

    readonly attributes: string[];

    constructor(modetag: string, scanmode: LexerStateScanMode, epos: number, cline: number, linestart: number, cpos: number, tokens: Token[], attributes: string[]) {
        this.modetag = modetag;
        this.scanmode = scanmode;

        this.epos = epos;

        this.cline = cline;
        this.linestart = linestart;
        this.cpos = cpos;
        this.tokens = [];

        this.attributes = attributes;
    }

    static createFileToplevelState(epos: number): LexerState {
        return new LexerState("toplevel", LexerStateScanMode.Enabled, epos, 1, 0, 0, [], AllAttributes);
    }

    cloneForNested(mode: string, epos: number, attribs: string[] | undefined): LexerState {
        return new LexerState(mode, this.scanmode, epos, this.cline, this.linestart, this.cpos, [...this.tokens], this.attributes || []);
    }

    cloneForTry(mode: string): LexerState {
        return new LexerState(mode, this.scanmode, this.epos, this.cline, this.linestart, this.cpos, [...this.tokens], this.attributes);
    }

    cloneForMacro(smode: LexerStateScanMode): LexerState {
        return new LexerState(this.modetag, smode, this.epos, this.cline, this.linestart, this.cpos, [...this.tokens], this.attributes);
    }

    moveStateIntoParent(parent: LexerState) {
        parent.cline = this.cline;
        parent.linestart = this.linestart;
        parent.cpos = this.cpos;
        parent.tokens = this.tokens;
        parent.errors = this.errors;
    }

    pushError(sinfo: SourceInfo, message: string) {
        if(this.scanmode === LexerStateScanMode.Enabled || this.scanmode === LexerStateScanMode.EnabledIf || this.scanmode === LexerStateScanMode.EnabledElse) {
            this.errors.push(new ParserError(sinfo, message));
        }
    }

    pushToken(token: Token) {
        if(this.scanmode === LexerStateScanMode.Enabled || this.scanmode === LexerStateScanMode.EnabledIf || this.scanmode === LexerStateScanMode.EnabledElse) {
            this.tokens.push(token);
        }
    }

    recover() {
        this.cpos = this.epos;
        this.tokens = [];
    }

    skipToPosition(pos: number | undefined) {
        this.cpos = pos || this.epos;
        this.tokens = [];
    }

    hasErrors(): boolean {
        return this.errors.length > 0;
    }
}

class Lexer {
    readonly macrodefs: string[];
    readonly input: string;
    
    readonly namespaces: string[];
    readonly typenames: string[];

    readonly stateStack: LexerState[];

    currentState(): LexerState {
        return this.stateStack[this.stateStack.length - 1];
    }

    prepStateStackForNested(mode: string, epos: number, attribs: string[] | undefined) {
        this.stateStack.push(this.currentState().cloneForNested(mode, epos, attribs));
    }

    prepStateStackForTry(mode: string) {
        this.stateStack.push(this.currentState().cloneForTry(mode + "-try"));
    }

    prepStateStackForMacro(smode: LexerStateScanMode) {
        this.stateStack.push(this.currentState().cloneForMacro(smode));
    }

    popStateIntoParentOk() {
        const pf = this.stateStack.pop() as LexerState;
        this.currentState().moveStateIntoParent(pf);
    }

    popStateReset() {
        this.stateStack.pop();
    }

    constructor(input: string, macrodefs: string[], istate: LexerState, namespaces: string[], typenames: string[]) {
        this.macrodefs = macrodefs;
        this.input = input;

        this.namespaces = namespaces;
        this.typenames = typenames;

        this.stateStack = [istate];
    }

    ////
    //Helpers
    private recordLexToken(epos: number, kind: string) {
        const cstate = this.currentState();

        cstate.pushToken(new Token(cstate.cline, cstate.cpos - cstate.linestart, cstate.cpos, epos - cstate.cpos, kind, kind)); //set data to kind string
        cstate.cpos = epos;
    }

    private recordLexTokenWData(epos: number, kind: string, data: string) {
        const cstate = this.currentState();

        cstate.pushToken(new Token(cstate.cline, cstate.cpos - cstate.linestart, cstate.cpos, epos - cstate.cpos, kind, data));
        cstate.cpos = epos;
    }

    private updatePositionInfo(spos: number, epos: number) {
        const cstate = this.currentState();

        for (let i = spos; i < epos; ++i) {
            if (this.input[i] === "\n") {
                cstate.cline++;
                cstate.linestart = i + 1;
            }
        }
    }

    private static readonly _s_spaceSensitiveOps = SpaceRequiredSymbols.map((op) => `"${op.trim()}"`).join("|")
    private static readonly _s_spaceSensitiveOpsRe = `/[ %n;%v;%f;%r;%t;]+(${Lexer._s_spaceSensitiveOps})[ %n;%v;%f;%r;%t;]+/`;

    private static readonly _s_spaceSensitiveFrontOps = SpaceFrontSymbols.map((op) => `"${op.trim()}"`).join("|")
    private static readonly _s_spaceSensitiveFrontOpsRe = `/[ %n;%v;%f;%r;%t;]+(${Lexer._s_spaceSensitiveFrontOps})[^0-9+-]/`;

    private static readonly _s_whitespaceRe = '/[ %n;%v;%f;%r;%t;]+/';
    private tryLexWS(): boolean {
        const cstate = this.currentState();

        const arop = lexFront(Lexer._s_spaceSensitiveOpsRe, cstate.cpos);
        if (arop !== null) {
            return false;
        }

        const frop = lexFront(Lexer._s_spaceSensitiveFrontOpsRe, cstate.cpos);
        if (frop !== null) {
            return false;
        }

        const m = lexFront(Lexer._s_whitespaceRe, cstate.cpos);
        if (m === null) {
            return false;
        }

        this.updatePositionInfo(cstate.cpos, cstate.cpos + m.length);
        cstate.cpos += m.length;

        return true;
    }

    private tryLexLineComment(): boolean {
        const cstate = this.currentState();

        const m = this.input.startsWith("%%", cstate.cpos);
        if (!m) {
            return false;
        }

        let epos = this.input.slice(0, cstate.epos).indexOf("\n", cstate.cpos);

        if (epos === -1) {
            this.updatePositionInfo(cstate.cpos, epos);
            cstate.cpos = cstate.epos;
        }
        else {
            epos++;

            this.updatePositionInfo(cstate.cpos, epos);
            cstate.cpos = epos;
        }

        return true;
    }

    private tryLexDocComment(): boolean {
        const cstate = this.currentState();

        const m = this.input.startsWith("%** ", cstate.cpos);
        if (!m) {
            return false;
        }

        let epos = this.input.slice(0, cstate.epos).indexOf(" **%", cstate.cpos + 3);
        if (epos !== -1) {
            epos += 3;

            this.updatePositionInfo(cstate.cpos, epos);
            this.recordLexTokenWData(epos, TokenStrings.DocComment, this.input.substring(cstate.cpos, epos));
            return true;
        }

        return false;
    }

    private tryLexSpanComment(): boolean {
        const cstate = this.currentState();

        const m = this.input.startsWith("%*", cstate.cpos);
        if (!m) {
            return false;
        }

        let epos = this.input.slice(0, cstate.epos).indexOf("*%", cstate.cpos + 2);
        if (epos === -1) {
            cstate.pushError(new SourceInfo(cstate.cline, cstate.linestart, cstate.cpos, cstate.epos - cstate.cpos), "Unterminated span comment");
            
            this.updatePositionInfo(cstate.cpos, epos);
            cstate.cpos = cstate.epos;
        }
        else {
            epos += 2;

            this.updatePositionInfo(cstate.cpos, epos);
            cstate.cpos = epos;
        }

        return true;
    }

    private static readonly _s_templateNameRe = '/[A-Z]"Numeric"?/';
    private static isTemplateName(str: string): boolean {
        return accepts(Lexer._s_templateNameRe, str);
    }

    private static readonly _s_literalTDOnlyTagRE = `"_"`;

    private static readonly _s_nonzeroIntValNoSignRE = `[1-9][0-9]*`;
    private static readonly _s_nonzeroIntValRE = `[+-]?${Lexer._s_nonzeroIntValNoSignRE}`;
    private static readonly _s_intValueNoSignRE = `"0"|${Lexer._s_nonzeroIntValNoSignRE}`;
    private static readonly _s_intValueRE = `"0"|${Lexer._s_nonzeroIntValRE}`;

    private static readonly _s_nonzeroFloatValueNoSignRE = `[0-9]+"."[0-9]+([eE][-+]?[0-9]+)?`;
    private static readonly _s_nonzeroFloatValueRE = `([+-]?${Lexer._s_nonzeroFloatValueNoSignRE})([eE][-+]?[0-9]+)?`;
    private static readonly _s_floatValueNoSignRE = `"0.0"|${Lexer._s_nonzeroFloatValueNoSignRE}`;
    private static readonly _s_floatValueRE = `"0.0"|${Lexer._s_nonzeroFloatValueRE}`;

    private static readonly _s_nonzeroFloatSimpleValueNoSignRE = '([0-9]+"."[0-9]+)';
    private static readonly _s_floatSimpleValueNoSignRE = `"0.0"|${Lexer._s_nonzeroFloatSimpleValueNoSignRE}`;
    private static readonly _s_floatSimpleValueRE = `"0.0"|[+-]?${Lexer._s_nonzeroFloatSimpleValueNoSignRE}`;

    private static readonly _s_intNumberinoRe = `/${Lexer._s_intValueRE}/`;
    private static readonly _s_floatNumberinoRe = `/${Lexer._s_floatValueRE}/`;

    private static readonly _s_intTaggedNumberinoRe = `/${Lexer._s_intValueRE}${Lexer._s_literalTDOnlyTagRE}/`;
    private static readonly _s_floatTaggedNumberinoRe = `/${Lexer._s_floatValueRE}${Lexer._s_literalTDOnlyTagRE}/`;
    private static readonly _s_rationalTaggedNumberinoRe = `/(${Lexer._s_intValueRE})"%slash;"(${Lexer._s_nonzeroIntValNoSignRE})${Lexer._s_literalTDOnlyTagRE}/`;

    private static readonly _s_intRe = `/(${Lexer._s_intValueRE})"i"(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static readonly _s_natRe = `/(${Lexer._s_intValueRE})"n"(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static readonly _s_bigintRe = `/(${Lexer._s_intValueRE})"I"(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static readonly _s_bignatRe = `/(${Lexer._s_intValueRE})"N"(${Lexer._s_literalTDOnlyTagRE})?/`;

    private static readonly _s_floatRe = `/(${Lexer._s_floatValueRE})"f"(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static readonly _s_decimalRe = `/(${Lexer._s_floatValueRE})"d"(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static readonly _s_rationalRe = `/(${Lexer._s_intValueRE})"%slash;"(${Lexer._s_nonzeroIntValNoSignRE})"R"(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static readonly _s_complexRe = `/(${Lexer._s_floatValueRE})[+-](${Lexer._s_floatValueNoSignRE})"j"(${Lexer._s_literalTDOnlyTagRE})?/`;

    private static readonly _s_decimalDegreeRe = `/(${Lexer._s_floatSimpleValueRE})"dd"(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static readonly _s_latlongRe = `/(${Lexer._s_floatSimpleValueRE})"lat"[+-]${Lexer._s_floatSimpleValueNoSignRE}"long"(${Lexer._s_literalTDOnlyTagRE})?/`;
    
    private static readonly _s_ticktimeRe = `/(${Lexer._s_intValueRE})"t"(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static readonly _s_logicaltimeRe = `/(${Lexer._s_intValueRE})"l"(${Lexer._s_literalTDOnlyTagRE})?/`;

    private static readonly _s_deltasecondsRE = `/[+-](${Lexer._s_floatValueNoSignRE})"ds"(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static readonly _s_deltaticktimeRE = `/[+-](${Lexer._s_intValueNoSignRE})"dt"(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static readonly _s_deltalogicaltimeRE = `/[+-](${Lexer._s_intValueNoSignRE})"dl"(${Lexer._s_literalTDOnlyTagRE})?/`;

    private static readonly _s_redundantSignRE = /^[+-]{2,}/y;
    private checkRedundantSigns() {
        const cstate = this.currentState();

        Lexer._s_redundantSignRE.lastIndex = cstate.cpos;
        const mm = Lexer._s_redundantSignRE.exec(this.input);
        if(mm !== null) {
            cstate.errors.push(new ParserError(new SourceInfo(cstate.cline, cstate.linestart, cstate.cpos, cstate.epos - cstate.cpos), "Redundant sign"));
            cstate.cpos = Math.min(cstate.epos, cstate.cpos + mm.length - 1);
        }
    }

    private tryLexFloatCompositeLikeToken(): boolean {
        const cstate = this.currentState();

        const mcomplex = lexFront(Lexer._s_complexRe, cstate.cpos);
        if(mcomplex !== null) {
            this.recordLexTokenWData(cstate.cpos + mcomplex.length, TokenStrings.Complex, mcomplex);
            return true;
        }

        const mlatlong = lexFront(Lexer._s_latlongRe, cstate.cpos);
        if(mlatlong !== null) {
            this.recordLexTokenWData(cstate.cpos + mlatlong.length, TokenStrings.LatLong, mlatlong);
            return true;
        }

        return false;
    }

    private tryLexFloatLikeToken(): boolean {
        const cstate = this.currentState();

        const mdecimaldegree = lexFront(Lexer._s_decimalDegreeRe, cstate.cpos);
        if(mdecimaldegree !== null) {
            this.recordLexTokenWData(cstate.cpos + mdecimaldegree.length, TokenStrings.DecimalDegree, mdecimaldegree);
            return true;
        }

        const mdeltaseconds = lexFront(Lexer._s_deltasecondsRE, cstate.cpos);
        if(mdeltaseconds !== null) {
            this.recordLexTokenWData(cstate.cpos + mdeltaseconds.length, TokenStrings.DeltaSeconds, mdeltaseconds);
            return true;
        }

        const mdecimal = lexFront(Lexer._s_decimalRe, cstate.cpos);
        if(mdecimal !== null) {
            this.recordLexTokenWData(cstate.cpos + mdecimal.length, TokenStrings.Decimal, mdecimal);
            return true;
        }

        const mfloat = lexFront(Lexer._s_floatRe, cstate.cpos);
        if(mfloat !== null) {
            this.recordLexTokenWData(cstate.cpos + mfloat.length, TokenStrings.Float, mfloat);
            return true;
        }

        const mnumberino = lexFront(Lexer._s_floatTaggedNumberinoRe, cstate.cpos);
        if(mnumberino !== null) {
            this.recordLexTokenWData(cstate.cpos + mnumberino.length, TokenStrings.TaggedNumberinoFloat, mnumberino);
            return true;
        }

        const unumberino = lexFront(Lexer._s_floatNumberinoRe, cstate.cpos);
        if(unumberino !== null) {
            this.recordLexTokenWData(cstate.cpos + unumberino.length, TokenStrings.NumberinoFloat, unumberino);
            return true;
        }

        return false;
    }

    private tryLexIntegralCompositeLikeToken(): boolean {
        const cstate = this.currentState();

        const mrational = lexFront(Lexer._s_rationalRe, cstate.cpos);
        if(mrational !== null) {
            this.recordLexTokenWData(cstate.cpos + mrational.length, TokenStrings.Rational, mrational);
            return true;
        }

        const mnumberino = lexFront(Lexer._s_rationalTaggedNumberinoRe, cstate.cpos);
        if(mnumberino !== null) {
            this.recordLexTokenWData(cstate.cpos + mnumberino.length, TokenStrings.TaggedNumberinoRational, mnumberino);
            return true;
        }

        return false;
    }

    private tryLexIntegralLikeToken(): boolean {
        const cstate = this.currentState();

        const mtick = lexFront(Lexer._s_ticktimeRe, cstate.cpos);
        if(mtick !== null) {
            this.recordLexTokenWData(cstate.cpos + mtick.length, TokenStrings.TickTime, mtick);
            return true;
        }

        const mlogical = lexFront(Lexer._s_logicaltimeRe, cstate.cpos);
        if(mlogical !== null) {
            this.recordLexTokenWData(cstate.cpos + mlogical.length, TokenStrings.LogicalTime, mlogical);
            return true;
        }

        const m_deltatick = lexFront(Lexer._s_deltaticktimeRE, cstate.cpos);
        if(m_deltatick !== null) {
            this.recordLexTokenWData(cstate.cpos + m_deltatick.length, TokenStrings.DeltaTickTime, m_deltatick);
            return true;
        }

        const m_deltalogical = lexFront(Lexer._s_deltalogicaltimeRE, cstate.cpos);
        if(m_deltalogical !== null) {
            this.recordLexTokenWData(cstate.cpos + m_deltalogical.length, TokenStrings.DeltaLogicalTime, m_deltalogical);
            return true;
        }
        
        const mint = lexFront(Lexer._s_intRe, cstate.cpos);
        if(mint !== null) {
            this.recordLexTokenWData(cstate.cpos + mint.length, TokenStrings.Int, mint);
            return true;
        }

        const mnat = lexFront(Lexer._s_natRe, cstate.cpos);
        if(mnat !== null) {
            this.recordLexTokenWData(cstate.cpos + mnat.length, TokenStrings.Nat, mnat);
            return true;
        }

        const mbigint = lexFront(Lexer._s_bigintRe, cstate.cpos);
        if(mbigint !== null) {
            this.recordLexTokenWData(cstate.cpos + mbigint.length, TokenStrings.BigInt, mbigint);
            return true;
        }

        const mbignat = lexFront(Lexer._s_bignatRe, cstate.cpos);
        if(mbignat !== null) {
            this.recordLexTokenWData(cstate.cpos + mbignat.length, TokenStrings.BigNat, mbignat);
            return true;
        }

        const mtnumberino = lexFront(Lexer._s_intTaggedNumberinoRe, cstate.cpos);
        if(mtnumberino !== null) {
            this.recordLexTokenWData(cstate.cpos + mtnumberino.length, TokenStrings.TaggedNumberinoInt, mtnumberino);
            return true;
        }

        const mnumberino = lexFront(Lexer._s_intNumberinoRe, cstate.cpos);
        if(mnumberino !== null) {
            this.recordLexTokenWData(cstate.cpos + mnumberino.length, TokenStrings.NumberinoInt, mnumberino);
            return true;
        }

        return false;
    }

    private tryLexNumberLikeToken(): boolean {
        this.checkRedundantSigns();

        const cft = this.tryLexFloatCompositeLikeToken();
        if(cft) {
            return true;
        }
        
        const ft = this.tryLexFloatLikeToken();
        if(ft) {
            return true;
        }

        const cit = this.tryLexIntegralCompositeLikeToken();
        if(cit) {
            return true;
        }

        const it = this.tryLexIntegralLikeToken();
        if(it) {
            return true;
        }

        return false;
    }

    private static _s_bytebufferRe = `/"0x["[0-9a-fA-F]+"]"(${Lexer._s_literalTDOnlyTagRE})?/`;
    private tryLexByteBuffer(): boolean {
        const cstate = this.currentState();

        const m = lexFront(Lexer._s_bytebufferRe, cstate.cpos);
        if(m !== null) {
            this.recordLexTokenWData(cstate.cpos + m.length, TokenStrings.ByteBuffer, m);
            return true;
        }

        return false;
    }

    private static _s_uuidRe = `/"uuid"[47]"{"[a-fA-F0-9]{8}"-"[a-fA-F0-9]{4}"-"[a-fA-F0-9]{4}"-"[a-fA-F0-9]{4}-[a-fA-F0-9]{12}"}"(${Lexer._s_literalTDOnlyTagRE})?/`;
    private tryLexUUID(): boolean {
        const cstate = this.currentState();

        const m = lexFront(Lexer._s_uuidRe, cstate.cpos);
        if(m !== null) {
            this.recordLexTokenWData(cstate.cpos + m.length, TokenStrings.UUIDValue, m);
            return true;
        }

        return false;
    }

    private static _s_shaRe = `/"sha3{"[a-fA-F0-9]{64}"}"(${Lexer._s_literalTDOnlyTagRE})?/`;
    private tryLexHashCode(): boolean {
        const cstate = this.currentState();

        const m = lexFront(Lexer._s_shaRe, cstate.cpos);
        if(m !== null) {
            this.recordLexTokenWData(cstate.cpos + m.length, TokenStrings.ShaHashcode, m);
            return true;
        }

        return false;
    }

    private static readonly _s_literalGeneralTagRE = /^_?[A-Z(]/y;

    private tryLexUnicodeString(): boolean {
        const cstate = this.currentState();

        let ncpos = cstate.cpos;
        let istemplate = false;
        if(this.input.startsWith('$"', cstate.cpos)) {
            ncpos += 2;
            istemplate = true;
        }
        else if(!this.input.startsWith('"', cstate.cpos)) {
            ncpos += 1;
        }
        else {
            return false;
        }


        let epos = this.input.slice(0, cstate.epos).indexOf('"', ncpos);
        if(epos === -1) {
            cstate.pushError(new SourceInfo(cstate.cline, cstate.linestart, cstate.cpos, cstate.epos - cstate.cpos), "Unterminated string literal");
            this.recordLexToken(cstate.epos, TokenStrings.Error);

            return true;
        }
        else {
            epos++;
            let strval = this.input.substring(ncpos, epos);

            Lexer._s_literalGeneralTagRE.lastIndex = epos;
            const mtag = Lexer._s_literalGeneralTagRE.exec(this.input);
            if(mtag !== null) {
                if(istemplate) {
                    cstate.pushError(new SourceInfo(cstate.cline, cstate.linestart, cstate.cpos, cstate.epos - cstate.cpos), "Template strings cannot have type tags");
                }
                else {
                    if(!mtag[0].startsWith("_")) {
                        strval += "[OF]"; //put special marker on back of string value for later
                    }
                    else {
                        epos++; //eat the underscore and include it in the string
                        strval += "_";
                    }
                }   
            }

            this.updatePositionInfo(cstate.cpos, epos);
            this.recordLexTokenWData(epos, istemplate ? TokenStrings.TemplateString : TokenStrings.String, strval);
            return true;
        }
    }

    private tryLexASCIIString(): boolean {
        const cstate = this.currentState();

        let ncpos = cstate.cpos;
        let istemplate = false;
        if(this.input.startsWith("$'", cstate.cpos)) {
            ncpos += 2;
            istemplate = true;
        }
        else if(!this.input.startsWith("'", cstate.cpos)) {
            ncpos += 1;
        }
        else {
            return false;
        }

        let epos = this.input.slice(0, cstate.epos).indexOf("'", ncpos);
        if(epos === -1) {
            cstate.pushError(new SourceInfo(cstate.cline, cstate.linestart, cstate.cpos, cstate.epos - cstate.cpos), "Unterminated ASCII string literal");
            this.recordLexToken(cstate.epos, TokenStrings.Error);

            return true;
        }
        else {
            epos++;
            let strval = this.input.substring(ncpos, epos);

            Lexer._s_literalGeneralTagRE.lastIndex = epos;
            const mtag = Lexer._s_literalGeneralTagRE.exec(this.input);
            if(mtag !== null) {
                if(istemplate) {
                    cstate.pushError(new SourceInfo(cstate.cline, cstate.linestart, cstate.cpos, cstate.epos - cstate.cpos), "Template strings cannot have type tags");
                }
                else {
                    if(!mtag[0].startsWith("_")) {
                        strval += "[OF]"; //put special marker on back of string value for later
                    }
                    else {
                        epos++; //eat the underscore and include it in the string
                        strval += "_";
                    }
                }   
            }

            this.updatePositionInfo(cstate.cpos, epos);
            this.recordLexTokenWData(epos, istemplate ? TokenStrings.TemplateASCIIString : TokenStrings.ASCIIString, strval);
            return true;
        }
    }

    private tryLexStringLike() {
        const us = this.tryLexUnicodeString();
        if(us) {
            return true;
        }

        const as = this.tryLexASCIIString();
        if(as) {
            return true;
        }

        return false;
    }

    private static _s_regexRe = '/"%slash;"[!-.0-~ %t;%n;]+"%slash;"[ap]?/';
    private tryLexRegex() {
        const cstate = this.currentState();

        const rem = lexFront(Lexer._s_regexRe, cstate.cpos);
        if(rem === null) {
            return false;
        }

        this.recordLexTokenWData(cstate.cpos + rem.length, TokenStrings.Regex, rem);
        return true;
    }

    
    private static _s_pathRe = /[gf]?\\[ !-Z^-~\[\]]\\/y;
    private static readonly _s_literalPathTagRE = /^_?[A-Z(]/y;
    private tryLexPath() {
        const cstate = this.currentState();

        Lexer._s_pathRe.lastIndex = cstate.cpos;
        const mpth = Lexer._s_pathRe.exec(this.input);
        if(mpth !== null) {
            let epos = cstate.cpos + mpth[0].length;
            let pthval = mpth[0];

            Lexer._s_literalPathTagRE.lastIndex = epos;
            const mtag = Lexer._s_literalPathTagRE.exec(this.input);
            if(mtag !== null) {
                if(mtag[0].startsWith("_")) {
                    epos++; //eat the underscore and include it in the string
                    pthval += "_"; 
                }
                else if(!mtag[0].startsWith("_")) {
                    pthval += "[OF]"; //put special marker on back of string value for later
                }
                else {
                    //implicit path of URI
                    pthval += "*";
                }
            }

            this.updatePositionInfo(cstate.cpos, epos);
            this.recordLexTokenWData(epos, TokenStrings.PathItem, pthval);
            return true;
        }

        return false;
    }

    private static _s_datevalueRE = '([0-9]{4})-([0-9]{2})-([0-9]{2})';
    private static _s_timevalueRE = '([0-9]{2}):([0-9]{2}):([0-9]{2})';
    private static _s_tzvalueRE = '(("%lbrace;"[a-zA-Z0-9/, _-]+"%rbrace;")|[A-Z]+)';

    private static _s_datatimeRE = `/${Lexer._s_datevalueRE}"T"${Lexer._s_timevalueRE}"@"${Lexer._s_tzvalueRE}(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static _s_utcdatetimeRE = `/${Lexer._s_datevalueRE}"T"${Lexer._s_timevalueRE}"Z"?(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static _s_plaindateRE = `/${Lexer._s_datevalueRE}(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static _s_plaintimeRE = `/${Lexer._s_timevalueRE}(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static _s_timestampRE = `/${Lexer._s_datevalueRE}"T"${Lexer._s_timevalueRE}"."([0-9]{3})"Z"(${Lexer._s_literalTDOnlyTagRE})?/`;

    private tryLexDateTime() {
        const cstate = this.currentState();

        const mdt = lexFront(Lexer._s_datatimeRE, cstate.cpos);
        if(mdt !== null) {
            this.recordLexTokenWData(cstate.cpos + mdt.length, TokenStrings.DateTime, mdt);
            return true;
        }

        const mutcdt = lexFront(Lexer._s_utcdatetimeRE, cstate.cpos);
        if(mutcdt !== null) {
            this.recordLexTokenWData(cstate.cpos + mutcdt.length, TokenStrings.UTCDateTime, mutcdt);
            return true;
        }

        const mts = lexFront(Lexer._s_timestampRE, cstate.cpos);
        if(mts !== null) {
            this.recordLexTokenWData(cstate.cpos + mts.length, TokenStrings.Timestamp, mts);
            return true;
        }

        const mpd = lexFront(Lexer._s_plaindateRE, cstate.cpos);
        if(mpd !== null) {
            this.recordLexTokenWData(cstate.cpos + mpd.length, TokenStrings.PlainDate, mpd);
            return true;
        }

        const mpt = lexFront(Lexer._s_plaintimeRE, cstate.cpos);
        if(mpt !== null) {
            this.recordLexTokenWData(cstate.cpos + mpt.length, TokenStrings.PlainTime, mpt);
            return true;
        }

        return false;
    }
    private static _s_datatimeDeltaRE = `/[+-]${Lexer._s_datevalueRE}"T"${Lexer._s_timevalueRE}"@"${Lexer._s_tzvalueRE}(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static _s_utcdatetimeDeltaRE = `/[+-]${Lexer._s_datevalueRE}"T"${Lexer._s_timevalueRE}"Z"?(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static _s_plaindateDeltaRE = `/[+-]${Lexer._s_datevalueRE}(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static _s_plaintimeDeltaRE = `/[+-]${Lexer._s_timevalueRE}(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static _s_timestampDeltaRE = `/[+-]${Lexer._s_datevalueRE}"T"${Lexer._s_timevalueRE}"."([0-9]{3})"Z"(${Lexer._s_literalTDOnlyTagRE})?/`;

    private tryLexDateTimeDelta() {
        const cstate = this.currentState();

        const mdt = lexFront(Lexer._s_datatimeDeltaRE, cstate.cpos);
        if(mdt !== null) {
            this.recordLexTokenWData(cstate.cpos + mdt.length, TokenStrings.DeltaDateTime, mdt);
            return true;
        }

        const mutcdt = lexFront(Lexer._s_utcdatetimeDeltaRE, cstate.cpos);
        if(mutcdt !== null) {
            this.recordLexTokenWData(cstate.cpos + mutcdt.length, TokenStrings.DeltaUTCDateTime, mutcdt);
            return true;
        }

        const mts = lexFront(Lexer._s_timestampDeltaRE, cstate.cpos);
        if(mts !== null) {
            this.recordLexTokenWData(cstate.cpos + mts.length, TokenStrings.DeltaTimestamp, mts);
            return true;
        }

        const mpd = lexFront(Lexer._s_plaindateDeltaRE, cstate.cpos);
        if(mpd !== null) {
            this.recordLexTokenWData(cstate.cpos + mpd.length, TokenStrings.DeltaPlainDate, mpd);
            return true;
        }

        const mpt = lexFront(Lexer._s_plaintimeDeltaRE, cstate.cpos);
        if(mpt !== null) {
            this.recordLexTokenWData(cstate.cpos + mpt.length, TokenStrings.DeltaPlainTime, mpt);
            return true;
        }

        return false;
    }

    private tryLexDateLike(): boolean {
        const mdd = this.tryLexDateTimeDelta();
        if(mdd) {
            return true;
        }

        const mdt = this.tryLexDateTime();
        if(mdt) {
            return true;
        }

        return false;
    }

    private tryLexSymbol() {
        const cstate = this.currentState();

        const spaceop = lexFront(Lexer._s_spaceSensitiveOpsRe, cstate.cpos);
        const frontop = lexFront(Lexer._s_spaceSensitiveFrontOpsRe, cstate.cpos);
        if(spaceop !== null) {
            const realstr = " " + spaceop.trim() + " ";

            this.recordLexToken(cstate.cpos + spaceop.length, realstr);
            return true; 
        }
        else if(frontop !== null) {
            const realstr = " " + spaceop.trim();

            this.recordLexToken(cstate.cpos + frontop.length, realstr);
            return true; 
        }
        else {
            const mm = StandardSymbols.find((value) => this.input.startsWith(value, cstate.cpos)) || ParenSymbols.find((value) => this.input.startsWith(value, cstate.cpos));
            if(mm !== undefined) {
                this.recordLexToken(cstate.cpos + mm.length, mm);
                return true;
            }

        
            return false;
        }
    }

    private tryLexAttribute() {
        const cstate = this.currentState();
        const attrsopt = cstate.attributes;

        const mm = attrsopt.find((value) => this.input.startsWith(value, cstate.cpos));
        if(mm !== undefined) {
            let epos = cstate.cpos + mm.length;
            if(this.input.startsWith("[", epos)) {
                epos = this.input.slice(epos, cstate.epos).indexOf("]", epos);
                if(epos === -1) {
                    cstate.pushError(new SourceInfo(cstate.cline, cstate.linestart, cstate.cpos, cstate.epos - cstate.cpos), "Unterminated attribute");
                    this.recordLexToken(cstate.epos, TokenStrings.Error);
                    return true;
                }
                epos++;
            }

            this.recordLexTokenWData(epos, TokenStrings.Attribute, this.input.substring(cstate.cpos, epos));
            return true;
        }

        return false;
    }

    private processIdentifierOptions(idm: string): boolean {
        const cstate = this.currentState();

        if(Lexer.isTemplateName(idm)) {
            this.recordLexTokenWData(cstate.cpos + idm.length, TokenStrings.Template, idm);
            return true;
        }
        else
        {        
            this.recordLexTokenWData(cstate.cpos + idm.length, TokenStrings.IdentifierName, idm);
            return true;
        }
    }

    private static readonly _s_taggedBooleanRE = `/<("true"|"false")"_">$[A-Z(]?/`;
    private static readonly _s_identiferName = '/"$"?[_a-zA-Z][_a-zA-Z0-9]*/';
    private tryLexName(): boolean {
        const cstate = this.currentState();

        const mtb = lexFront(Lexer._s_taggedBooleanRE, cstate.cpos);
        if (mtb !== null) {
            this.recordLexTokenWData(cstate.cpos + mtb.length, TokenStrings.TaggedBoolean, mtb);
            return true;
        }

        const identifiermatch = lexFront(Lexer._s_identiferName, cstate.cpos);
        const kwmatch = KeywordStrings.find((value) => this.input.startsWith(value, cstate.cpos));

        if(identifiermatch === null && kwmatch === undefined) {
            return false;
        }

        if (identifiermatch !== null && kwmatch === undefined) {
            return this.processIdentifierOptions(identifiermatch);
        }
        else if(identifiermatch === null && kwmatch !== undefined) {
            this.recordLexToken(cstate.cpos + kwmatch.length, kwmatch);
            return true;
        }
        else {
            const nnid = identifiermatch as string;
            const nnkw = kwmatch as string;

            if (nnid.length > nnkw.length) {
                return this.processIdentifierOptions(nnid);
            }
            else {
                this.recordLexToken(cstate.cpos + nnkw.length, nnkw);
                return true;
            }
        }
    }

    private static readonly _s_macroRe = '/("#if"" "+([A-Z][_A-Z0-9]*)|"#else"|"#endif")/';
    tryLexMacroOp(): [string, string | undefined] | undefined {
        const cstate = this.currentState();

        const m = lexFront(Lexer._s_macroRe, cstate.cpos);
        if (m === null) {
            return undefined;
        }

        const name = m[0].trim();
        cstate.cpos += m[0].length;

        if(name.slice(0, "#if".length) === "#if") {
            return ["#if", name.slice("#if".length).trim()];
        }
        else {
            return [name, undefined]
        }
    }

    lexk(k: number): Token[] {
        let cstate = this.currentState();
        if (cstate.tokens.length > k) {
            return cstate.tokens;
        }

        cstate.tokens = [];
        while (cstate.cpos < cstate.epos && cstate.tokens.length < k) {
            const macro = this.tryLexMacroOp();
            if(macro !== undefined) {
                if(macro[0] === "#if") {
                    const ifenabled = this.macrodefs.includes(macro[1] as string);
                    const cenabled = cstate.scanmode === LexerStateScanMode.Enabled || cstate.scanmode === LexerStateScanMode.EnabledIf || cstate.scanmode === LexerStateScanMode.EnabledElse;

                    let nscanmode = LexerStateScanMode.Disabled;
                    if(cenabled) {
                        nscanmode = ifenabled ? LexerStateScanMode.EnabledIf : LexerStateScanMode.DisabledIf;
                    }

                    this.prepStateStackForMacro(nscanmode);
                    cstate = this.currentState();
                }
                else if(macro[0] === "#else") {
                    const ifmode = cstate.scanmode;
                    this.popStateIntoParentOk();

                    if(ifmode === LexerStateScanMode.Disabled) {
                        this.prepStateStackForMacro(LexerStateScanMode.Disabled);
                    }
                    else {
                        let nscanmode = ifmode === LexerStateScanMode.EnabledIf ? LexerStateScanMode.DisabledElse : LexerStateScanMode.EnabledElse;
                        this.prepStateStackForMacro(nscanmode);
                    }

                    cstate = this.currentState();
                }
                else {
                    this.popStateIntoParentOk();
                    cstate = this.currentState();
                }
            }
            else {
                if (this.tryLexWS() || this.tryLexLineComment() || this.tryLexDocComment() || this.tryLexSpanComment()) {
                    //continue
                }
                else if(this.tryLexDateLike()) {
                    //continue
                }
                else if (this.tryLexPath() || this.tryLexRegex()) {
                    //continue
                }
                else if(this.tryLexStringLike()) {
                    //continue
                }
                else if(this.tryLexByteBuffer() || this.tryLexUUID() || this.tryLexHashCode()) {
                    //continue
                }
                else if (this.tryLexNumberLikeToken()) {
                    //continue
                }
                else if(this.tryLexAttribute()) {
                    //continue
                }
                else if (this.tryLexSymbol() || this.tryLexName()) {
                    //continue
                }
                else {
                    this.recordLexToken(cstate.cpos + 1, TokenStrings.Error);
                }
            }
        }

        if(cstate.cpos === cstate.epos) {
            if(cstate.cpos === this.input.length) {
                this.recordLexToken(this.input.length, TokenStrings.EndOfStream);
            }
            else {
                this.recordLexToken(cstate.cpos, TokenStrings.Recover);
            }
        }

        return cstate.tokens;
    }

    lexNext(): Token {
        this.lexk(1);
        return this.currentState().tokens[0];
    }

    peekK(k: number): Token {
        this.lexk(k + 1);
        
        const cstate = this.currentState();
        if(cstate.tokens.length < k) {
            return cstate.tokens[cstate.tokens.length - 1];
        }
        else {
            return cstate.tokens[k];
        }
    }

    peekNext(): Token {
        return this.peekK(0);
    }

    consumeK(k: number) {
        this.lexk(k);

        const tks = this.currentState().tokens;
        while(k > 0 && (tks[0].kind !== TokenStrings.EndOfStream && tks[0].kind !== TokenStrings.Recover)) {
            tks.shift();
        }
    }

    consumeToken() {
        this.consumeK(1);
    }
}

class Parser {
    private lexer: Lexer;
    private env: ParserEnvironment;

    private currentPhase: ParsePhase;
    private declaredToplevelNamespaces: string[] = [];

    wellknownTypes: Map<string, NominalTypeSignature> = new Map<string, NominalTypeSignature>();

    constructor(currentFile: string, toplevelns: string, contents: string, macrodefs: string[], assembly: Assembly, currentPhase: ParsePhase) {
        const allToplevelNamespaces = assembly.toplevelNamespaces.map((nsd) => nsd.name);
        if(!allToplevelNamespaces.includes("Core")) {
            allToplevelNamespaces.push("Core");
        }

        this.lexer = new Lexer(contents, macrodefs, LexerState.createFileToplevelState(contents.length), allToplevelNamespaces.sort(), []);

        const nns = assembly.ensureToplevelNamespace(toplevelns);
        this.env = new ParserEnvironment(assembly, currentFile, nns);

        this.currentPhase = currentPhase;
    }

    ////
    //Helpers

    private static attributeSetContains(attr: string, attribs: string[]): boolean {
        return attribs.indexOf(attr) !== -1;
    }

    private recordExpectedError(token: Token, expected: string, contextinfo: string) {
        const cstate = this.lexer.currentState();
        cstate.errors.push(new ParserError(token.getSourceInfo(), `Expected "${expected}" but got "${token.data || token.kind}" when parsing "${contextinfo}"`));
    }

    private recordErrorGeneral(sinfo: SourceInfo, msg: string) {
        const cstate = this.lexer.currentState();
        cstate.errors.push(new ParserError(sinfo, msg));
    }

    private scanMatchingParens(lp: string, rp: string): number | undefined {
        let pscount = 1;
        let tpos = 1;

        let tok = this.lexer.peekK(tpos);
        while (tok.kind !== TokenStrings.EndOfStream && tok.kind !== TokenStrings.Recover) {
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
                return tpos;
            }

            tpos++;
            tok = this.lexer.peekK(tpos);
        }

        return undefined;
    }

    private scanCodeParens(): number | undefined {
        let pscount = 1;
        let tpos = 1;

        let tok = this.lexer.peekK(tpos);
        while (tok.kind !== TokenStrings.EndOfStream && tok.kind !== TokenStrings.Recover) {
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
                return tpos;
            }

            tpos++;
            tok = this.lexer.peekK(tpos);
        }

        return undefined;
    }

    private scanToRecover(trecover: string): number | undefined {
        let pscount = 0;
        let tpos = 0;

        let tok = this.lexer.peekK(tpos);
        while (tok.kind !== TokenStrings.EndOfStream && tok.kind !== TokenStrings.Recover) {
            if (LeftScanParens.indexOf(tok.kind) !== -1) {
                pscount++;
            }
            else if (RightScanParens.indexOf(tok.kind) !== -1) {
                pscount--;
            }
            else {
                //nop
            }

            if(tok.kind === trecover && pscount === 0) {
                return tpos;
            }

            tpos++;
            tok = this.lexer.peekK(tpos);
        }

        return undefined;
    }

    private scanToSyncPos(...tsync: string[]): number | undefined {
        let pscount = 0;
        let tpos = 0;

        let tok = this.lexer.peekK(tpos);
        while (tok.kind !== TokenStrings.EndOfStream && tok.kind !== TokenStrings.Recover) {
            if (LeftScanParens.indexOf(tok.kind) !== -1) {
                pscount++;
            }
            else if (RightScanParens.indexOf(tok.kind) !== -1) {
                pscount--;
            }
            else {
                //nop
            }

            if(tsync.includes(tok.kind) && pscount === 0) {
                return tpos;
            }

            tpos++;
            tok = this.lexer.peekK(tpos);
        }

        return undefined;
    }

    private scanToSyncEatParens(lp: string, rp: string): number | undefined {
        this.ensureAndConsumeToken(lp, "sync-eat-parens");
        
        let pscount = 1;
        let tpos = 1;

        let tok = this.lexer.peekK(tpos);
        while (tok.kind !== TokenStrings.EndOfStream && tok.kind !== TokenStrings.Recover) {
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
                return tpos;
            }

            tpos++;
            tok = this.lexer.peekK(tpos);
        }

        return undefined;
    }

    private peekToken(pos?: number): string {
        return this.lexer.peekK((pos || 0)).kind;
    }

    private peekTokenData(pos?: number): string {
        return this.lexer.peekK((pos || 0)).data as string;
    }

    private testToken(kind: string): boolean {
        return this.lexer.peekNext().kind === kind;
    }

    private testFollows(...kinds: string[]): boolean {
        for (let i = 0; i < kinds.length; ++i) {
            if (this.peekToken(i) !== kinds[i]) {
                return false;
            }
        }

        return true;
    }

    private consumeToken() {
        this.lexer.consumeToken();
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
        const td = this.lexer.peekNext().data as string;
        this.consumeToken();

        return td;
    }

    private ensureToken(kind: string, contextinfo: string): boolean {
        if (this.testToken(kind)) {
            return true;
        }
        else {
            this.recordExpectedError(this.lexer.peekNext(), kind, contextinfo);
            return false;
        }
    }

    private ensureAndConsumeToken(kind: string, contextinfo: string) {
        const ok = this.ensureToken(kind, contextinfo);
        this.consumeToken();

        return ok;
    }

    private scanToken(tok: string): number | undefined {
        let pos = 0;
        let tk = this.lexer.peekK(pos);
        while(tk.kind !== TokenStrings.EndOfStream) {
            if(tk.kind === tok) {
                return pos;
            }

            pos++;
            tk = this.lexer.peekK(pos);
        }

        return undefined;
    }

    private scanTokenOptions(...toks: string[]): number | undefined {
        let pos = 0;
        let tk = this.lexer.peekK(pos);
        while(tk.kind !== TokenStrings.EndOfStream) {
            if(toks.includes(tk.kind)) {
                return pos;
            }

            pos++;
            tk = this.lexer.peekK(pos);
        }

        return undefined;
    }

    private parseListOf<T>(contextinfobase: string, start: string, end: string, sep: string, fn: () => T): T[] {
        const closeparen = this.scanMatchingParens(start, end);

        const closepos = closeparen !== undefined ? this.lexer.peekK(closeparen).pos : this.lexer.currentState().epos;
        this.lexer.prepStateStackForNested("list-" + contextinfobase, closepos, undefined);

        let result: T[] = [];
        this.ensureAndConsumeToken(start, contextinfobase);
        while (!this.testAndConsumeTokenIf(end) && !this.testToken(TokenStrings.Recover) && !this.testToken(TokenStrings.EndOfStream)) {
            const nextcomma = this.scanToRecover(sep);
            const nextpos = nextcomma !== undefined ? this.lexer.peekK(nextcomma).pos : closepos;
            this.lexer.prepStateStackForNested("element-" + contextinfobase, nextpos, undefined);

            const v = fn();
            result.push(v);
            
            if(!this.testToken(end) && !this.testToken(sep)) {
                this.lexer.currentState().recover();
            }

            if(this.testToken(end)) {
                //great this is the happy path we will exit next iter
                this.lexer.popStateIntoParentOk();
            }
            else if(this.testToken(sep)) {
                //consume the sep
                this.consumeToken();

                //check for a stray ,) type thing at the end of the list -- if we have it report and then continue
                if(this.testToken(end)) {
                    this.recordErrorGeneral(this.lexer.peekNext().getSourceInfo(), "Stray , at end of list");
                }

                this.lexer.popStateIntoParentOk();
            }
            else {
                //ok all going wrong lets get out of here 
                this.lexer.popStateIntoParentOk();
                this.lexer.currentState().recover();
            }
        }

        this.lexer.popStateIntoParentOk();
        return result;
    }

    private parseBuildInfo(cb: BuildLevel): BuildLevel {
        if(this.testToken(KW_spec) || this.testToken(KW_debug) || this.testToken(KW_test) || this.testToken(KW_release) || this.testToken(KW_safety)) {
            return this.consumeTokenAndGetValue() as "spec" | "debug" | "test" | "release" | "safety";
        }
        else {
            return cb;
        }
    }

    ////
    //Misc parsing

    private parseIdentifierAccessChainHelperTypeTail(leadingscoper: boolean, currentns: NamespaceDeclaration, scopeTokens: string[]): {nsScope: NamespaceDeclaration, scopeTokens: string[], typeTokens: {tname: string, terms: TypeSignature[]}[]} {
        if(leadingscoper) {
            this.consumeToken();
        }
        const tsroot = this.peekTokenData();

        if(currentns.name === "Core" && (tsroot === "Result" || tsroot === "APIResult")) {
            this.consumeToken();
            const terms = this.parseTermList();

            if(!this.testToken(SYM_coloncolon)) {
                return {nsScope: currentns, scopeTokens: scopeTokens, typeTokens: [{tname: tsroot, terms: terms}]};
            }
            else {
                this.consumeToken();
                this.ensureToken(TokenStrings.IdentifierName, "type tail");
                const ttname = (this.testToken(TokenStrings.IdentifierName) ? this.consumeTokenAndGetValue() : "[error]");

                if(tsroot === "Result" && (ttname === "Ok" || ttname === "Err")) {
                    return {nsScope: currentns, scopeTokens: scopeTokens, typeTokens: [{tname: "Result", terms: terms}, {tname: ttname, terms: []}]};
                }
                else if(tsroot === "APIResult" && (ttname === "Rejected" || ttname === "Error" || ttname === "Failed" || ttname === "Success")) {
                    return {nsScope: currentns, scopeTokens: scopeTokens, typeTokens: [{tname: "APIResult", terms: terms}, {tname: ttname, terms: []}]};
                }
                else {
                    return {nsScope: currentns, scopeTokens: scopeTokens, typeTokens: [{tname: "error", terms: terms}]};
                }
            }
        }
        else {
            this.consumeToken();
            const terms = this.parseTermList();

            return {nsScope: currentns, scopeTokens: scopeTokens, typeTokens: [{tname: tsroot, terms: terms}]};
        }
    }

    private parseIdentifierAccessChainHelper(leadingscoper: boolean, currentns: NamespaceDeclaration, scopeTokens: string[]): {nsScope: NamespaceDeclaration, scopeTokens: string[], typeTokens: {tname: string, terms: TypeSignature[]}[]} | undefined {
        const nsroot = this.peekTokenData(leadingscoper ? 1 : 0);
        const hasterms = this.peekToken(leadingscoper ? 2 : 1) === SYM_langle;

        if(nsroot === "Core") {
            this.recordErrorGeneral(this.lexer.peekNext().getSourceInfo(), "Cannot shadow the Core namespace");
            return undefined;
        }

        const nns = currentns.subns.find((ns) => ns.name === nsroot);
        const nnt = currentns.declaredTypeNames.find((t) => t.name === nsroot);
        if(nns !== undefined && !hasterms) {
            if(leadingscoper) {
                this.consumeToken();
            }
            this.consumeToken();
            return this.parseIdentifierAccessChainHelper(this.testToken(SYM_coloncolon), nns, [...scopeTokens, nsroot]);
        }
        else if(nnt !== undefined) {
            return this.parseIdentifierAccessChainHelperTypeTail(this.testToken(SYM_coloncolon), currentns, scopeTokens);
        }
        else {
            return {nsScope: currentns, scopeTokens: scopeTokens, typeTokens: []};
        }
    }

    private parseIdentifierAccessChain(): {nsScope: NamespaceDeclaration, scopeTokens: string[], typeTokens: {tname: string, terms: TypeSignature[]}[]} | undefined {
        assert(isParsePhase_Enabled(this.currentPhase, ParsePhase_CompleteParse));

        const nsroot = this.peekTokenData();

        const coredecl = this.env.assembly.getToplevelNamespace("Core");
        if (nsroot === "Core") {
            this.consumeToken();
            if(this.testToken(SYM_coloncolon)) {
                return this.parseIdentifierAccessChainHelper(true, coredecl, ["Core"]);
            }
            else {
                return {nsScope: coredecl, scopeTokens: ["Core"], typeTokens: []};
            }
        }
        else if(coredecl.declaredNames.has(nsroot)) {
            return this.parseIdentifierAccessChainHelper(false, coredecl, []);
        }
        else if(this.env.currentNamespace.declaredNames.has(nsroot)) {
            return this.parseIdentifierAccessChainHelper(false, this.env.currentNamespace, []);
        }
        else if(this.env.currentNamespace.usings.find((nsuse) => nsuse.asns === nsroot) !== undefined) {
            const uns = (this.env.currentNamespace.usings.find((nsuse) => nsuse.asns === nsroot) as NamespaceUsing).fromns.ns;
            this.consumeToken();

            let iidx = 1;
            const rrns = this.env.assembly.getToplevelNamespace(uns[0]);
            while(rrns !== undefined && iidx < uns.length) {
                rrns.subns.find((sns) => sns.name === uns[iidx]);
                iidx++;
            }

            if(rrns === undefined) {
                return undefined;
            }

            if(this.testToken(SYM_coloncolon)) {
                return this.parseIdentifierAccessChainHelper(true, rrns, [nsroot]);
            }
            else {
                return {nsScope: rrns, scopeTokens: [nsroot], typeTokens: []};
            }
        }
        else {
            this.consumeToken();

            const tlns = this.env.assembly.getToplevelNamespace(nsroot);
            if(tlns === undefined) {
                return undefined;
            }
            else {
                if(this.testToken(SYM_coloncolon)) {
                    return this.parseIdentifierAccessChainHelper(true, tlns, [nsroot]);
                }
                else {
                    return {nsScope: tlns, scopeTokens: [nsroot], typeTokens: []};
                }
            }
        }
    }

    private tryNormalizeCoreType(corens: NamespaceDeclaration, typeTokens: {tname: string, terms: TypeSignature[]}[]): AbstractNominalTypeDecl | undefined {
        const tname = typeTokens[0].tname;
        const nnt = corens.typedecls.find((t) => t.name === typeTokens[0].tname);

        if(tname === "Result" || tname === "APIResult") {
            if(typeTokens.length === 1) {
                return nnt;
            }
            else {
                const extname = typeTokens[1].tname;
                if(tname === "Result") {
                    return (nnt as ResultTypeDecl).nestedEntityDecls.find((ned) => ned.name === extname);
                }
                else {
                    return (nnt as APIResultTypeDecl).nestedEntityDecls.find((ned) => ned.name === extname);
                }
            }
        }
        else {
            return nnt;
        }
    }

    private normalizeTypeNameChain(sinfo: SourceInfo, ns: NamespaceDeclaration, typeTokens: {tname: string, terms: TypeSignature[]}[]): [{name: string, type: TypeSignature}[], NamespaceTypedef | undefined, AbstractNominalTypeDecl | undefined] | undefined {
        const tydef = ns.typeDefs.find((t) => t.name === typeTokens[0].tname);
        if(tydef !== undefined) {
            if(typeTokens[0].terms.length !== tydef.terms.length) {
                this.recordErrorGeneral(sinfo, `Type ${tydef.name} expects ${tydef.terms.length} type arguments but got ${typeTokens[0].terms.length}`);
            };

            const rterms = typeTokens[0].terms.length === tydef.terms.length ? typeTokens[0].terms.map((t, i) => { 
                return {name: tydef.terms[i].name, type: t}; 
            }) : [];

            return [rterms, tydef, undefined];
        }
        
        const taskdef = ns.tasks.find((t) => t.name === typeTokens[0].tname);
        if(taskdef !== undefined) {
            if(typeTokens[0].terms.length !== taskdef.terms.length) {
                this.recordErrorGeneral(sinfo, `Task ${taskdef.name} expects ${taskdef.terms.length} type arguments but got ${typeTokens[0].terms.length}`);
            };

            const rterms = typeTokens[0].terms.length === taskdef.terms.length ? typeTokens[0].terms.map((t, i) => { 
                return {name: taskdef.terms[i].name, type: t}; 
            }) : [];

            return [rterms, undefined, taskdef];
        }

        //handle special Core types first
        if(ns.name === "Core") {
            const ndecl = this.tryNormalizeCoreType(ns, typeTokens);
            if(ndecl !== undefined) {
                if(typeTokens[0].terms.length !== ndecl.terms.length) {
                    this.recordErrorGeneral(sinfo, `Type ${ndecl.name} expects ${ndecl.terms.length} type arguments but got ${typeTokens[0].terms.length}`);
                };
    
                const rterms = typeTokens[0].terms.length === ndecl.terms.length ? typeTokens[0].terms.map((t, i) => { 
                    return {name: ndecl.terms[i].name, type: t}; 
                }) : [];

                return [rterms, undefined, ndecl];
            }
        }

        const nnt = ns.typedecls.find((t) => t.name === typeTokens[0].tname);
        if(nnt !== undefined) {
            if(typeTokens[0].terms.length !== nnt.terms.length) {
                this.recordErrorGeneral(sinfo, `Type ${nnt.name} expects ${nnt.terms.length} type arguments but got ${typeTokens[0].terms.length}`);
            };

            const rterms = typeTokens[0].terms.length === nnt.terms.length ? typeTokens[0].terms.map((t, i) => { 
                return {name: nnt.terms[i].name, type: t}; 
            }) : [];

            return [rterms, undefined, nnt];
        }

        return undefined;
    }

    private parseAttribute(): DeclarationAttibute {
        if(this.testToken(TokenStrings.DocComment)) {
            const docstr = this.consumeTokenAndGetValue();
            return new DeclarationAttibute("doc", [], docstr);
        }
        else {
            this.ensureToken(TokenStrings.Attribute, "attribute");
            const attr = this.consumeTokenAndGetValue();

            let args: {enumType: TypeSignature, tag: string}[] = [];
            if(this.testToken(SYM_lbrack)) {
                args = this.parseListOf<{enumType: TypeSignature, tag: string}>("attribute args", SYM_lparen, SYM_rparen, SYM_coma, () => {
                    const etype = this.parseTypeSignature();
                    this.ensureAndConsumeToken(SYM_coloncolon, "attribute args");

                    this.ensureToken(TokenStrings.IdentifierName, "attribute args");
                    const tag = this.consumeTokenAndGetValue();

                    return {enumType: etype, tag: tag};
                });
            }

            return new DeclarationAttibute(attr, args, undefined);
        }
    }

    private parseInvokeTermRestriction(): InvokeTemplateTypeRestriction  {
        this.ensureAndConsumeToken(SYM_lbrace, "template term restiction");
        this.ensureAndConsumeToken(KW_when, "template term restiction");
        
        const trl = this.parseListOf<InvokeTemplateTypeRestrictionClause>("template term restiction list", SYM_lbrace, SYM_rbrace, SYM_semicolon, () => {
            if(this.testToken(KW_type)) {
                this.consumeToken();
                this.ensureAndConsumeToken(SYM_lparen, "template term restiction");

                this.ensureToken(TokenStrings.IdentifierName, "template term restiction");
                const vname = this.testToken(TokenStrings.IdentifierName) ? this.consumeTokenAndGetValue() : "[error]";

                this.ensureAndConsumeToken(SYM_rparen, "template term restiction");
                this.ensureAndConsumeToken(SYM_arrow, "template term restiction");

                const tunify = this.parseTypeSignature();

                return new InvokeTemplateTypeRestrictionClauseUnify(vname, tunify);
            }
            else {
                const ts = this.parseTemplateTypeReference();
                this.ensureAndConsumeToken(SYM_at, "template term restiction");
                const subtype = this.parseTypeSignature();

                return new InvokeTemplateTypeRestrictionClauseSubtype(ts as TemplateTypeSignature, subtype);
            }
        });

        this.ensureAndConsumeToken(SYM_rbrace, "template term restiction");
        return new InvokeTemplateTypeRestriction(trl);
    }

    private parseInvokeTermRestrictionInfo(): InvokeTemplateTypeRestriction | undefined {
        if(!this.testToken(SYM_lbrace)) {
            return undefined;
        }
        else {
            return this.parseInvokeTermRestriction();
        }
    }

    private parsePreAndPostConditions(sinfo: SourceInfo, argnames: Set<string>, refParams: Set<string>, boundtemplates: Set<string>): [PreConditionDecl[], PostConditionDecl[]] {
        let preconds: PreConditionDecl[] = [];
        
        this.env.scope = new StandardScopeInfo([...argnames].map((v) => new LocalVariableDefinitionInfo(v, true)), boundtemplates, this.wellknownTypes.get("Bool") as TypeSignature);
        while (this.testToken(KW_requires)) {
            this.consumeToken();
            
            let tag: string | undefined = undefined;
            if(this.testAndConsumeTokenIf(SYM_lbrack)) {
                if(this.ensureToken(TokenStrings.ASCIIString, "requires tag")) {
                    tag = this.consumeTokenAndGetValue();
                }
                
                this.ensureAndConsumeToken(SYM_rbrack, "requires tag");
            }

            const level = this.parseBuildInfo(KW_release);
            const exp = this.parseExpression();

            preconds.push(new PreConditionDecl(this.env.currentFile, sinfo, tag, level, exp));

            this.ensureAndConsumeToken(SYM_semicolon, "requires");
        }
        this.env.scope = undefined;

        let postconds: PostConditionDecl[] = [];

        const refnames = [...refParams].map((v) => new LocalVariableDefinitionInfo("$" + v, true));
        this.env.scope = new StandardScopeInfo([...[...argnames].map((v) => new LocalVariableDefinitionInfo(v, true)), ...refnames, new LocalVariableDefinitionInfo("$return", true)], boundtemplates, this.wellknownTypes.get("Bool") as TypeSignature);
        
        while (this.testToken(KW_ensures)) {
            this.consumeToken();

            let tag: string | undefined = undefined;
            if(this.testAndConsumeTokenIf(SYM_lbrack)) {
                if(this.ensureToken(TokenStrings.ASCIIString, "requires tag")) {
                    tag = this.consumeTokenAndGetValue();
                }
                
                this.ensureAndConsumeToken(SYM_rbrack, "requires tag");
            }

            const level = this.parseBuildInfo(KW_release);
            const exp = this.parseExpression();

            postconds.push(new PostConditionDecl(this.env.currentFile, sinfo, tag, level, exp));

            this.ensureAndConsumeToken(SYM_semicolon, "ensures");
        }
        this.env.scope = undefined;

        return [preconds, postconds];
    }

    private parseSamples(sinfo: SourceInfo): InvokeExample[] {
        let samples: InvokeExample[] = [];
        while (this.testToken(KW_test) || this.testToken(KW_example)) {
            const istest = this.testToken(KW_test);
            this.consumeToken();

            if (this.testToken(TokenStrings.PathItem)) {
                const fp = this.consumeTokenAndGetValue();

                samples.push(new InvokeExampleDeclFile(this.env.currentFile, sinfo, istest, fp));
            }
            else {
                this.ensureToken(SYM_lbrace, "example");
                const examples = this.parseListOf<{args: Expression[], output: Expression}>("examples", SYM_lbrace, SYM_rbrace, SYM_semicolon, () => {
                    const args = this.parseListOf<Expression>("example args", SYM_lparen, SYM_rparen, SYM_coma, () => this.parseExpression());
                    this.ensureAndConsumeToken(SYM_bigarrow, "example");
                    const result = this.parseExpression();

                    return {args: args, output: result};
                });
                
                samples.push(new InvokeExampleDeclInline(this.env.currentFile, sinfo, istest, examples));
            }

            this.ensureAndConsumeToken(SYM_semicolon, "example");
        }

        return samples;
    }

    private parseInvokeSignatureParameter(autotypeok: boolean): FunctionParameter {
        const cinfo = this.lexer.peekNext().getSourceInfo();

        const isref = this.testAndConsumeTokenIf(KW_ref);
        const isspread = this.testAndConsumeTokenIf(SYM_dotdotdot);

        if(isref && isspread) {
            this.recordErrorGeneral(cinfo, "Cannot have a parameter that is both a reference and a spread");
        }

        const idok = this.ensureToken(TokenStrings.IdentifierName, "function parameter");
        const pname = idok ? this.consumeTokenAndGetValue() : "[error]";

        let ptype = this.env.SpecialAutoSignature;
        if(this.testAndConsumeTokenIf(SYM_colon)) {
            ptype = this.parseTypeSignature();
        }
        else {
            if(!autotypeok) {
                this.recordErrorGeneral(cinfo, "Missing type specifier -- auto typing is only supported for lambda parameter declarations");

                //maybe do a try parse type here in case someone just forgot the colon
                if(!this.testToken(SYM_coma) && !this.testToken(SYM_rparen)) {
                    ptype = this.parseTypeSignature();
                }
            }
        }

        return new FunctionParameter(pname, ptype, isref, isspread);
    }

    private parseInvokeSignatureParameters(cinfo: SourceInfo, autotypeok: boolean, implicitRefAllowed: boolean): FunctionParameter[] {
        const params = this.parseListOf<FunctionParameter>("function parameter list", SYM_lparen, SYM_rparen, SYM_coma, () => {
            return this.parseInvokeSignatureParameter(autotypeok)
        });
        
        if(params.length !== 0) {
            if(params.slice(0, -1).some((param) => param.isSpreadParam)) {
                this.recordErrorGeneral(cinfo, "Spread parameter must be the last parameter");
            }

            if(!implicitRefAllowed && params.some((param) => param.isRefParam)) {
                this.recordErrorGeneral(cinfo, "Cannot have more a reference parameter");
            }
        }

        return params;
    }

    private parseInvokeTemplateTermDecl(): InvokeTemplateTermDecl {
        this.ensureToken(TokenStrings.Template, "template term");
        const tname = this.consumeTokenAndGetValue();

        const isinferable = this.testAndConsumeTokenIf(SYM_question);

        let ttype = this.wellknownTypes.get("Any") as TypeSignature;
        if(this.testAndConsumeTokenIf(SYM_colon)) {
            ttype = this.parseTypeSignature();
        }

        return new InvokeTemplateTermDecl(tname, ttype, isinferable);
    }

    private parseInvokeTemplateTerms(): InvokeTemplateTermDecl[] { 
        let terms: InvokeTemplateTermDecl[] = [];
        if(this.testToken(SYM_langle)) {
            terms = this.parseListOf<InvokeTemplateTermDecl>("template terms", SYM_langle, SYM_rangle, SYM_coma, () => {
                return this.parseInvokeTemplateTermDecl();
            });
        }

        return terms;
    }

    private parseLambdaDecl(): LambdaDecl | undefined {
        const cinfo = this.lexer.peekNext().getSourceInfo();

        let isrecursive: "yes" | "no" | "cond" = "no";
        if(this.testToken(KW_recursive) || this.testToken(KW_recursive_q)) {
            isrecursive = this.testToken(KW_recursive) ? "yes" : "cond";
            this.consumeToken();
        }

        let ispred = false;
        let isfn = false;
        while(this.testToken(KW_pred) || this.testToken(KW_fn)) {
            ispred = this.testAndConsumeTokenIf(KW_pred);
            isfn = this.testAndConsumeTokenIf(KW_fn);
        }

        if(ispred && isfn) {
            this.recordErrorGeneral(this.lexer.peekNext(), "Lambda cannot be marked as both a pred and a fn");
        }
        if(!ispred && !isfn) {
            this.recordErrorGeneral(this.lexer.peekNext(), "Lambda must be either a pred or fn");
        }

        const okdecl = this.testToken(SYM_lparen);
        if(!okdecl) {
            return undefined;
        }

        const params: FunctionParameter[] = this.parseInvokeSignatureParameters(cinfo, true, true);

        const allTypedParams = params.every((param) => !(param.type instanceof AutoTypeSignature));
        const someTypedParams = params.some((param) => !(param.type instanceof AutoTypeSignature));

        if(!allTypedParams && someTypedParams) {
            this.recordErrorGeneral(cinfo, "Cannot have a mix of typed parameter with untyped parameters");
        }

        let resultInfo = this.env.SpecialAutoSignature;
        if (this.testAndConsumeTokenIf(SYM_colon)) {
            resultInfo = this.parseTypeSignature();
        }

        if(!this.testToken(SYM_bigarrow)) {
            this.recordExpectedError(this.lexer.peekNext(), SYM_bigarrow, "lambda declaration");
        }
        else {
            this.consumeToken();
        }
        
        const lambdaargs = params.map((param) => new LocalVariableDefinitionInfo(param.name, !param.isRefParam));
        const lambdaenv = this.env.pushLambdaScope(lambdaargs, (resultInfo instanceof AutoTypeSignature) ? undefined : resultInfo);
        const body = this.parseBody([], false, true);
        this.env.popLambdaScope();

        return new LambdaDecl(this.env.currentFile, cinfo, [], ispred ? "pred" : "fn", isrecursive, params, resultInfo, body, lambdaenv.capturedVars, !someTypedParams);
    }

    private parseFunctionInvokeDecl(functionkind: "namespace" | "predicate" | "errtest" | "chktest" | "typescope", attributes: DeclarationAttibute[], typeTerms: Set<string>): FunctionInvokeDecl | undefined {
        const cinfo = this.lexer.peekNext().getSourceInfo();

        let isrecursive: "yes" | "no" | "cond" = "no";
        if(this.testToken(KW_recursive) || this.testToken(KW_recursive_q)) {
            isrecursive = this.testToken(KW_recursive) ? "yes" : "cond";
            this.consumeToken();
        }

        let fkind: "function" | "predicate" | "chktest" | "errtest" = "function";
        if(functionkind === "predicate") { 
            fkind = "predicate";
            this.ensureAndConsumeToken(KW_predicate, "predicate declaration");
        }
        else if(functionkind === "errtest") {
            fkind = "errtest";
            this.ensureAndConsumeToken(KW_errtest, "errtest declaration");
        }
        else if(functionkind === "chktest") {
            fkind = "chktest";
            this.ensureAndConsumeToken(KW_chktest, "chktest declaration");
        }
        else {
            this.ensureAndConsumeToken(KW_function, "function declaration");
        }

        const termRestrictions = this.parseInvokeTermRestrictionInfo();

        this.ensureToken(TokenStrings.IdentifierName, "function name");
        const fname = this.testToken(TokenStrings.IdentifierName) ? this.consumeTokenAndGetValue() : "[error]";

        const terms = this.parseInvokeTemplateTerms();

        const okdecl = this.testToken(SYM_lparen);
        if(!okdecl) {
            this.recordErrorGeneral(cinfo, "Function declaration missing parameter list");
            return undefined;
        }

        const params: FunctionParameter[] = this.parseInvokeSignatureParameters(cinfo, false, true);
        
        let resultInfo = this.env.SpecialVoidSignature;
        if (this.testAndConsumeTokenIf(SYM_colon)) {
            resultInfo = this.parseTypeSignature();
        }

        const argNames = new Set<string>(params.map((param) => param.name));
        const cargs = params.map((param) => new LocalVariableDefinitionInfo(param.name, !param.isRefParam));
        const refparams = new Set<string>(params.filter((param) => param.isRefParam).map((param) => param.name));
        const boundtemplates = new Set<string>(...typeTerms, ...terms.map((term) => term.name));

        const [preconds, postconds] = this.parsePreAndPostConditions(cinfo, argNames, refparams, boundtemplates);
        const samples = this.parseSamples(cinfo);
    
        this.env.pushStandardFunctionScope(cargs, boundtemplates, resultInfo);
        const body = this.parseBody(attributes, functionkind === "predicate", false);
        this.env.popStandardFunctionScope();

        if(functionkind === "typescope") {
            return new TypeFunctionDecl(this.env.currentFile, cinfo, attributes, fname, isrecursive, params, resultInfo, body, terms, termRestrictions, preconds, postconds, samples);
        }
        else {
            return new NamespaceFunctionDecl(this.env.currentFile, cinfo, attributes, fname, isrecursive, params, resultInfo, body, terms, termRestrictions, preconds, postconds, samples, fkind);
        }
    }

    private parseMethodInvokeDecl(taskscope: boolean, attributes: DeclarationAttibute[], typeTerms: Set<string>): MethodDecl | TaskMethodDecl | undefined {
        const cinfo = this.lexer.peekNext().getSourceInfo();

        let isrecursive: "yes" | "no" | "cond" = "no";
        if(this.testToken(KW_recursive) || this.testToken(KW_recursive_q)) {
            isrecursive = this.testToken(KW_recursive) ? "yes" : "cond";
            this.consumeToken();
        }

        const isref = this.testAndConsumeTokenIf(KW_ref);
        this.ensureAndConsumeToken(KW_method, "method declaration");

        const termRestrictions = this.parseInvokeTermRestrictionInfo();

        this.ensureToken(TokenStrings.IdentifierName, "method name");
        const fname = this.testToken(TokenStrings.IdentifierName) ? this.consumeTokenAndGetValue() : "[error]";

        const terms = this.parseInvokeTemplateTerms();

        const okdecl = this.testToken(SYM_lparen);
        if(!okdecl) {
            this.recordErrorGeneral(cinfo, "Method declaration missing parameter list");
            return undefined;
        }

        const params: FunctionParameter[] = this.parseInvokeSignatureParameters(cinfo, false, !isref);
        
        let resultInfo = this.env.SpecialVoidSignature;
        if (this.testAndConsumeTokenIf(SYM_colon)) {
            resultInfo = this.parseTypeSignature();
        }

        const argNames = new Set<string>(params.map((param) => param.name));
        let cargs = params.map((param) => new LocalVariableDefinitionInfo(param.name, !param.isRefParam));
        const refparams = new Set<string>(params.filter((param) => param.isRefParam).map((param) => param.name));
        const boundtemplates = new Set<string>(...typeTerms, ...terms.map((term) => term.name));

        if(taskscope) {
            argNames.add("self");
            cargs = [new LocalVariableDefinitionInfo("self", !isref), ...cargs];
            if(isref) {
                refparams.add("self");
            }
        }
        else {
            argNames.add("this");
            cargs = [new LocalVariableDefinitionInfo("self", !isref), ...cargs];
            if(isref) {
                refparams.add("this");
            }
        }

        const [preconds, postconds] = this.parsePreAndPostConditions(cinfo, argNames, refparams, boundtemplates);
        const samples = this.parseSamples(cinfo);
    
        this.env.pushStandardFunctionScope(cargs, boundtemplates, resultInfo);
        const body = this.parseBody(attributes, false, false);
        this.env.popStandardFunctionScope();

        if(taskscope) {
            return new TaskMethodDecl(this.env.currentFile, cinfo, attributes, fname, isrecursive, params, resultInfo, body, terms, termRestrictions, preconds, postconds, samples, isref);
        }
        else {
            return new MethodDecl(this.env.currentFile, cinfo, attributes, fname, isrecursive, params, resultInfo, body, terms, termRestrictions, preconds, postconds, samples, isref);
        }
    }

    private parseActionInvokeDecl(attributes: DeclarationAttibute[], typeTerms: Set<string>): TaskActionDecl | undefined {
        const cinfo = this.lexer.peekNext().getSourceInfo();

        this.ensureAndConsumeToken(KW_action, "action declaration");

        const termRestrictions = this.parseInvokeTermRestrictionInfo();

        this.ensureToken(TokenStrings.IdentifierName, "action name");
        const fname = this.testToken(TokenStrings.IdentifierName) ? this.consumeTokenAndGetValue() : "[error]";

        const terms = this.parseInvokeTemplateTerms();

        const okdecl = this.testToken(SYM_lparen);
        if(!okdecl) {
            this.recordErrorGeneral(cinfo, "Action declaration missing parameter list");
            return undefined;
        }

        const params: FunctionParameter[] = this.parseInvokeSignatureParameters(cinfo, false, false);
        
        let resultInfo = this.env.SpecialVoidSignature;
        if (this.testAndConsumeTokenIf(SYM_colon)) {
            resultInfo = this.parseTypeSignature();
        }

        const argNames = new Set<string>(params.map((param) => param.name));
        let cargs = params.map((param) => new LocalVariableDefinitionInfo(param.name, !param.isRefParam));
        const refparams = new Set<string>(params.filter((param) => param.isRefParam).map((param) => param.name));
        const boundtemplates = new Set<string>(...typeTerms, ...terms.map((term) => term.name));

        argNames.add("self");
        cargs = [new LocalVariableDefinitionInfo("self", true), ...cargs];
        refparams.add("self");
    
        const [preconds, postconds] = this.parsePreAndPostConditions(cinfo, argNames, refparams, boundtemplates);
        const samples = this.parseSamples(cinfo);
    
        this.env.pushStandardFunctionScope(cargs, boundtemplates, resultInfo);
        const body = this.parseBody(attributes, false, false);
        this.env.popStandardFunctionScope();

        return new TaskActionDecl(this.env.currentFile, cinfo, attributes, fname, params, resultInfo, body, terms, termRestrictions, preconds, postconds, samples);
    }

    ////
    //Type parsing

    private parseTypeSignature(): TypeSignature {
        return this.parseOrCombinatorType();
    }

    private parseOrCombinatorType(): TypeSignature {
        const ltype = this.parseAndCombinatorType();
        if (!this.testToken(SYM_bar)) {
            return ltype;
        }
        else {
            const sinfo = this.lexer.peekNext().getSourceInfo();
            this.consumeToken();
            const rtype = this.parseOrCombinatorType();

            return new UnionTypeSignature(sinfo, ltype, rtype);
        }
    }

    private parseAndCombinatorType(): TypeSignature {
        const ltype = this.parseNoneableType();
        if (!this.testToken(SYM_amp)) {
            return ltype;
        }
        else {
            const sinfo = this.lexer.peekNext().getSourceInfo();
            this.consumeToken();
            const rtype = this.parseOrCombinatorType();

            return new AndTypeSignature(sinfo, ltype, rtype);
        }
    }

    private parseNoneableType(): TypeSignature {
        let roottype = this.parseBaseTypeReference();
        if(this.testAndConsumeTokenIf(SYM_question)) {
            roottype = new NoneableTypeSignature(roottype.sinfo, roottype);
        }
        return roottype;
    }

    private parseBaseTypeReference(): TypeSignature {
        switch (this.peekToken()) {
            case TokenStrings.Template: {
                return this.parseTemplateTypeReference();
            }
            case TokenStrings.IdentifierName: {
                const sinfo = this.lexer.peekNext().getSourceInfo();
                const idtype = this.peekTokenData();
                if(/[^A-Z].*/.test(idtype)) {
                    return this.parseNominalType();
                }
                else {
                    this.recordErrorGeneral(sinfo, `Invalid type reference "${idtype}"`);
                    return new ErrorTypeSignature(sinfo, undefined);
                }
            }
            case SYM_lbrack: {
                return this.parseTupleType();
            }
            case SYM_lbrace: {
                return this.parseRecordType();
            }
            case KW_fn:
            case KW_pred:
            case KW_recursive_q:
            case KW_recursive: {
                return this.parseLambdaType();
            }
            case SYM_lparen: {
                const sinfo = this.lexer.peekNext().getSourceInfo();
                const closeparen = this.scanMatchingParens(SYM_lparen, SYM_rparen);

                const closepos = closeparen !== undefined ? this.lexer.peekK(closeparen).pos : this.lexer.currentState().epos;
                this.lexer.prepStateStackForNested("paren-type", closepos, undefined);

                this.consumeToken();
                let ptype = this.parseTypeSignature();
                if(!this.testAndConsumeTokenIf(SYM_rparen)) {
                    ptype = this.completeEListTypeParse(sinfo, ptype, closeparen !== undefined);
                }
                else {
                    if(this.testToken(SYM_rparen)) {
                        this.consumeToken();
                    }
                    else {
                        if(closeparen !== undefined) {
                            this.lexer.currentState().recover();
                        }
                    }
                }

                return ptype;
            }
            default: {
                return new ErrorTypeSignature(this.lexer.peekNext().getSourceInfo(), undefined);
            }
        }
    }

    private parseTemplateTypeReference(): TypeSignature {
        const sinfo = this.lexer.peekNext().getSourceInfo();

        const tname = this.consumeTokenAndGetValue();
        return new TemplateTypeSignature(sinfo, tname);
    }

    private parseTermList(): TypeSignature[] {
        let terms: TypeSignature[] = [];
        if (this.testToken(SYM_langle)) {
            terms = this.parseListOf<TypeSignature>("template term list", SYM_langle, SYM_rangle, SYM_coma, () => {
                return this.parseTypeSignature();
            });
        }
        return terms;
    }

    private parseNominalType(): TypeSignature {
        const sinfo = this.lexer.peekNext().getSourceInfo();

        const nsr = this.parseIdentifierAccessChain();
        if(nsr === undefined) {
            return new ErrorTypeSignature(sinfo, undefined);
        }
        else if(nsr.typeTokens.length === 0) {
            return new ErrorTypeSignature(sinfo, new FullyQualifiedNamespace(nsr.scopeTokens));
        }
        else {
            const resolved = this.normalizeTypeNameChain(sinfo, nsr.nsScope, nsr.typeTokens);
            if(resolved === undefined) {
                return new ErrorTypeSignature(sinfo, nsr.nsScope.fullnamespace);
            }
            else {
                return new NominalTypeSignature(sinfo, nsr.scopeTokens, nsr.typeTokens, ...resolved);
            }
        }
    }

    private parseTupleType(): TypeSignature {
        const sinfo = this.lexer.peekNext().getSourceInfo();

        const entries = this.parseListOf<TypeSignature>("tuple type", SYM_lbrack, SYM_rbrack, SYM_coma, () => {
            return this.parseTypeSignature();
        });

        return new TupleTypeSignature(sinfo, entries);
    }

    private parseRecordType(): TypeSignature {
        const sinfo = this.lexer.peekNext().getSourceInfo();

        let pnames = new Set<string>();
        const entries = this.parseListOf<[string, TypeSignature]>("record type", SYM_lbrace, SYM_rbrace, SYM_coma, () => {
            this.ensureToken(TokenStrings.IdentifierName, "record type entry property name");

            const name = this.consumeTokenAndGetValue();
            if(pnames.has(name)) {
                this.recordErrorGeneral(this.lexer.peekNext(), `Duplicate property name ${name} in record type`);
            }
            pnames.add(name);

            this.ensureAndConsumeToken(SYM_colon, "record type property type");
            const rtype = this.parseTypeSignature();

            return [name, rtype];
        });

        return new RecordTypeSignature(sinfo, entries);
    }

    private parseLambdaType(): TypeSignature {
        const sinfo = this.lexer.peekNext().getSourceInfo();

        let isrecursive: "yes" | "no" | "cond" = "no";
        if(this.testToken(KW_recursive) || this.testToken(KW_recursive_q)) {
            isrecursive = this.testToken(KW_recursive) ? "yes" : "cond";
            this.consumeToken();
        }

        let name: "fn" | "pred" = "fn";
        if(this.testToken(KW_fn) && this.testToken(KW_pred)) {
            name = this.consumeTokenAndGetValue() as "fn" | "pred";
        }
        else {
            this.recordErrorGeneral(this.lexer.peekNext(), "Lambda type must be either a fn or pred");

            if(!this.testToken(SYM_lparen)) {
                this.consumeToken();
            }
        }

        const params = this.parseInvokeSignatureParameters(sinfo, false, false);

        this.ensureAndConsumeToken(SYM_arrow, "lambda type reference");
        const resultInfo = this.parseTypeSignature();

        return new LambdaTypeSignature(sinfo, isrecursive, name, params, resultInfo);
    }

    private completeEListTypeParse(sinfo: SourceInfo, ptype: TypeSignature, canrecover: boolean): TypeSignature {
        let rtypes = [ptype];

        while (!this.testAndConsumeTokenIf(SYM_rparen)) {
            const v = this.parseTypeSignature();
            rtypes.push(v);
            
            if(this.testToken(SYM_rparen)) {
                ; //great this is the happy path we will exit next iter
            }
            else if(this.testToken(SYM_coma)) {
                //consume the sep
                this.consumeToken();

                //check for a stray ,) type thing at the end of the list -- if we have it report and then continue
                if(this.testToken(SYM_rparen)) {
                    this.recordErrorGeneral(this.lexer.peekNext().getSourceInfo(), "Stray , at end of list");
                }
            }
            else {
                //error token check here -- we have a valid parse then assume a missing , and continue -- otherwise try to cleanup as best possible and continue
                //maybe this is where we want to do some tryParse stuff to recover as robustly as possible -- like in the TypeSpec list parse implementation

                if(!canrecover) {
                    break; //we can't scan to a known recovery token so just break and let it sort itself out
                }
                else {
                    this.lexer.currentState().recover();
                }
            }
        }

        return new EListTypeSignature(sinfo, rtypes);
    }

    ////
    //Expression parsing
    private parseBinderInfo(): string | undefined {
        if(!this.testToken(TokenStrings.IdentifierName)) {
            return undefined;
        }
        else {
            let vname = this.consumeTokenAndGetValue();
            this.consumeToken();

            if(/^\$[a-z_]/.test(vname)) {
                return vname;
            }
            else {
                this.recordErrorGeneral(this.lexer.peekNext(), "Binder name must start with $ and be lower case");
                return undefined;
            }
        }
    }

    private static generateITestBinderName(test: ITest | undefined, exp: Expression, binder: string | undefined): [boolean, string[]] {
        let bnames: string[] = [];
        let isimplicit = false;

        if(test !== undefined) {
            if(binder !== undefined) {
                bnames = [binder];
            }
            else if(exp instanceof AccessVariableExpression) {
                const vname = exp.srcname;
                if(!vname.startsWith("$")) {
                    bnames = ["$" + vname];
                }
            }
            else {
                bnames = ["$_"];
                isimplicit = true;
            }
        }

        return [isimplicit, bnames];
    }

    private parseMatchTypeGuard(): TypeSignature | undefined {
        if (this.testToken(KW_under)) {
            return undefined;
        }
        else {
            return this.parseTypeSignature();
        }
    }

    private parseSwitchLiteralGuard(): LiteralExpressionValue | undefined {
        if (this.testToken(KW_under)) {
            return undefined;
        }
        else {
            return this.parseLiteralExpression();
        }
    }

    private static generateMatchBinderName(exp: Expression, binder: string | undefined): [boolean, string[]] {
        let bnames: string[] = [];
        let isimplicit = false;

        if(binder !== undefined) {
            bnames = [binder];
        }
        else if(exp instanceof AccessVariableExpression) {
            const vname = exp.srcname;
            if(!vname.startsWith("$")) {
                bnames = ["$" + vname];
            }
        }
        else {
            bnames = ["$_"];
            isimplicit = true;
        }

        return [isimplicit, bnames];
    }

    private parseITest(): ITest | undefined {
        const isnot = this.testAndConsumeTokenIf(SYM_bang);

        if(this.testToken(SYM_langle)) {
            return this.parseITypeTest(isnot);
        }
        else if(this.testToken(SYM_lbrack)) {
            return this.parseILiteralTest(isnot);
        }
        else {
            if(this.testToken(KW_none)) {
                this.consumeToken();
                return new ITestNone(isnot);
            }
            else if(this.testToken(KW_some)) {
                this.consumeToken();
                return new ITestSome(isnot);
            }
            else if(this.testToken(KW_nothing)) {
                this.consumeToken();
                return new ITestNothing(isnot);
            }
            else if(this.testToken(KW_something)) {
                this.consumeToken();
                return new ITestSomething(isnot);
            }
            else if(this.testToken(KW_ok)) {
                this.consumeToken();
                return new ITestOk(isnot);
            }
            else if(this.testToken(KW_err)) {
                this.consumeToken();
                return new ITestErr(isnot);
            }
            else {
                this.recordErrorGeneral(this.lexer.peekNext(), "Expected ITest");
                return undefined;
            }
        }
    }

    private parseITypeTest(isnot: boolean): ITest {
        this.consumeToken();
        const ttype = this.parseTypeSignature();
        this.ensureAndConsumeToken(SYM_rangle, "ITest");

        return new ITestType(isnot, ttype);
    }

    private parseILiteralTest(isnot: boolean): ITest {
        this.consumeToken();
        const literal = this.parseLiteralExpression();
        this.ensureAndConsumeToken(SYM_rbrack, "ITest");

        return new ITestLiteral(isnot, literal);
    }

    private parseArguments(lparen: string, rparen: string, sep: string, refok: boolean, spreadok: boolean, mapargs: boolean, lambdaok: boolean): ArgumentList {
        const args = this.parseListOf<ArgumentValue>("argument list", lparen, rparen, sep, () => {
            if(this.testToken(KW_ref)) {
                if(!refok) {
                    this.recordErrorGeneral(this.lexer.peekNext(), "Cannot have a reference argument in this context");
                }
                this.consumeToken();
                const exp = this.parseExpression();
                if(!(exp instanceof AccessVariableExpression)) {
                    this.recordErrorGeneral(exp.sinfo, "Expected variable as target in ref argument");
                }

                return new RefArgumentValue(exp as AccessVariableExpression);
            }
            else if(this.testToken(SYM_dotdotdot)) {
                if(!spreadok) {
                    this.recordErrorGeneral(this.lexer.peekNext(), "Cannot have a spread argument in this context");
                }
                this.consumeToken();
                const exp = this.parseExpression();

                return new SpreadArgumentValue(exp);
            }
            else if(this.testFollows(TokenStrings.IdentifierName, SYM_eq)) {
                const name = this.consumeTokenAndGetValue();
                this.consumeToken();
                const exp = this.parseExpression();

                return new NamedArgumentValue(name, exp);
            }
            else {
                let exp: Expression;
                if(mapargs) {
                    exp = this.parseMapEntryConstructorExpression();
                }
                else if(lambdaok) {
                    exp = this.parseLambdaOkExpression();
                }
                else {
                    exp = this.parseExpression();
                }
                
                return new PositionalArgumentValue(exp);
            }
        });

        const namedParams = args.filter((arg) => arg instanceof NamedArgumentValue).map((arg) => (arg as NamedArgumentValue).name);
        const duplicateNames = namedParams.find((name, index) => namedParams.indexOf(name) !== index);
        if(duplicateNames !== undefined) {
            this.recordErrorGeneral(this.lexer.peekNext(), `Duplicate argument name ${duplicateNames}`);
        }

        const multiplerefs = args.filter((arg) => arg instanceof RefArgumentValue).length > 1;
        if(multiplerefs) {
            this.recordErrorGeneral(this.lexer.peekNext(), "Cannot have multiple reference arguments");
        }

        const spreadidx = args.findIndex((arg, index) => arg instanceof SpreadArgumentValue && index !== args.length - 1);
        const badspread = spreadidx !== -1 && args.slice(spreadidx).some((arg) => !(arg instanceof NamedArgumentValue));
        if(badspread) {
            this.recordErrorGeneral(this.lexer.peekNext(), "Spread argument must be the last argument");
        }

        return new ArgumentList(args);
    }

    private parseRecursiveAnnotation(): RecursiveAnnotation {
        let recursive: "yes" | "no" | "cond" = "no";
        
        this.consumeToken();
        if (!this.testToken(KW_recursive) && !this.testToken(KW_recursive_q)) {
            this.recordErrorGeneral(this.lexer.peekNext(), "Expected recursive annotation");
        }

        recursive = this.testToken("recursive") ? "yes" : "cond";
        this.consumeToken();

        this.ensureAndConsumeToken(SYM_rbrack, "recursive annotation");
         
        return recursive;
    }
    
    private parseLambdaTerm(): Expression {
        const sinfo = this.lexer.peekNext().getSourceInfo();

        const ldecl = this.parseLambdaDecl();
        if(ldecl === undefined) {
            return new ErrorExpression(sinfo, undefined, undefined);
        }

        ldecl.captureVarSet.forEach((v) => {
            this.env.useVariable(v);
        });

        return new ConstructorLambdaExpression(sinfo, ldecl);
    }

    private parseLiteralExpression(): LiteralExpressionValue {
        this.env.pushStandardFunctionScope([], this.env.getScope().boundtemplates, undefined);        
        const exp = this.parseExpression();
        this.env.popStandardFunctionScope();

        if(!exp.isLiteralExpression()) {
            this.recordErrorGeneral(exp.sinfo, "Expected literal expression")
        }

        return new LiteralExpressionValue(exp);
    }

    private parseConstExpression(etype: TypeSignature | undefined): ConstantExpressionValue {
        this.env.pushStandardFunctionScope([], this.env.getScope().boundtemplates, etype);
        this.env.pushBinderUnknownInConstantExpressionScope();
        const exp = this.parseExpression();
        const usedbinds = this.env.popBinderUnknownInConstantExpressionScope();
        this.env.popStandardFunctionScope();

        return new ConstantExpressionValue(exp, new Set<string>(...usedbinds));
    }

    private static isTaggedLiteral(val: string): boolean {
        return val.endsWith("_");
    }

    private processTaggedLiteral(val: string): [string, TypeSignature] {
        const vval = val.slice(0, val.length - 1);
        const ttype = this.parseTypeSignature();
        return [vval, ttype];
    }

    private processSimplyTaggableLiteral(sinfo: SourceInfo, tag: ExpressionTag, val: string): Expression {
        if(!Parser.isTaggedLiteral(val)) {
            return new LiteralSimpleExpression(tag, sinfo, val);
        }
        else {
            const [vval, ttype] = this.processTaggedLiteral(val);
            return new LiteralTypeDeclValueExpression(sinfo, new LiteralSimpleExpression(tag, sinfo, vval), ttype);
        }
    }

    private parseNamespaceScopedFirstExpression(nspace: NamespaceDeclaration): Expression {
        const sinfo = this.lexer.peekNext().getSourceInfo();

        this.ensureAndConsumeToken(SYM_coloncolon, "namespace scoped expression");
        this.ensureToken(TokenStrings.IdentifierName, "namespace scoped expression");

        const idname = this.consumeTokenAndGetValue();

        const constOpt = nspace.consts.find((c) => c.name === idname);
        const funOpt = nspace.functions.find((f) => f.name === idname);
        if(constOpt) {
            return new AccessNamespaceConstantExpression(sinfo, nspace.fullnamespace, idname);
        }
        else if(funOpt) {
            assert(false, "Not implemented -- parseNamespaceScopedFirstExpression");
        }
        else {
            this.recordErrorGeneral(sinfo, `Name '${nspace.fullnamespace.emit()}::${idname}' is not defined in this context`);
            return new ErrorExpression(sinfo, {ns: nspace, typeopt: undefined}, undefined);
        }
    }

    private parseTypeScopedFirstExpression(access: {nsScope: NamespaceDeclaration, scopeTokens: string[], typeTokens: {tname: string, terms: TypeSignature[]}[]}): Expression {
        assert(false, "Not implemented -- parseTypeScopedFirstExpression");
    }

    private parseIdentifierFirstExpression(): Expression {
        const sinfo = this.lexer.peekNext().getSourceInfo();
        if (this.peekTokenData().startsWith("$")) {
            const idname = this.consumeTokenAndGetValue();
            
            const scopename = this.env.useVariable(idname);
            if(scopename !== undefined) {
                return new AccessVariableExpression(sinfo, idname, scopename[0], scopename[1]);
            }
            else {
                this.recordErrorGeneral(sinfo, `Variable '${idname}' is not defined in this context`);
                return new ErrorExpression(sinfo, undefined, undefined);
            }
        }
        else if (this.env.identifierResolvesAsVariable(this.peekTokenData())) {
            const idname = this.consumeTokenAndGetValue();
            
            const scopename = this.env.useVariable(idname);
            if(scopename !== undefined) {
                return new AccessVariableExpression(sinfo, idname, scopename[0], scopename[1]);
            }
            else {
                this.recordErrorGeneral(sinfo, `Variable '${idname}' is not defined in this context`);
                return new ErrorExpression(sinfo, undefined, undefined);
            }
        }
        else {
            const access = this.parseIdentifierAccessChain();
            if(access === undefined) {
                this.recordErrorGeneral(sinfo, "Invalid expression -- could not resolve name");
                return new ErrorExpression(sinfo, undefined, undefined);
            }

            if(access.typeTokens.length === 0) {
                return this.parseNamespaceScopedFirstExpression(access.nsScope);
            }
            else {
                return this.parseTypeScopedFirstExpression(access);
            }
        }
    }

    private parsePrimaryExpression(): Expression {
        const sinfo = this.lexer.peekNext().getSourceInfo();

        const tk = this.peekToken();
        if (tk === KW_none) {
            this.consumeToken();
            return new LiteralSingletonExpression(ExpressionTag.LiteralNoneExpression, sinfo, "none");
        }
        else if (tk === KW_nothing) {
            this.consumeToken();
            return new LiteralSingletonExpression(ExpressionTag.LiteralNothingExpression, sinfo, "nothing");
        }
        else if (tk === KW_true || tk === KW_false) {
            this.consumeToken();
            return new LiteralSimpleExpression(ExpressionTag.LiteralBoolExpression, sinfo, tk);
        }
        else if(tk === TokenStrings.TaggedBoolean) {
            const bstr = this.consumeTokenAndGetValue();
            const [vval, ttype] = this.processTaggedLiteral(bstr);
            return new LiteralTypeDeclValueExpression(sinfo, new LiteralSimpleExpression(ExpressionTag.LiteralBoolExpression, sinfo, vval), ttype);
        }
        else if(tk === TokenStrings.NumberinoInt || tk === TokenStrings.NumberinoFloat) {
            this.consumeToken();
            this.recordErrorGeneral(sinfo, "Un-annotated numeric literals are not supported");
            return new ErrorExpression(sinfo, undefined, undefined);
        }
        else if(tk === TokenStrings.TaggedNumberinoInt) {
            const istr = this.consumeTokenAndGetValue();
            const [vval, ttype] = this.processTaggedLiteral(istr);
            return new LiteralTypeDeclIntegralValueExpression(sinfo, vval, ttype);
        }
        else if(tk === TokenStrings.TaggedNumberinoFloat) {
            const fstr = this.consumeTokenAndGetValue();
            const [vval, ttype] = this.processTaggedLiteral(fstr);
            return new LiteralTypeDeclFloatPointValueExpression(sinfo, vval, ttype);
        }
        else if(tk === TokenStrings.TaggedNumberinoRational) {
            const rstr = this.consumeTokenAndGetValue();
            const [vval, ttype] = this.processTaggedLiteral(rstr);
            return new LiteralTypeDeclValueExpression(sinfo, new LiteralSimpleExpression(ExpressionTag.LiteralRationalExpression, sinfo, vval + "R"), ttype);
        }
        else if (tk === TokenStrings.Nat) {
            const istr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralNatExpression, istr);
        }
        else if (tk === TokenStrings.Int) {
            const istr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralIntExpression, istr);
        }
        else if(tk === TokenStrings.BigNat) {
            const istr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralBigNatExpression, istr);
        }
        else if (tk === TokenStrings.BigInt) {
            const istr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralBigIntExpression, istr);
        }
        else if (tk === TokenStrings.Rational) {
            const rstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralRationalExpression, rstr);
        }
        else if (tk === TokenStrings.Float) {
            const fstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralFloatExpression, fstr);
        }
        else if (tk === TokenStrings.Decimal) {
            const fstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralDecimalExpression, fstr);
        }
        else if(tk === TokenStrings.DecimalDegree) {
            const dstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralDecimalDegreeExpression, dstr);
        }
        else if(tk === TokenStrings.LatLong) {
            const llstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralLatLongCoordinateExpression, llstr);
        }
        else if(tk === TokenStrings.Complex) {
            const cstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralComplexNumberExpression, cstr);
        }
        else if(tk === TokenStrings.ByteBuffer) {
            const bbstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralByteBufferExpression, bbstr);
        }
        else if(tk === TokenStrings.UUIDValue) {
            const ustr = this.consumeTokenAndGetValue();
            const tag = ustr.startsWith("uuid4{") ? ExpressionTag.LiteralUUIDv4Expression : ExpressionTag.LiteralUUIDv7Expression;
            return this.processSimplyTaggableLiteral(sinfo, tag, ustr);
        }
        else if(tk === TokenStrings.ShaHashcode) {
            const hstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralSHAContentHashExpression, hstr);
        }
        else if(tk === TokenStrings.DateTime) {
            const dstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralDateTimeExpression, dstr);
        }
        else if(tk === TokenStrings.UTCDateTime) {
            const dstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralUTCDateTimeExpression, dstr);
        }
        else if(tk === TokenStrings.PlainDate) {
            const dstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralPlainDateExpression, dstr);
        }
        else if(tk === TokenStrings.PlainTime) {
            const tstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralPlainTimeExpression, tstr);
        }
        else if(tk === TokenStrings.LogicalTime) {
            const tstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralLogicalTimeExpression, tstr);
        }
        else if(tk === TokenStrings.TickTime) {
            const tstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralTickTimeExpression, tstr);
        }
        else if(tk === TokenStrings.Timestamp) {
            const dstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralISOTimeStampExpression, dstr);
        }
        else if(tk === TokenStrings.DeltaDateTime) {
            const dstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralDeltaDateTimeExpression, dstr);
        }
        else if(tk === TokenStrings.DeltaPlainDate) {
            const dstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralDeltaPlainDateExpression, dstr);
        }
        else if(tk === TokenStrings.DeltaPlainTime) {
            const tstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralDeltaPlainTimeExpression, tstr);
        }
        else if(tk === TokenStrings.DeltaTimestamp) {
            const dstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralDeltaISOTimeStampExpression, dstr);
        }
        else if(tk === TokenStrings.DeltaSeconds) {
            const dstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralDeltaSecondsExpression, dstr);
        }
        else if(tk === TokenStrings.DeltaTickTime) {
            const dstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralDeltaTickExpression, dstr);
        }
        else if(tk === TokenStrings.DeltaLogicalTime) {
            const dstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralDeltaLogicalExpression, dstr);
        }
        else if(tk === TokenStrings.Regex) {
            const rstr = this.consumeTokenAndGetValue();
            return new LiteralRegexExpression(rstr.endsWith("/") ? ExpressionTag.LiteralUnicodeRegexExpression : ExpressionTag.LiteralASCIIRegexExpression, sinfo, rstr);
        }
        else if(tk === TokenStrings.String) {
            const sstr = this.consumeTokenAndGetValue();
            if(sstr.endsWith("_")) {
                const vval = sstr.slice(0, sstr.length - 1);
                const ttype = this.parseTypeSignature();
                return new LiteralTypeDeclValueExpression(sinfo, new LiteralSimpleExpression(ExpressionTag.LiteralStringExpression, sinfo, vval), ttype);
            }
            else if(sstr.endsWith("[OF]")) {
                const vval = sstr.slice(0, sstr.length - "[OF]".length);
                const oftype = this.parseTypeSignature();
                return new LiteralTypedStringExpression(ExpressionTag.LiteralTypedStringExpression, sinfo, vval, oftype);
            }
            else {
                return new LiteralSimpleExpression(ExpressionTag.LiteralStringExpression, sinfo, sstr);
            }
        }
        else if(tk === TokenStrings.ASCIIString) {
            const sstr = this.consumeTokenAndGetValue();
            if(sstr.endsWith("_")) {
                const vval = sstr.slice(0, sstr.length - 1);
                const ttype = this.parseTypeSignature();
                return new LiteralTypeDeclValueExpression(sinfo, new LiteralSimpleExpression(ExpressionTag.LiteralASCIIStringExpression, sinfo, vval), ttype);
            }
            else if(sstr.endsWith("[OF]")) {
                const vval = sstr.slice(0, sstr.length - "[OF]".length);
                const oftype = this.parseTypeSignature();
                return new LiteralTypedStringExpression(ExpressionTag.LiteralASCIITypedStringExpression, sinfo, vval, oftype);
            }
            else {
                return new LiteralSimpleExpression(ExpressionTag.LiteralASCIIStringExpression, sinfo, sstr);
            }
        }
        else if(tk === TokenStrings.TemplateString) {
            const sstr = this.consumeTokenAndGetValue();
            return new LiteralTemplateStringExpression(ExpressionTag.LiteralTemplateStringExpression, sinfo, sstr);
        }
        else if(tk === TokenStrings.TemplateASCIIString) {
            const sstr = this.consumeTokenAndGetValue();
            return new LiteralTemplateStringExpression(ExpressionTag.LiteralASCIITemplateStringExpression, sinfo, sstr);
        }
        else if(tk === TokenStrings.PathItem) {
            const sstr = this.consumeTokenAndGetValue();

            let ptag = ExpressionTag.LiteralPathExpression;
            if(!sstr.startsWith("\\")) {
                ptag = sstr.startsWith("g") ? ExpressionTag.LiteralPathGlobExpression : ExpressionTag.LiteralPathFragmentExpression;
            }

            if(sstr.endsWith("_")) {
                const vval = sstr.slice(0, sstr.length - 1);
                const ttype = this.parseTypeSignature();
                return new LiteralTypeDeclValueExpression(sinfo, new LiteralPathExpression(ptag, sinfo, vval, undefined), ttype);
            }
            else if(sstr.endsWith("[OF]")) {
                const vval = sstr.slice(0, sstr.length - "[OF]".length);
                const oftype = this.parseTypeSignature();
                return new LiteralPathExpression(ptag, sinfo, vval, oftype);
            }
            else {
                return new LiteralPathExpression(ptag, sinfo, sstr, undefined);
            }
        }
        else if (tk === KW_this) {
            this.consumeToken();

            const scopename = this.env.useVariable("this");
            if(scopename !== undefined) {
                return new AccessVariableExpression(sinfo, "this", scopename[0], scopename[1]);
            }
            else {
                this.recordErrorGeneral(sinfo, "Variable 'this' is not defined in this context");
                return new ErrorExpression(sinfo, undefined, undefined);
            }
        }
        else if (tk === KW_self) {
            assert(false, "Need to handle any self cases");
        }
        /*
        else if (tk === KW_ok || tk === KW_err || tk === KW_something || tk === KW_result) {
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

            return [new SpecialConstructorExpression(sinfo, tk, arg), false];
        }
        else if (tk === KW_env) {
            this.ensureTaskOpOk();
            this.consumeToken();

            let opttype = this.m_penv.SpecialStringSignature;
            if(this.testAndConsumeTokenIf(SYM_le)) {
                opttype = this.parseTypeSignature();
                this.ensureAndConsumeToken(SYM_ge, "");
            }

            const isNoneMode = this.testAndConsumeTokenIf(SYM_question);

            this.ensureAndConsumeToken(SYM_lbrack, "environment access");
            this.ensureToken(TokenStrings.String, "environment access");
            const keyname = this.consumeTokenAndGetValue();
            this.ensureToken(SYM_rbrack, "environment access");

            return [new AccessEnvValueExpression(sinfo, keyname, opttype, isNoneMode), false];
        }
        else if (tk === KW_ref && this.peekToken(1) === TokenStrings.Identifier && this.peekTokenData(1) === "self") {
            this.ensureTaskOpOk();
            this.consumeToken();
            this.consumeToken();

            this.ensureAndConsumeToken(SYM_dot, "self field access");
            this.ensureNotToken(TokenStrings.Identifier, "self field access");
            const sfname = this.consumeTokenAndGetValue();

            const targs = this.testToken(SYM_le) ? this.parseTemplateArguments() : [];
            const args = this.parseArguments(SYM_lparen, SYM_rparen);

            return [new TaskSelfActionExpression(sinfo, sfname, targs, args, true), false];
        }
        else if (tk === TokenStrings.Identifier || this.testFollows(KW_ref, TokenStrings.Identifier)) {
            const refstr = this.testAndConsumeTokenIf(KW_ref);
            let namestr = this.consumeTokenAndGetValue();

            const isvar = this.m_penv.isVarDefinedInAnyScope(namestr) || namestr === "this" || namestr.startsWith("$");
            if (isvar) {
                const istr = this.m_penv.useLocalVar(namestr);

                if(refstr && (this.testToken(SYM_lbrack) || this.testToken(SYM_lparen))) {
                    this.raiseError(line, "cannot use ref on lambda invoke");
                }

                if (this.testToken(SYM_lbrack)) {
                    const rec = this.parseRecursiveAnnotation();
                    const args = this.parseArguments(SYM_lparen, SYM_rparen);

                    return [new PCodeInvokeExpression(sinfo, istr, rec, args), false];
                }
                else if (this.testToken(SYM_lparen)) {
                    const args = this.parseArguments(SYM_lparen, SYM_rparen);

                    return [new PCodeInvokeExpression(sinfo, istr, "no", args), false];
                }
                else {
                    return [new AccessVariableExpression(sinfo, istr), refstr];
                }
            }
            else {
                const tryfunctionns = this.m_penv.tryResolveNamespace(undefined, namestr);
                if (tryfunctionns === undefined) {
                    this.raiseError(line, `Cannot resolve name "${namestr}"`);
                }

                if(refstr) {
                    this.raiseError(line, "cannot use ref on namespace invoke");
                }

                const targs = this.testToken(SYM_le) ? this.parseTemplateArguments() : [];
                const rec = this.testToken(SYM_lbrack) ? this.parseRecursiveAnnotation() : "no";
                const args = this.parseArguments(SYM_lparen, SYM_rparen);

                return [new CallNamespaceFunctionOrOperatorExpression(sinfo, tryfunctionns as string, namestr, targs, rec, args), false];
            }
        }
        else if (tk === KW_fn || this.testFollows(KW_recursive, KW_fn) || this.testFollows(KW_recursive_q, KW_fn) || tk === KW_pred || this.testFollows(KW_recursive, KW_pred) || this.testFollows(KW_recursive_q, KW_pred)) {
            return [this.parsePCodeTerm(), false];
        }
        else if (tk === SYM_lparen && !this.checkTypeScopeBasedExpressionFollowsParens()) {
            try {
                this.setRecover(this.scanMatchingParens(SYM_lparen, SYM_rparen));

                this.consumeToken();
                const exp = this.parseExpression();
                this.ensureAndConsumeToken(SYM_rparen, "(Exp _<- Missing \")\"?");

                this.clearRecover();
                return [exp, false];
            }
            catch (ex) {
                this.processRecover();
                return [new InvalidExpression(sinfo), false];
            }
        }
        else if (this.testToken(SYM_lbrack)) {
            const args = this.parseArguments(SYM_lbrack, SYM_rbrack);
            return [new ConstructorTupleExpression(sinfo, args), false];
        }
        else if  (this.testToken(SYM_lbrace)) {
            const args = this.parseArgumentsNamed(SYM_lbrace, SYM_rbrace).sort((a, b) => ((a.name !== b.name) ? (a.name < b.name ? -1 : 1) : 0));
            return [new ConstructorRecordExpression(sinfo, args.map((nn) => {
                return {property: nn.name, value: nn.value};
            })), false];
        }
        else if (this.testToken(SYM_land) || this.testToken(SYM_lor)) {
            const op = this.consumeTokenAndGetValue() as "/\\" | "\\/";
            const args = this.parseArguments(SYM_lparen, SYM_rparen);
            if(op === SYM_land) {
                return [new LogicActionAndExpression(sinfo, args), false];
            }
            else {
                return [new LogicActionOrExpression(sinfo, args), false];
            }
        }
        else if (this.testFollows(TokenStrings.Namespace, SYM_coloncolon, TokenStrings.Identifier)) {
            //it is a namespace access of some type
            let ns: string | undefined = this.consumeTokenAndGetValue();
            this.consumeToken();
            const name = this.consumeTokenAndGetValue();

            if(ns === "Task" && (name === "getTaskID" || name === "isCanceled")) {
                this.ensureTaskOpOk();

                if(name === "getTaskID") {
                    return [new TaskGetIDExpression(sinfo), false];
                }
                else {
                    return [new TaskCancelRequestedExpression(sinfo), false];
                }
            }
            else {
                ns = this.m_penv.tryResolveNamespace(ns, name);
                if (ns === undefined) {
                    ns = "[Unresolved Namespace]";
                }

                if (!this.testToken(SYM_le) && !this.testToken(SYM_lbrack) && !this.testToken(SYM_lparen)) {
                    //just a constant access
                    return [new AccessNamespaceConstantExpression(sinfo, ns, name), false];
                }
                else {
                    const targs = this.testToken(SYM_le) ? this.parseTemplateArguments() : [];
                    const rec = this.testToken(SYM_lbrack) ? this.parseRecursiveAnnotation() : "no";
                    const args = this.parseArguments(SYM_lparen, SYM_rparen);

                    return [new CallNamespaceFunctionOrOperatorExpression(sinfo, ns, name, targs, rec, args), false];
                }
            }
        }
        else if (this.testFollows(TokenStrings.Namespace, SYM_hash, TokenStrings.Identifier)) {
            //it is a namespace access of some formatter info
            let ns: string | undefined = this.consumeTokenAndGetValue();
            this.consumeToken();
            const name = this.consumeTokenAndGetValue();

            return [new AccessFormatInfoExpression(sinfo, ns, name), false];
        }
        else {
            if(this.testToken(TokenStrings.Numberino)) {
                this.raiseError(this.getCurrentLine(), `expected numeric specifier, [i, n, I, N, f, d, R], on literal but got naked ${this.peekTokenData()}`)
            }
            const ttype = this.parseTypeSignature();

            if (this.testFollows(SYM_coloncolon, TokenStrings.Identifier)) {
                this.consumeToken();
                const name = this.consumeTokenAndGetValue();
                if (!this.testToken(SYM_le) && !this.testToken(SYM_lbrack) && !this.testToken(SYM_lparen) && !this.testToken(SYM_lbrace)) {
                    //just a static access
                    return [new AccessStaticFieldExpression(sinfo, ttype, name), false];
                }
                else {
                    const targs = this.testToken(SYM_le) ? this.parseTemplateArguments() : [];
                    const rec = this.testToken(SYM_lbrack) ? this.parseRecursiveAnnotation() : "no";
                    const args = this.parseArguments(SYM_lparen, SYM_rparen);
                    return [new CallStaticFunctionExpression(sinfo, ttype, name, targs, rec, args), false];
                }
            }
            else if (this.testFollows(SYM_lbrace)) {
                return [this.parseConstructorPrimary(ttype), false];
            }
            else {
                //
                //TODO: maybe a better error here -- slice the string at the position...
                //
                this.raiseError(line, `Unknown token sequence in parsing expression -- ${tk}`);
                return [new InvalidExpression(sinfo), false];
            }
        }
        */
        else if(tk === SYM_lparen) {
            const closeparen = this.scanMatchingParens(SYM_lparen, SYM_rparen);

            const closepos = closeparen !== undefined ? this.lexer.peekK(closeparen).pos : this.lexer.currentState().epos;
            this.lexer.prepStateStackForNested("paren-type", closepos, undefined);

            this.consumeToken();
            let exp = this.parseExpression();
            if(!this.testAndConsumeTokenIf(SYM_rparen)) {
                exp = this.completeEListConstructorParse(sinfo, exp, closeparen !== undefined);
            }
            else {
                if(this.testToken(SYM_rparen)) {
                    this.consumeToken();
                }
                else {
                    if(closeparen !== undefined) {
                        this.lexer.currentState().recover();
                    }
                }
            }

            return exp;
        }
        else if (tk === TokenStrings.IdentifierName) {
            return this.parseIdentifierFirstExpression();
        }
        else {
            this.recordErrorGeneral(sinfo, `Unexpected token in expression -- ${tk}`);
            return new ErrorExpression(sinfo, undefined, undefined);
        }
    }

    private completeEListConstructorParse(sinfo: SourceInfo, exp: Expression, canrecover: boolean): Expression {
        let exps = [new PositionalArgumentValue(exp)];

        while (!this.testAndConsumeTokenIf(SYM_rparen)) {
            const v = this.parseExpression();
            exps.push(new PositionalArgumentValue(v));
            
            if(this.testToken(SYM_rparen)) {
                ; //great this is the happy path we will exit next iter
            }
            else if(this.testToken(SYM_coma)) {
                //consume the sep
                this.consumeToken();

                //check for a stray ,) type thing at the end of the list -- if we have it report and then continue
                if(this.testToken(SYM_rparen)) {
                    this.recordErrorGeneral(this.lexer.peekNext().getSourceInfo(), "Stray , at end of list");
                }
            }
            else {
                //error token check here -- we have a valid parse then assume a missing , and continue -- otherwise try to cleanup as best possible and continue
                //maybe this is where we want to do some tryParse stuff to recover as robustly as possible -- like in the TypeSpec list parse implementation

                if(!canrecover) {
                    break; //we can't scan to a known recovery token so just break and let it sort itself out
                }
                else {
                    this.lexer.currentState().recover();
                }
            }
        }

        return new ConstructorEListExpression(sinfo, new ArgumentList(exps));
    }

    private parsePostfixExpression(): Expression {
        let rootexp = this.parsePrimaryExpression();

        let ops: PostfixOperation[] = [];
        while (true) {
            const sinfo = this.lexer.peekNext().getSourceInfo();

            if(this.testToken(SYM_question)) {
                this.consumeToken();

                const ttest = this.parseITest();
                if(ttest !== undefined) {
                    ops.push(new PostfixIsTest(sinfo, ttest));
                }
            }
            else if(this.testToken(SYM_at)) {
                this.consumeToken();
                
                const ttest = this.parseITest();
                if(ttest !== undefined) {
                    ops.push(new PostfixAsConvert(sinfo, ttest));
                }
            }
            /*
            else if (this.testToken(SYM_dot)) {
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

                    if (!(this.testToken(SYM_le) || this.testToken(SYM_lbrack) || this.testToken(SYM_lparen))) {
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
                            if (followtoken === TokenStrings.Namespace || followtoken === TokenStrings.Type || followtoken === TokenStrings.Template || followtoken ===  SYM_lbrack || followtoken === SYM_lbrace) {
                                const terms = this.parseTemplateArguments();
                                const rec = this.testToken(SYM_lbrack) ? this.parseRecursiveAnnotation() : "no";

                                const args = this.parseArguments(SYM_lparen, SYM_rparen);
                                ops.push(new PostfixInvoke(sinfo, specificResolve, refpfx, name, terms, rec, args));
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
                            ops.push(new PostfixInvoke(sinfo, specificResolve, refpfx, name, [], rec, args));
                        }
                    }
                }
            }
            */
            else {
                if (ops.length === 0) {
                    return rootexp;
                }
                else {
                    return new PostfixOp(ops[0].sinfo, rootexp, ops);
                }
            }
        }
    }

    private prefixStackApplicationHandler(exp: Expression, sinfo: SourceInfo, ops: string[]): Expression {
        for (let i = 0; i < ops.length; ++i) {
            const op = ops[i];

            if (op === SYM_bang) {
                exp = new PrefixNotOpExpression(sinfo, exp);
            }
            else if (op === SYM_negate) {
                exp = new PrefixNegateOpExpression(sinfo, exp);
            }
            else {
                ; //drop the redundant +
            }
        }

        return exp;
    }

    private parsePrefixExpression(): Expression {
        const sinfo = this.lexer.peekNext().getSourceInfo();

        let ops: string[] = [];
        while(this.testToken(SYM_bang) || this.testToken(SYM_positive) || this.testToken(SYM_negate)) {
            ops.push(this.consumeTokenAndGetValue());
        }

        let exp: Expression;
        if (this.testToken(KW_if)) {
            exp = this.parseIfExpression();
        }
        else {
            exp = this.parsePostfixExpression();
        }

        return this.prefixStackApplicationHandler(exp, sinfo, ops.reverse());
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
        const sinfo = this.lexer.peekNext().getSourceInfo();
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
                    aexp = new BinMultExpression(sinfo, lhs, rhs);
                }
                else {
                    aexp = new BinDivExpression(sinfo, lhs, rhs);
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
        const sinfo = this.lexer.peekNext().getSourceInfo();
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
                    aexp = new BinAddExpression(sinfo, lhs, rhs);
                }
                else {
                    aexp = new BinSubExpression(sinfo, lhs, rhs);
                }
            }

            return aexp;
        }
    }

    private parseRelationalExpression(): Expression {
        const sinfo = this.lexer.peekNext().getSourceInfo();
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
        else if(this.testAndConsumeTokenIf(SYM_lt)) {
            return new NumericLessExpression(sinfo, exp, this.parseRelationalExpression());
        }
        else if(this.testAndConsumeTokenIf(SYM_lteq)) {
            return new NumericLessEqExpression(sinfo, exp, this.parseRelationalExpression());
        }
        else if(this.testAndConsumeTokenIf(SYM_gt)) {
            return new NumericGreaterExpression(sinfo, exp, this.parseRelationalExpression());
        }
        else if(this.testAndConsumeTokenIf(SYM_gteq)) {
            return new NumericGreaterEqExpression(sinfo, exp, this.parseRelationalExpression());
        }
        else {
            return exp;
        }
    }

    private parseAndExpression(): Expression {
        const sinfo = this.lexer.peekNext().getSourceInfo();
        const exp = this.parseRelationalExpression();

        if (this.testAndConsumeTokenIf(SYM_ampamp)) {
            return new BinLogicAndExpression(sinfo, exp, this.parseAndExpression());
        }
        else {
            return exp;
        }
    }

    private parseOrExpression(): Expression {
        const sinfo = this.lexer.peekNext().getSourceInfo();
        const exp = this.parseAndExpression();

        if (this.testAndConsumeTokenIf(SYM_barbar)) {
            return new BinLogicOrExpression(sinfo, exp, this.parseOrExpression());
        }
        else {
            return exp;
        }
    }

    private parseImpliesExpression(): Expression {
        const sinfo = this.lexer.peekNext().getSourceInfo();
        const exp = this.parseOrExpression();

        if (this.testAndConsumeTokenIf(SYM_implies)) {
            return new BinLogicImpliesExpression(sinfo, exp, this.parseImpliesExpression());
        }
        else if(this.testAndConsumeTokenIf(SYM_iff)) {
            return new BinLogicIFFExpression(sinfo, exp, this.parseImpliesExpression());
        }
        else {
            return exp;
        }
    }

    private parseIfTest(): IfTest {
        const tk = this.peekToken();

        if(tk !== SYM_lparen) {
            const itest = this.parseITest();
            
            this.ensureAndConsumeToken(SYM_lparen, "if test");
            const exp = this.parseExpression();
            this.ensureAndConsumeToken(SYM_rparen, "if test");

            return new IfTest(exp, itest);
        }
        else {
            this.ensureAndConsumeToken(SYM_lparen, "if test");
            const exp = this.parseExpression();
            this.ensureAndConsumeToken(SYM_rparen, "if test");

            return new IfTest(exp,  undefined);
        }
    }

    private parseIfExpression(): Expression {
        const sinfo = this.lexer.peekNext().getSourceInfo();

        this.consumeToken();
        const binder = this.parseBinderInfo();
        const iftest = this.parseIfTest();

        this.ensureAndConsumeToken(KW_then, "if expression value")

        const [isimplicit, bnames] = Parser.generateITestBinderName(iftest.itestopt, iftest.exp, binder);

        const ifvalueinfo = this.parseExpressionWithBinder(bnames);
        let btrue: BinderInfo | undefined = undefined;
        if(ifvalueinfo.used.length > 0) {
            btrue = new BinderInfo(ifvalueinfo.used[0].srcname, ifvalueinfo.used[0].scopedname, isimplicit);
        }

        this.ensureAndConsumeToken(KW_else, "if expression else value");
        const elsevalueinfo = this.parseExpressionWithBinder(bnames);

        let belse: BinderInfo | undefined = undefined;
        if(elsevalueinfo.used.length > 0) {
            belse = new BinderInfo(elsevalueinfo.used[0].srcname, elsevalueinfo.used[0].scopedname, isimplicit);
        }

        return new IfExpression(sinfo, iftest, ifvalueinfo.exp, btrue, elsevalueinfo.exp, belse);
    }

    private parseExpression(): Expression {
        return this.parseImpliesExpression();
    }

    private parseExpressionWithBinder(bindernames: string[]): {exp: Expression, used: {srcname: string, scopedname: string}[]} {
        this.env.pushBinderExpressionScope(bindernames)
        const exp = this.parseExpression();
        const used = this.env.popBinderExpressionScope();

        return {exp: exp, used: used};
    }

    private parseMapEntryConstructorExpression(): Expression {
        const sinfo = this.lexer.peekNext().getSourceInfo();
        //TODO: this will reject (2 => 3) since there are parens, maybe this is ok or maybe we should allow it?

        const lexp = this.parseExpression();   
        if(this.testAndConsumeTokenIf("=>")) {
            const rexp = this.parseExpression();
        
            return new MapEntryConstructorExpression(sinfo, lexp, rexp);
        }
        else {
            return lexp;
        }
    }

    private parseLambdaOkExpression(): Expression {
        //TODO: this will reject (fn(x) => x) since there are parens, maybe this is ok or maybe we should allow it?

        if (this.testToken(KW_fn) || this.testFollows(KW_recursive, KW_fn) || this.testFollows(KW_recursive_q, KW_fn)) {
            return this.parseLambdaTerm();
        }
        else if (this.testToken(KW_pred) || this.testFollows(KW_recursive, KW_pred) || this.testFollows(KW_recursive_q, KW_pred)) {
            return this.parseLambdaTerm();
        }
        else {
            return this.parseExpression();
        }
    }

    private parseRHSExpression(): Expression {
        //todo we need to handle ref calls and such
        if(this.testToken(KW_ref)) {
            assert(false, "Not implemented -- ref expression");
        }
        else {
            return this.parseExpression();
        }
    }

    private parseStatementExpression(isref: boolean): Statement {
        if(this.testFollows(TokenStrings.IdentifierName, SYM_at)) {
            const sinfo = this.lexer.peekNext().getSourceInfo();
            const name = this.consumeTokenAndGetValue();
            this.consumeToken();

            const badbinder = name.startsWith("$");
            const lambdacapture = this.env.identifierResolvesAsVariable(name)
            if(badbinder || lambdacapture) {
                this.recordErrorGeneral(sinfo, "Cannot retype lambda captured or binder variables");
                return new ErrorStatement(sinfo);
            }

            const ttest = this.parseITest();
            if(ttest === undefined) {
                this.recordErrorGeneral(sinfo, "Expected test expression after @");
                return new ErrorStatement(sinfo);
            }

            return new VariableRetypeStatement(sinfo, name, ttest);
        }
        else {
            assert(false, "Not implemented -- statement expression");
        }
    }

    ////
    //Statement parsing

    parseSingleDeclarationVarInfo(): {name: string, vtype: TypeSignature} {
        const sinfo = this.lexer.peekNext().getSourceInfo();

        this.ensureToken(TokenStrings.IdentifierName, "assignment statement");
        const name = this.consumeTokenAndGetValue();

        let itype = this.env.SpecialAutoSignature;
        if (this.testAndConsumeTokenIf(":")) {
            itype = this.parseTypeSignature();
        }

        if(!/^[a-z_]/.test(name)) {
            this.recordErrorGeneral(sinfo, `Local varialbes must start with a lowercase letter or underscore but got "${name}"`);
        }

        return { name: name, vtype: itype };
    }

    parseMultiDeclarationVarInfo(): {name: string, vtype: TypeSignature}[] {
        let decls: {name: string, vtype: TypeSignature}[] = [];

        while(this.testToken(SYM_coma)) {
            const dd = this.parseSingleDeclarationVarInfo();
            decls.push(dd);
        }

        return decls;
    }

    parseSingleAssignmentVarInfo(): string {
        const sinfo = this.lexer.peekNext().getSourceInfo();

        this.ensureToken(TokenStrings.IdentifierName, "assignment statement");
        const name = this.consumeTokenAndGetValue();

        
        if(!/^[a-z_]/.test(name)) {
            this.recordErrorGeneral(sinfo, `Local varialbes must start with a lowercase letter or underscore but got "${name}"`);
        }

        return name;
    }

    parseMultiAssignmentVarInfo(): string[] {
        let assigns: string[] = [];

        while(this.testToken(SYM_coma)) {
            const dd = this.parseSingleAssignmentVarInfo();
            assigns.push(dd);
        }

        return assigns;
    }

    /*
    private parseTaskRunStatement(sinfo: SourceInfo, isdefine: boolean, isconst: boolean, vv: {name: string, vtype: TypeSignature} | undefined): Statement {
        this.ensureTaskOpOk();
        
        //TODO: need to cleanup so that SC return and assign work with this as well 

        let allvvs: {name: string, vtype: TypeSignature}[] = [];
        if (vv !== undefined) {
            allvvs.push(vv);
            while (!this.testToken(SYM_eq)) {
                this.ensureAndConsumeToken(SYM_coma, "Expected , in task result assignment list");

                const assign = this.parseAssignmentVarInfo(this.getCurrentSrcInfo(), isconst ? KW_let : KW_var);
                const vvar = { name: assign.name, vtype: assign.vtype };

                if (this.m_penv.getCurrentFunctionScope().isVarNameDefined(assign.name)) {
                    this.raiseError(this.getCurrentLine(), "Variable name is already defined");
                }
                this.m_penv.getCurrentFunctionScope().defineLocalVar(assign.name, assign.name, false);

                allvvs.push(vvar);
            }
        }

        this.consumeToken();
        this.ensureAndConsumeToken(SYM_coloncolon, "Task statement");
        this.ensureToken(TokenStrings.Identifier, "Task statement");

        const name = this.consumeTokenAndGetValue();

        if(name === "getTaskID" || name === "isCanceled") {
            this.ensureAndConsumeToken(SYM_lparen, `Task expression ${name}`);
            this.ensureAndConsumeToken(SYM_rparen, `Task expression ${name}`);
            this.ensureAndConsumeToken(SYM_semicolon, `Task expression ${name}`);

            if(name === "getTaskID") {
                if(vv === undefined) {
                    return new ReturnStatement(sinfo, new TaskGetIDExpression(sinfo));
                }
                else if(isdefine) {
                    return new VariableDeclarationStatement(sinfo, vv.name, isconst, vv.vtype, new TaskGetIDExpression(sinfo), undefined);
                }
                else {
                    return new VariableAssignmentStatement(sinfo, vv.name, new TaskGetIDExpression(sinfo), undefined);
                }
            }
            else {
                if(vv === undefined) {
                    return new ReturnStatement(sinfo, new TaskCancelRequestedExpression(sinfo))
                }
                else if(isdefine) {
                    return new VariableDeclarationStatement(sinfo, vv.name, isconst, vv.vtype, new TaskCancelRequestedExpression(sinfo), undefined);
                }
                else {
                    return new VariableAssignmentStatement(sinfo, vv.name, new TaskCancelRequestedExpression(sinfo), undefined);
                }
            }
        }
        else {
            let argpack: { argn: string, argv: Expression }[] = [];
            if (this.testToken(SYM_lbrace)) {
                this.parseListOf("Task Run arguments", SYM_lbrace, SYM_rbrace, SYM_coma, () => {
                    const argn = this.ensureAndConsumeToken(TokenStrings.Identifier, "Task Run argument name");
                    this.ensureAndConsumeToken("=", "Task run argument");
                    const argv = this.parseExpression();

                    return { argn: argn, argv: argv };
                });
            }

            const terms = this.parseTemplateArguments();
            const args = this.parseArguments(SYM_lparen, SYM_rparen);

            if (terms.length !== 0) {
                this.raiseError(sinfo.line, "Must supply at least 1 task to run");
            }

            this.ensureAndConsumeToken(SYM_semicolon, "assignment statement");

            if (name === "run") {
                if (terms.length !== allvvs.length) {
                    this.raiseError(sinfo.line, "Must have equal numbers of tasks and result assignments");
                }

                if (terms.length === 1) {
                    //x = Task::run<T>(args)
                    return new TaskRunStatement(sinfo, isdefine, isconst, allvvs[0], terms[0], argpack, args);
                }
                else {
                    //y, z = Task::run<T, U>(argv, ...)
                    return new TaskMultiStatement(sinfo, isdefine, isconst, allvvs, terms, argpack, args);
                }
            }
            else if (name === "dash") {
                if (terms.length === 1) {
                    this.raiseError(sinfo.line, "dashing to a result on a single task is redundant -- use \"run\" instead");
                }

                if (terms.length !== allvvs.length) {
                    this.raiseError(sinfo.line, "Must have equal numbers of tasks and result assignments");
                }

                //x, y, z = Task::dash<T, U>(argv, ...)
                return new TaskDashStatement(sinfo, isdefine, isconst, allvvs, terms, argpack, args);
            }
            else if (name === "all") {
                if (terms.length !== 1 || args.length !== 1) {
                    this.raiseError(sinfo.line, "Task::all runs same task on all args tuples in the list");
                }

                if (allvvs.length !== 1) {
                    this.raiseError(sinfo.line, "Task::all produces a single result List");
                }

                //x: List<V> = Task::all<T>(List<U>) <-- result list all done
                return new TaskAllStatement(sinfo, isdefine, isconst, allvvs[0], terms[0], argpack, args[0]);
            }
            else if (name === "race") {
                if (terms.length !== 1 || args.length !== 1) {
                    this.raiseError(sinfo.line, "Task::all runs same task on all args tuples in the list");
                }

                if (allvvs.length !== 1) {
                    this.raiseError(sinfo.line, "Task::all produces a single Result");
                }

                //x: Result<T, E> = Task::race<T>(List<U>) <-- result list all done
                return new TaskRaceStatement(sinfo, isdefine, isconst, allvvs[0], terms[0], argpack, args[0]);
            }
            else {
                this.raiseError(sinfo.line, "Unknown \"Task\" operation");
                return new InvalidStatement(sinfo);
            }
        }
    }
    */

    private parseLineStatement(): Statement {
        const sinfo = this.lexer.peekNext().getSourceInfo();

        if (this.testToken(SYM_semicolon)) {
            return new EmptyStatement(sinfo);
        }
        else if (this.testToken(KW_var) || this.testToken(KW_let)) {
            const isConst = this.testToken(KW_let);
            
            this.consumeToken();
            const assigns = this.parseMultiDeclarationVarInfo();

            if(this.testToken(SYM_semicolon)) {
                if(isConst) {
                    this.recordErrorGeneral(sinfo, "Cannot declare as const without an assignment");
                }

                if(assigns.some((vv) => vv.vtype instanceof AutoTypeSignature)) {
                    this.recordErrorGeneral(sinfo, "Cannot declare a variable with an auto type without an assignment");
                }

                assigns.forEach((vv) => {
                    this.env.addVariable(vv.name, isConst);
                });

                return assigns.length === 1 ? new VariableDeclarationStatement(sinfo, assigns[0].name, assigns[0].vtype) : new VariableMultiDeclarationStatement(sinfo, assigns);
            }
            else if(this.testToken(SYM_eq)) {
                this.consumeToken();

                const exp = this.parseRHSExpression();
                if(this.testToken(SYM_semicolon)) {
                    //could be elist type expression but we need to wait for type checking
                    assigns.forEach((vv) => {
                        this.env.addVariable(vv.name, isConst);
                    });

                    return assigns.length === 1 ? new VariableInitializationStatement(sinfo, isConst, assigns[0].name, assigns[0].vtype, exp) : new VariableMultiInitializationStatement(sinfo, isConst, assigns, exp);
                }
                else {
                    //we need as many expressions as there are variables
                    let exps = [exp];
                    while(this.testToken(SYM_coma) && exps.length < assigns.length) {
                        this.consumeToken();
                        exps.push(this.parseRHSExpression());
                    }

                    if(exps.length !== assigns.length) {
                        this.recordErrorGeneral(sinfo, "Mismatch in number of variables and expressions in assignment");
                    }

                    assigns.forEach((vv) => {
                        this.env.addVariable(vv.name, isConst);
                    });

                    return assigns.length === 1 ? new VariableInitializationStatement(sinfo, isConst, assigns[0].name, assigns[0].vtype, exps[0]) : new VariableMultiInitializationStatement(sinfo, isConst, assigns, exps);
                }
            }
            else {
                this.recordErrorGeneral(sinfo, `Expected a \";\" or an assignment after variable declaration but got ${this.peekToken()}`);
                return new ErrorStatement(sinfo);
            }
        }
        else if (this.testFollows(TokenStrings.IdentifierName, SYM_eq)) {
            const vname = this.parseSingleAssignmentVarInfo();
            const exp = this.parseRHSExpression();

            return new VariableAssignmentStatement(sinfo, vname, exp);
        }
        else if (this.testFollows(TokenStrings.IdentifierName, SYM_coma)) {
            const vnames = this.parseMultiAssignmentVarInfo();

            this.ensureAndConsumeToken(SYM_eq, "assignment statement");
            const exp = this.parseRHSExpression();

            if(this.testToken(SYM_semicolon)) {
                //could be elist type expression but we need to wait for type checking
                vnames.forEach((vv) => {
                    this.env.assignVariable(vv);
                });

                return vnames.length === 1 ? new VariableAssignmentStatement(sinfo, vnames[0], exp) : new VariableMultiAssignmentStatement(sinfo, vnames, exp);
            }
            else {
                //we need as many expressions as there are variables
                let exps = [exp];
                while(this.testToken(SYM_coma) && exps.length < vnames.length) {
                    this.consumeToken();
                    exps.push(this.parseRHSExpression());
                }

                if(exps.length !== vnames.length) {
                    this.recordErrorGeneral(sinfo, "Mismatch in number of variables and expressions in assignment");
                }

                vnames.forEach((vv) => {
                    this.env.assignVariable(vv);
                });

                return vnames.length === 1 ? new VariableAssignmentStatement(sinfo, vnames[0], exps[0]) : new VariableMultiAssignmentStatement(sinfo, vnames, exps);
            }
        }
        else if (this.testToken(KW_return)) {
            this.consumeToken();

            if(this.testToken(SYM_semicolon)) {
                return new ReturnStatement(sinfo, undefined);
            }
            else {
                const rexp = this.parseRHSExpression();
                if(this.testToken(SYM_semicolon)) {
                    return new ReturnStatement(sinfo, rexp);
                }
                else {
                    let rexps = [rexp];
                    while(this.testToken(SYM_coma)) {
                        this.consumeToken();
                        rexps.push(this.parseRHSExpression());
                    }

                    return new ReturnStatement(sinfo, rexps);
                }
            }
        }
        /*
        else if (tk === KW_env) {
            this.ensureTaskOpOk();

            this.consumeToken();

            const isfresh = this.testToken(SYM_lbrace);
            let binds: {keyname: string, valexp: [TypeSignature, Expression] | undefined}[] = [];
            if(isfresh) {
                binds = this.parseEnvUpdateArguments(SYM_lbrace, SYM_rbrace).map((nn) => {
                    return {keyname: nn.name, valexp: nn.value};
                });
            }
            else {
                binds = this.parseEnvUpdateArguments(SYM_lbrack, SYM_rbrack).map((nn) => {
                    return {keyname: nn.name, valexp: nn.value};
                });
            }

            if(!isfresh && binds.length === 0) {
                this.raiseError(sinfo.line, "environment update without any assignments is vacuous")
            }

            if(binds.some((bb, ii) => binds.findIndex((obb) => obb.keyname === bb.keyname) !== ii)) {
                this.raiseError(sinfo.line, "duplicate key in environment operation");
            }

            if(this.testAndConsumeTokenIf(SYM_semicolon)) {
                //env set value here
                if(isfresh) {
                    return new EnvironmentFreshStatement(sinfo, binds);
                }
                else {
                    return new EnvironmentSetStatement(sinfo, binds);
                }
            }
            else if(this.testAndConsumeTokenIf(KW_in)) {
                const block = this.parseBlockStatement("environment");

                return new EnvironmentSetStatementBracket(sinfo, binds, block, isfresh);
            }
            else {
                this.raiseError(sinfo.line, "expected a \";\" or \"in\" keyword as part of an environment statement");
                return new InvalidStatement(sinfo);
            }
        }
        */
        else if (this.testToken(KW_abort)) {
            this.consumeToken();
            return new AbortStatement(sinfo);
        }
        else if (this.testToken(KW_assert)) {
            this.consumeToken();

            const level = this.parseBuildInfo(KW_release);
            const exp = this.parseExpression();

            return new AssertStatement(sinfo, exp, level);
        }
        else if (this.testToken(KW_validate)) {
            this.consumeToken();

            let diagnosticTag: string | undefined = undefined;
            if(this.testToken(SYM_lbrack)) {
                this.consumeToken();
                this.ensureToken(TokenStrings.ASCIIString, "validate statement tag");
                diagnosticTag = this.consumeTokenAndGetValue();
                this.ensureAndConsumeToken(SYM_rbrack, "validate statement tag");
            }

            const exp = this.parseExpression();

            return new ValidateStatement(sinfo, exp, diagnosticTag);
        }
        else if (this.testToken(KW__debug)) {
            this.consumeToken();

            this.ensureAndConsumeToken(SYM_lparen, "_debug statement");
            const value = this.parseExpression();
            this.ensureAndConsumeToken(SYM_rparen, "_debug statement");
            
            return new DebugStatement(sinfo, value);
        }
        /*
        else if (tk === KW_ref) {
            const call = this.parseSCRefExpression();
            if(!(call[0] instanceof PostfixOp) && !(call[0] instanceof TaskSelfActionExpression)) {
                this.raiseError(sinfo.line, "ref invoke statement");
            }

            return new RefCallStatement(sinfo, call[0] as (PostfixOp | TaskSelfActionExpression), call[1]);
        }
        else if(tk === KW_callwith) {
            this.ensureTaskOpOk();

            this.consumeToken();
            this.ensureToken(TokenStrings.Identifier, "callwith operation");
            if(this.consumeTokenAndGetValue() !== "self") {
                this.raiseError(sinfo.line, "can only callwith on self actions");
            }

            this.ensureAndConsumeToken(SYM_dot, "callwith operation");

            this.ensureToken(TokenStrings.Identifier, "callwith operation name");
            const cname = this.consumeTokenAndGetValue();

            const terms = this.testToken(SYM_le) ? this.parseTemplateArguments() : [];
            const args = this.parseArguments(SYM_lparen, SYM_rparen);

            this.ensureAndConsumeToken(SYM_semicolon, "callwith operation");

            return new TaskCallWithStatement(sinfo, cname, terms, args);
        }
        else if(tk === KW_resultwith) {
            this.ensureTaskOpOk();

            this.consumeToken();
            this.ensureToken(TokenStrings.Identifier, "resultwith operation");
            if(this.consumeTokenAndGetValue() !== "self") {
                this.raiseError(sinfo.line, "can only resultwith on self actions");
            }

            this.ensureAndConsumeToken(SYM_dot, "resultwith operation");

            this.ensureToken(TokenStrings.Identifier, "resultwith operation name");
            const cname = this.consumeTokenAndGetValue();

            const terms = this.testToken(SYM_le) ? this.parseTemplateArguments() : [];
            const args = this.parseArguments(SYM_lparen, SYM_rparen);

            this.ensureAndConsumeToken(SYM_semicolon, "resultwith operation");

            return new TaskCallWithStatement(sinfo, cname, terms, args);
        }
        else if(tk === TokenStrings.Namespace && this.peekTokenData() === "Task") {
            this.ensureTaskOpOk();

            this.consumeToken();
            this.ensureAndConsumeToken(SYM_coloncolon, "Task operation");
            this.ensureToken(TokenStrings.Identifier, "Task operation");
            const op = this.consumeTokenAndGetValue();
            if(op !== "status" && op !== "event") {
                this.raiseError(sinfo.line, `unknown call ${op} on Task`);
            }

            const args = this.parseArguments(SYM_lparen, SYM_rparen);
            if(args.length !== 1) {
                this.raiseError(sinfo.line, `Task::${op} takes a single argument`);
            }

            this.ensureAndConsumeToken(SYM_semicolon, `Task::${op} operation`);
                    
            if(op === "status") {
                return new TaskSetStatusStatement(sinfo, args[0]);
            }
            else {
                return new TaskEventEmitStatement(sinfo, args[0]);
            }
        }
        */
        else {
            const isref = this.testToken(KW_ref);
            return this.parseStatementExpression(isref);
        }
    }

    private parseScopedBlockStatement(): BlockStatement {
        const sinfo = this.lexer.peekNext().getSourceInfo();

        this.env.pushStandardBlockScope();
        const stmts = this.parseListOf<Statement>("block", SYM_lbrace, SYM_rbrace, SYM_semicolon, () => {
            return this.parseStatement();
        });
        this.env.popStandardBlockScope();

        if(stmts.length === 0) {
            this.recordErrorGeneral(sinfo, "Empty block statement -- should include a ';' to indicate intentionally empty block");
        }

        return new BlockStatement(sinfo, stmts);
    }

    private parseScopedBlockStatementWithBinderTracking(bindernames: string[]): {block: BlockStatement, used: {srcname: string, scopedname: string}[]} {
        const sinfo = this.lexer.peekNext().getSourceInfo();

        this.env.pushBinderExpressionScope(bindernames);
        const stmts = this.parseListOf<Statement>("block", SYM_lbrace, SYM_rbrace, SYM_semicolon, () => {
            return this.parseStatement();
        });
        const used = this.env.popBinderExpressionScope();

        if(stmts.length === 0) {
            this.recordErrorGeneral(sinfo, "Empty block statement -- should include a ';' to indicate intentionally empty block");
        }

        return {block: new BlockStatement(sinfo, stmts), used: used};
    }

    private parseIfElseStatement(): Statement {
        const sinfo = this.lexer.peekNext().getSourceInfo();

        this.ensureAndConsumeToken(KW_if, "if statement cond");
        const ifbinder = this.parseBinderInfo();
        const iftest = this.parseIfTest();

        const [ifisimplicit, ifbnames] = Parser.generateITestBinderName(iftest.itestopt, iftest.exp, ifbinder);
        const ifbody = this.parseScopedBlockStatementWithBinderTracking(ifbnames);
        let ifbind: BinderInfo | undefined = undefined;
        if(ifbody.used.length > 0) {
            ifbind = new BinderInfo(ifbody.used[0].srcname, ifbody.used[0].scopedname, ifisimplicit);
        }

        let conds: {cond: IfTest, block: BlockStatement}[] = [];
        while (this.testAndConsumeTokenIf(KW_elif)) {
            const eliftest = this.parseIfTest();
            const elifbody = this.parseScopedBlockStatement();
           
            conds.push({cond: eliftest, block: elifbody});
        }

        if(conds.length === 0) {
            if(!this.testAndConsumeTokenIf(KW_else)) {
                return new IfStatement(sinfo, iftest, ifbody.block, ifbind);
            }
            else {
                const elsebody = this.parseScopedBlockStatementWithBinderTracking([]);
                let elsebind: BinderInfo | undefined = undefined;
                if(elsebody.used.length > 0) {
                    elsebind = new BinderInfo(elsebody.used[0].srcname, elsebody.used[0].scopedname, false);
                }

                return new IfElseStatement(sinfo, iftest, ifbody.block, ifbind, elsebody.block, elsebind);
            }
        }
        else {
            if(ifbody.used.length > 0) {
                this.recordErrorGeneral(sinfo, "Cannot have a binder in an if-elif-else statement");
            }

            const elssebody = this.parseScopedBlockStatement();
            return new IfElifElseStatement(sinfo, [{cond: iftest, block: ifbody.block}, ...conds], elssebody);
        }
    }

    private parseSwitchStatement(): Statement {
        const sinfo = this.lexer.peekNext().getSourceInfo();
        
        this.ensureAndConsumeToken(KW_switch, "switch statement dispatch value");

        const binder = this.parseBinderInfo();

        this.ensureAndConsumeToken(SYM_lparen, "switch statement dispatch value");
        const sexp = this.parseExpression();
        this.ensureAndConsumeToken(SYM_rparen, "switch statement dispatch value");

        const [mimplicit, mbnames] = Parser.generateMatchBinderName(sexp, binder);

        let entries: { lval: LiteralExpressionValue | undefined, value: BlockStatement, bindername: string | undefined }[] = [];
        this.ensureAndConsumeToken(SYM_lbrace, "switch statement options");
        
        const swlit = this.parseSwitchLiteralGuard();
        this.ensureAndConsumeToken(SYM_bigarrow, "switch statement entry");
        const svalue = this.parseScopedBlockStatementWithBinderTracking(mbnames);

        entries.push({ lval: swlit, value: svalue.block, bindername: svalue.used.length !== 0 ? svalue.used[0].srcname : undefined });
        while (this.testToken(SYM_bar)) {
            this.consumeToken();

            const swlitx = this.parseSwitchLiteralGuard();
            this.ensureAndConsumeToken(SYM_bigarrow, "switch statement entry");
            const svaluex = this.parseScopedBlockStatementWithBinderTracking(mbnames);

            entries.push({ lval: swlitx, value: svaluex.block, bindername: svaluex.used.length !== 0 ? svaluex.used[0].srcname : undefined });
        }
        this.ensureAndConsumeToken(SYM_rbrace, "switch statement options");

        let bindinfo: BinderInfo | undefined = undefined;
        if(entries.some((cc) => cc.bindername !== undefined)) {
            bindinfo = new BinderInfo(mbnames[0], this.env.getScope().getBinderVarName(mbnames[0]), mimplicit);
        }

        return new SwitchStatement(sinfo, [sexp, bindinfo], entries);
    }

    private parseMatchStatement(): Statement {
        const sinfo = this.lexer.peekNext().getSourceInfo();
        
        this.ensureAndConsumeToken(KW_match, "match statement dispatch value");

        const binder = this.parseBinderInfo();

        this.ensureAndConsumeToken(SYM_lparen, "match statement dispatch value");
        const mexp = this.parseExpression();
        this.ensureAndConsumeToken(SYM_rparen, "match statement dispatch value");

        const [mimplicit, mbnames] = Parser.generateMatchBinderName(mexp, binder);

        let entries: { mtype: TypeSignature | undefined, value: BlockStatement, bindername: string | undefined  }[] = [];
        this.ensureAndConsumeToken(SYM_lbrace, "match statement options");

        const mtype = this.parseMatchTypeGuard();
        this.ensureAndConsumeToken(SYM_bigarrow, "match statement entry");
        const mvalue = this.parseScopedBlockStatementWithBinderTracking(mbnames);

        entries.push({ mtype: mtype, value: mvalue.block, bindername: mvalue.used.length !== 0 ? mvalue.used[0].srcname : undefined});
        while (this.testToken(SYM_bar)) {
            this.consumeToken();
            
            const mtypex = this.parseMatchTypeGuard();
            this.ensureAndConsumeToken(SYM_bigarrow, "match statement entry");
            const mvaluex = this.parseScopedBlockStatementWithBinderTracking(mbnames);

            entries.push({ mtype: mtypex, value: mvaluex.block, bindername: mvaluex.used.length !== 0 ? mvaluex.used[0].srcname : undefined});
        }
        this.ensureAndConsumeToken(SYM_rbrace, "switch statment options");

        let bindinfo: BinderInfo | undefined = undefined;
        if(entries.some((cc) => cc.bindername !== undefined)) {
            bindinfo = new BinderInfo(mbnames[0], this.env.getScope().getBinderVarName(mbnames[0]), mimplicit);
        }

        return new MatchStatement(sinfo, [mexp, bindinfo], entries);
    }

    private parseStatement(): Statement {
        if (this.testToken(KW_if)) {
            return this.parseIfElseStatement();
        }
        else if (this.testToken(KW_switch)) {
            return this.parseSwitchStatement();
        }
        else if (this.testToken(KW_match)) {
            return this.parseMatchStatement();
        }
        else if(this.testToken(SYM_lbrace)) {
            return this.parseScopedBlockStatement();
        }
        else {  
            const closesemi = this.scanToRecover(SYM_semicolon);
            const closepos = closesemi !== undefined ? this.lexer.peekK(closesemi).pos : this.lexer.currentState().epos;
            this.lexer.prepStateStackForNested("line-statement", closepos, undefined);

            const result = this.parseLineStatement();
            
            if(!this.testToken(SYM_semicolon)) {
                //we gotta recover
                this.lexer.currentState().recover();
            }

            if(this.testToken(SYM_semicolon)) {
                this.consumeToken();
            }

            this.lexer.popStateIntoParentOk();

            return result;
        }
    }

    private parseBody(attribs: DeclarationAttibute[], isPredicate: boolean, isLambda: boolean): BodyImplementation {
        const sinfo = this.lexer.peekNext().getSourceInfo();

        if(this.testToken(SYM_semicolon)) {
            if(!attribs.some((aa) => aa.name === "abstract") && !isPredicate) {
                this.recordErrorGeneral(sinfo, "Body implementation expected unless declared as abstract or a predicate");
            }

            this.consumeToken();
            if(isPredicate) {
                return new PredicateUFBodyImplementation(sinfo, this.env.currentFile);
            }
            else {
                return new AbstractBodyImplementation(sinfo, this.env.currentFile);
            }
        }
        else if(this.testToken(SYM_eq)) {
            this.consumeToken();

            this.ensureToken(TokenStrings.IdentifierName, "body");
            const iname = this.consumeTokenAndGetValue();
            this.ensureAndConsumeToken(SYM_semicolon, "body");

            return new BuiltinBodyImplementation(sinfo, this.env.currentFile, iname);
        }
        else if(this.testFollows(SYM_lbrace, SYM_HOLE, SYM_semicolon, SYM_rbrace)) {
            this.consumeToken();
            this.consumeToken();
            this.consumeToken();
            this.consumeToken();

            return new SynthesisBodyImplementation(sinfo, this.env.currentFile);
        }
        else {
            if(this.testToken(SYM_lbrace)) {
                //check for the case where this is actually a record constructor in a lambda body
                if(isLambda && (this.testFollows(SYM_lbrace, SYM_rbrace) || this.testFollows(SYM_lbrace, TokenStrings.IdentifierName, SYM_eq))) {
                    return new ExpressionBodyImplementation(sinfo, this.env.currentFile, this.parseExpression());
                }
                else {
                    return new StandardBodyImplementation(sinfo, this.env.currentFile, this.parseScopedBlockStatement().statements);
                }
            }
            else {
                return new ExpressionBodyImplementation(sinfo, this.env.currentFile, this.parseExpression());
            }
        }
    }

    ////
    //Decl parsing

    private parseTypeTemplateTermDecl(): TypeTemplateTermDecl {
        this.ensureToken(TokenStrings.Template, "template term");
        const tname = this.consumeTokenAndGetValue();

        let ttype = this.wellknownTypes.get("Any") as TypeSignature;
        if(this.testAndConsumeTokenIf(SYM_colon)) {
            ttype = this.parseTypeSignature();
        }

        return new TypeTemplateTermDecl(tname, ttype);
    }

    private parseTypeTemplateTerms(): TypeTemplateTermDecl[] { 
        let terms: TypeTemplateTermDecl[] = [];
        if(this.testToken(SYM_langle)) {
            terms = this.parseListOf<TypeTemplateTermDecl>("template terms", SYM_langle, SYM_rangle, SYM_coma, () => {
                return this.parseTypeTemplateTermDecl();
            });
        }

        return terms;
    }

    private scanOverCodeTo(...tsync: string[]) {
        const spoc = this.scanToSyncPos(...tsync);
        this.lexer.currentState().skipToPosition(spoc);
    }

    private scanOverCodeParenSet(lp: string, rp: string) {
        const spoc = this.scanToSyncEatParens(lp, rp);
        this.lexer.currentState().skipToPosition(spoc);
    }

    private parseNamespaceUsing(phase: ParsePhase) {
        const sinfo = this.lexer.peekNext().getSourceInfo();

        this.ensureAndConsumeToken(KW_using, "namespce using");
        this.ensureToken(TokenStrings.IdentifierName, "namespce using");
            
        const chain: string[] = [];
        while(this.testToken(TokenStrings.IdentifierName)) {
            chain.push(this.consumeTokenAndGetValue());
            if(!this.testToken(SYM_coloncolon)) {
                break;
            }
            this.consumeToken();
        }

        if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterNamespaces)) {
            if(chain.length === 0) {
                this.recordErrorGeneral(sinfo, "Expected a namespace identifier");

                this.scanOverCodeTo(SYM_semicolon);
            }
            else {
                if(!this.testToken(KW_as)) {
                    if(this.env.currentNamespace.istoplevel) {
                        this.env.currentNamespace.usings.push(new NamespaceUsing(this.env.currentFile, new FullyQualifiedNamespace(chain), undefined));
                    }
                    else {
                        this.recordErrorGeneral(sinfo, `Cannot "use" a namespace in a non-toplevel namespace`);
                    }
                }
                else {
                    this.ensureToken(TokenStrings.IdentifierName, "namespace import");
                    const asns = this.consumeTokenAndGetValue();

                    if(!/^[A-Z].+/.test(asns)) {
                        this.recordErrorGeneral(sinfo, `Invalid namespace alias ${asns}`);
                        return;
                    }

                    if(this.env.currentNamespace.istoplevel) {
                        this.env.currentNamespace.usings.push(new NamespaceUsing(this.env.currentFile, new FullyQualifiedNamespace(chain), asns));
                    }
                    else {
                        this.recordErrorGeneral(sinfo, `Cannot "use" a namespace in a non-toplevel namespace`);
                    }
                }

                this.ensureAndConsumeToken(SYM_semicolon, "namespace import");
            }
        }
        else {
            if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterTypes)) {
                //make sure namespace is valid

                let iidx = 1;
                const rrns = this.env.assembly.getToplevelNamespace(chain[0]);
                while(rrns !== undefined && iidx < chain.length) {
                    rrns.subns.find((sns) => sns.name === chain[iidx]);
                    iidx++;
                }
    
                if(rrns === undefined) {
                    this.recordErrorGeneral(sinfo, `Unknown namespace ${chain.join("::")}`);
                }
            }

            this.scanOverCodeTo(SYM_semicolon);
            this.ensureAndConsumeToken(SYM_semicolon, "namespace using");
        }
    }

    private parseNamespaceMembers() {
        xxxx;
    }

    private parseSubNamespace() {
        this.ensureAndConsumeToken(KW_namespace, "nested namespace declaration");
        this.ensureToken(TokenStrings.IdentifierName, "nested namespace declaration");

        const nsname = this.consumeTokenAndGetValue();
        if(!/^[A-Z].+/.test(nsname)) {
            this.recordErrorGeneral(this.lexer.peekNext().getSourceInfo(), `Invalid namespace name ${nsname}`);
            return;
        }

        const sinfo = this.lexer.peekNext().getSourceInfo();
        if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterNamespaces)) {
            if (this.env.currentNamespace.checkDeclNameClashNS(nsname)) {
                this.recordErrorGeneral(sinfo, `Collision between namespace and other names -- ${nsname}`);
            }

            const nsdecl = new NamespaceDeclaration(false, nsname, new FullyQualifiedNamespace([...this.env.currentNamespace.fullnamespace.ns, nsname]));

            this.env.currentNamespace.subns.push(nsdecl);
            this.env.currentNamespace.declaredSubNSNames.add(nsname);

            const ons = this.env.currentNamespace;

            this.env.currentNamespace = nsdecl;
            this.ensureAndConsumeToken(SYM_lbrace, "nested namespace declaration");
            this.parseNamespaceMembers();
            this.ensureAndConsumeToken(SYM_rbrace, "nested namespace declaration");

            this.env.currentNamespace = ons;
        }
        else {
            const ons = this.env.currentNamespace;

            const nsdecl = this.env.currentNamespace.subns.find((ns) => ns.name === nsname) as NamespaceDeclaration;
            this.env.currentNamespace = nsdecl;
            this.ensureAndConsumeToken(SYM_lbrace, "nested namespace declaration");
            this.parseNamespaceMembers();
            this.ensureAndConsumeToken(SYM_rbrace, "nested namespace declaration");

            this.env.currentNamespace = ons;
        }
    }

    private parseNamespaceTypedef(attributes: DeclarationAttibute[]) {
        const sinfo = this.lexer.peekNext().getSourceInfo();
        this.ensureAndConsumeToken(KW_type, "type alias");
        this.ensureToken(TokenStrings.IdentifierName, "type alias");
        const tyname = this.consumeTokenAndGetValue();

        if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterNamespaces)) {
            if (this.env.currentNamespace.checkDeclNameClashType(tyname, this.testToken(SYM_langle))) {
                this.recordErrorGeneral(sinfo, `Collision between type alias and other names -- ${tyname}`);
            }

            this.env.currentNamespace.declaredNames.add(tyname);
            this.env.currentNamespace.declaredTypeNames.push({name: tyname, hasterms: this.testToken(SYM_langle)});
            
            this.scanOverCodeTo(SYM_semicolon);
            this.ensureAndConsumeToken(SYM_semicolon, "type alias");
        }
        else if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterTypes)) {
            if(this.env.currentNamespace.typeDefs.find((td) => td.name === tyname) === undefined){
                this.env.currentNamespace.typeDefs.push(new NamespaceTypedef(this.env.currentFile, sinfo, attributes, tyname, [], new ErrorTypeSignature(sinfo, undefined)));
            }

            this.scanOverCodeTo(SYM_semicolon);
            this.ensureAndConsumeToken(SYM_semicolon, "type alias");
        }
        else {
            const terms = this.parseTypeTemplateTerms();
            this.ensureAndConsumeToken(SYM_eq, "type alias");

            const btype = this.parseTypeSignature();

            const nndl = this.env.currentNamespace.typeDefs.find((td) => td.name === tyname);
            if(nndl !== undefined) {
                nndl.terms = terms;
                nndl.boundType = btype;
            }

            this.ensureAndConsumeToken(SYM_semicolon, "type alias");
        }
    }

    private parseNamespaceConstant(attributes: DeclarationAttibute[]) {
        const sinfo = this.lexer.peekNext().getSourceInfo();
        this.ensureAndConsumeToken(KW_const, "const member");

        this.ensureToken(TokenStrings.IdentifierName, "const member");
        const sname = this.consumeTokenAndGetValue();

        if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterNamespaces)) {
            if(this.env.currentNamespace.checkDeclNameClashMember(sname)) {
                this.recordErrorGeneral(sinfo, `Collision between const and other names -- ${sname}`);
            }

            this.env.currentNamespace.declaredNames.add(sname);
            this.env.currentNamespace.declaredMemberNames.add(sname);

            this.scanOverCodeTo(SYM_semicolon);
            this.ensureAndConsumeToken(SYM_semicolon, "const member");
        }
        else if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterTypes)) {
            this.scanOverCodeTo(SYM_semicolon);
            this.ensureAndConsumeToken(SYM_semicolon, "const member");
        }
        else {
            this.ensureAndConsumeToken(SYM_colon, "const member");
            const stype = this.parseTypeSignature();

            this.ensureAndConsumeToken(SYM_eq, "const member");
            const value = this.parseConstExpression(stype);
            if(value.captured.size !== 0) {
                this.recordErrorGeneral(sinfo, "Cannot have captured variables in const member");
            }

            this.env.currentNamespace.consts.push(new ConstMemberDecl(this.env.currentFile, sinfo, attributes, sname, stype, value));

            this.ensureAndConsumeToken(SYM_semicolon, "const member");
        }
    }

    private parseNamespaceFunction(attributes: DeclarationAttibute[]) {
        const sinfo = this.lexer.peekNext().getSourceInfo();

        if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterNamespaces)) {
            this.consumeTokenIf(KW_recursive);
            this.consumeTokenIf(KW_recursive_q);
            this.consumeToken();

            const fname = this.consumeTokenAndGetValue();
            if(this.env.currentNamespace.checkDeclNameClashMember(fname)) {
                this.recordErrorGeneral(sinfo, `Collision between function and other names -- ${fname}`);
            }

            this.env.currentNamespace.declaredNames.add(fname);
            this.env.currentNamespace.declaredMemberNames.add(fname);

            this.scanOverCodeTo(...NAMESPACE_DECL_FIRSTS);
        }
        else if (isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterTypes)) {
            this.scanOverCodeTo(...NAMESPACE_DECL_FIRSTS);
        }
        else {
            let fkind: "namespace" | "predicate" | "chktest" | "errtest" = "namespace";
            if(this.testFollows(KW_predicate) || this.testFollows(KW_recursive, KW_predicate) || this.testFollows(KW_recursive_q, KW_predicate)) {
                fkind = "predicate";
            }
            else if(this.testFollows(KW_chktest)) {
                fkind = "chktest";
            }
            else if(this.testFollows(KW_errtest)) {
                fkind = "errtest";
            }
            else {
                ;
            }

            const fdecl = this.parseFunctionInvokeDecl(fkind, attributes, new Set<string>());

            if(fdecl !== undefined) {
                this.env.currentNamespace.functions.push(fdecl as NamespaceFunctionDecl);
            }
        }
    }

    private parseProvides(sinfo: SourceInfo, endtoken: string[]): TypeSignature[] {
        assert(isParsePhase_Enabled(this.currentPhase, ParsePhase_CompleteParse));

        let provides: TypeSignature[] = [];
        if (this.testAndConsumeTokenIf(KW_provides)) {
            while (!endtoken.some((tok) => this.testToken(tok))) {
                this.consumeTokenIf(SYM_coma);
                provides.push(this.parseTypeSignature());
            }
        }
        
        if (this.env.currentNamespace.fullnamespace.ns[0] !== "Core") {
            const corens = this.env.assembly.getToplevelNamespace("Core");
            const otype = corens.typedecls.find((td) => td.name === "Object") as AbstractNominalTypeDecl;

            provides.push(new NominalTypeSignature(sinfo, ["Core"], [{tname: "Object", terms: []}], [], undefined, otype));
        }

        return provides;
    }

    private parseConstMember(constMembers: ConstMemberDecl[] | undefined, allMemberNames: Set<string>, attributes: DeclarationAttibute[]) {
        assert(isParsePhase_Enabled(this.currentPhase, ParsePhase_CompleteParse));

        const sinfo = this.lexer.peekNext().getSourceInfo();
        this.ensureAndConsumeToken(KW_const, "const member");

        this.ensureToken(TokenStrings.IdentifierName, "const member");
        const sname = this.consumeTokenAndGetValue();

        this.ensureAndConsumeToken(SYM_colon, "const member");
        const stype = this.parseTypeSignature();

        this.ensureAndConsumeToken(SYM_eq, "const member");
        const value = this.parseConstExpression(stype);

        if(constMembers === undefined) {
            this.recordErrorGeneral(sinfo, "Cannot have a const member on this type");
        }
        if(allMemberNames.has(sname)) {
            this.recordErrorGeneral(sinfo, `Duplicate const member ${sname}`);
        }
        allMemberNames.add(sname);

        if(constMembers !== undefined && !constMembers.some((cm) => cm.name === sname)) {
            constMembers.push(new ConstMemberDecl(this.env.currentFile, sinfo, attributes, sname, stype, value));
        }

        this.ensureAndConsumeToken(SYM_semicolon, "const member");
    }

    private parseMemberFunction(memberFunctions: TypeFunctionDecl[] | undefined, allMemberNames: Set<string>, attributes: DeclarationAttibute[], typeTerms: Set<string>) {
        assert(isParsePhase_Enabled(this.currentPhase, ParsePhase_CompleteParse));

        const sinfo = this.lexer.peekNext().getSourceInfo();
        const fdecl = this.parseFunctionInvokeDecl("typescope", attributes, typeTerms);

        if(memberFunctions === undefined) {
            this.recordErrorGeneral(sinfo, "Cannot have a function member on this type");
        }
        if(fdecl === undefined) {
            return;
        } 
        
        if(allMemberNames.has(fdecl.name)) {
            this.recordErrorGeneral(sinfo, `Duplicate const member ${fdecl.name}`);
        }
        allMemberNames.add(fdecl.name);

        if(memberFunctions !== undefined && !memberFunctions.some((cm) => cm.name === fdecl.name)) {
            memberFunctions.push(fdecl);
        }
    }

    private parseMemberField(memberFields: MemberFieldDecl[] | undefined, allMemberNames: Set<string>, attributes: DeclarationAttibute[]) {
        assert(isParsePhase_Enabled(this.currentPhase, ParsePhase_CompleteParse));

        const sinfo = this.lexer.peekNext().getSourceInfo();
        this.ensureAndConsumeToken(KW_field, "member field");

        this.ensureToken(TokenStrings.IdentifierName, "member field");
        const fname = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(SYM_colon, "member field");
        const ftype = this.parseTypeSignature();

        let ivalue: ConstantExpressionValue | undefined = undefined;
        if (this.testAndConsumeTokenIf(SYM_eq)) {
            ivalue = this.parseConstExpression(ftype);
        }

        if(memberFields === undefined) {
            this.recordErrorGeneral(sinfo, "Cannot have a const member on this type");
        }
        if(allMemberNames.has(fname)) {
            this.recordErrorGeneral(sinfo, `Duplicate const member ${fname}`);
        }
        allMemberNames.add(fname);

        if(memberFields !== undefined && !memberFields.some((cm) => cm.name === fname)) {
            memberFields.push(new MemberFieldDecl(this.env.currentFile, sinfo, attributes, fname, ftype, ivalue));
        }

        this.ensureAndConsumeToken(SYM_semicolon, "member field");
    }

    private parseMemberMethod(memberMethods: MethodDecl[] | undefined, allMemberNames: Set<string>, attributes: DeclarationAttibute[], typeTerms: Set<string>) {
        assert(isParsePhase_Enabled(this.currentPhase, ParsePhase_CompleteParse));

        const sinfo = this.lexer.peekNext().getSourceInfo();
        const mdecl = this.parseMethodInvokeDecl(false, attributes, typeTerms) as MethodDecl;

        if(memberMethods === undefined) {
            this.recordErrorGeneral(sinfo, "Cannot have a method member on this type");
        }
        if(mdecl === undefined) {
            return;
        } 
        
        if(allMemberNames.has(mdecl.name)) {
            this.recordErrorGeneral(sinfo, `Duplicate const member ${mdecl.name}`);
        }
        allMemberNames.add(mdecl.name);

        if(memberMethods !== undefined && !memberMethods.some((cm) => cm.name === mdecl.name)) {
            memberMethods.push(mdecl);
        }
    }

    private parseTaskMemberMethod(taskMemberMethods: TaskMethodDecl[] | undefined, allMemberNames: Set<string>, attributes: DeclarationAttibute[], typeTerms: Set<string>) {
        assert(isParsePhase_Enabled(this.currentPhase, ParsePhase_CompleteParse));

        const sinfo = this.lexer.peekNext().getSourceInfo();
        const mdecl = this.parseMethodInvokeDecl(true, attributes, typeTerms) as TaskMethodDecl;

        if(taskMemberMethods === undefined) {
            this.recordErrorGeneral(sinfo, "Cannot have a task method member on this type");
        }
        if(mdecl === undefined) {
            return;
        } 
        
        if(allMemberNames.has(mdecl.name)) {
            this.recordErrorGeneral(sinfo, `Duplicate const member ${mdecl.name}`);
        }
        allMemberNames.add(mdecl.name);

        if(taskMemberMethods !== undefined && !taskMemberMethods.some((cm) => cm.name === mdecl.name)) {
            taskMemberMethods.push(mdecl);
        }
    }

    private parseTaskMemberAction(taskMemberAction: TaskActionDecl[] | undefined, allMemberNames: Set<string>, attributes: DeclarationAttibute[], typeTerms: Set<string>) {
        assert(isParsePhase_Enabled(this.currentPhase, ParsePhase_CompleteParse));

        const sinfo = this.lexer.peekNext().getSourceInfo();
        const adecl = this.parseActionInvokeDecl(attributes, typeTerms) ;

        if(taskMemberAction === undefined) {
            this.recordErrorGeneral(sinfo, "Cannot have a task method member on this type");
        }
        if(adecl === undefined) {
            return;
        } 
        
        if(allMemberNames.has(adecl.name)) {
            this.recordErrorGeneral(sinfo, `Duplicate const member ${adecl.name}`);
        }
        allMemberNames.add(adecl.name);

        if(taskMemberAction !== undefined && !taskMemberAction.some((cm) => cm.name === adecl.name)) {
            taskMemberAction.push(adecl);
        }
    }

    private parseInvariantsInto(invs: InvariantDecl[] | undefined, vdates: ValidateDecl[] | undefined, typeTerms: Set<string>) {
        assert(isParsePhase_Enabled(this.currentPhase, ParsePhase_CompleteParse));
        const sinfo = this.lexer.peekNext().getSourceInfo();

        this.env.pushStandardFunctionScope([], typeTerms, this.wellknownTypes.get("Bool") as TypeSignature);
        while (this.testToken(KW_invariant) || this.testToken(KW_validate)) {
            const isvalidate = this.testToken(KW_validate);
            this.consumeToken();

            let tag: string | undefined = undefined;
            if(this.testAndConsumeTokenIf(SYM_lbrack)) {
                if(this.ensureToken(TokenStrings.ASCIIString, "invariant/validate tag")) {
                    tag = this.consumeTokenAndGetValue();
                }
            
                this.ensureAndConsumeToken(SYM_rbrack, "invariant/validate tag");
            }

            if(isvalidate) {
                const exp = this.parseConstExpression(this.wellknownTypes.get("Bool") as TypeSignature);

                if(vdates === undefined) {
                    this.recordErrorGeneral(sinfo, "Cannot have a validate on this type");
                }
                else {
                    vdates.push(new ValidateDecl(this.env.currentFile, sinfo, tag, exp));
                }
            }
            else {
                const level = this.parseBuildInfo(KW_release);
                const exp = this.parseConstExpression(this.wellknownTypes.get("Bool") as TypeSignature);

                if(invs === undefined) {
                    this.recordErrorGeneral(sinfo, "Cannot have an invariant on this type");
                }
                else {
                    invs.push(new InvariantDecl(this.env.currentFile, sinfo, tag, level, exp));
                }
            }

            this.ensureAndConsumeToken(SYM_semicolon, "invariant");
        }
        this.env.popStandardFunctionScope();
    }

    private parseOOPMembersCommonAll(istask: boolean, specialConcept: InternalConceptTypeDecl | undefined, typeTerms: Set<string>,
        invariants: InvariantDecl[] | undefined, validates: ValidateDecl[] | undefined,
        constMembers: ConstMemberDecl[] | undefined, functionMembers: TypeFunctionDecl[] | undefined, 
        memberFields: MemberFieldDecl[] | undefined, memberMethods: MethodDecl[] | undefined, 
        taskMemberMethods: TaskMethodDecl[] | undefined, taskMemberAction: TaskActionDecl[] | undefined 
        ) {
        let allMemberNames = new Set<string>();

        while (!this.testToken(SYM_rbrace)) {
            let attributes: DeclarationAttibute[] = [];
            while(this.testToken(TokenStrings.Attribute)) {
                const attr = this.parseAttribute();
                attributes.push(attr);
            }

            const sinfo = this.lexer.peekNext().getSourceInfo();
            if (this.testToken(KW_field)) {
                this.parseMemberField(memberFields, allMemberNames, attributes);
            }
            else if (this.testToken(KW_invariant) || this.testToken(KW_validate)) {
                this.parseInvariantsInto(invariants, validates, typeTerms);
            }
            else if (this.testToken(KW_const)) {
                this.parseConstMember(constMembers, allMemberNames, attributes);
            }
            else if (this.testToken(KW_invariant) || this.testToken(KW_validate)) {
                if(attributes.length !== 0) {
                    this.recordErrorGeneral(sinfo, "Cannot have attributes on invariants/validates");
                }

                this.parseInvariantsInto(invariants, validates, typeTerms);
            }
            else if (this.testToken(KW_function) || this.testFollows(KW_recursive, KW_function) || this.testFollows(KW_recursive_q, KW_function)) {
                this.parseMemberFunction(functionMembers, allMemberNames, attributes, typeTerms);
            }
            else if(this.testToken(KW_ref) || this.testFollows(KW_recursive, KW_ref) || this.testFollows(KW_recursive_q, KW_ref)) {
                if(istask) {
                    this.parseTaskMemberMethod(taskMemberMethods, allMemberNames, attributes, typeTerms);
                }
                else {
                    this.parseMemberMethod(memberMethods, allMemberNames, attributes, typeTerms);
                }
            }
            else if(this.testToken(KW_ref) || this.testFollows(KW_recursive, KW_method) || this.testFollows(KW_recursive_q, KW_method)) {
                if(istask) {
                    this.parseTaskMemberMethod(taskMemberMethods, allMemberNames, attributes, typeTerms);
                }
                else {
                    this.parseMemberMethod(memberMethods, allMemberNames, attributes, typeTerms);
                }
            }
            else if(this.testToken(KW_action)) {
                this.parseTaskMemberAction(taskMemberAction, allMemberNames, attributes, typeTerms);
            }
            else if(this.testToken(KW_entity)) {
                if(specialConcept === undefined) {
                    this.recordErrorGeneral(this.lexer.peekNext().getSourceInfo(), "Cannot have nested entities on this type");
                }
                else {
                    this.parseNestedEntity(specialConcept, allMemberNames, attributes);
                }
            }
            else {
                this.recordErrorGeneral(sinfo, `Unknown member ${this.peekTokenData()}`);

                //scan to the next declaration or end brace
                const rpos = this.scanToSyncPos(SYM_rbrace, ...TYPE_DECL_FIRSTS);
                if(rpos === undefined) {
                    this.lexer.currentState().recover();
                    return; 
                }
                else {
                    this.lexer.currentState().skipToPosition(rpos);
                }
            }
        }
    }

    private parseNestedEntity(specialConcept: InternalConceptTypeDecl, allMemberNames: Set<string>, attributes: DeclarationAttibute[]) {
        //special Concept should be Result or APIResult and this should be one of the known subtypes

        assert(false, "Not implemented");
    }

    private parseEntityRegisterType(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, hasTerms: boolean) {
        xxxx;
    }

    private parseEntityCompleteParse(sinfo: SourceInfo, attributes: DeclarationAttibute[]) {
        xxxx;
    }

    private parseEntity(attributes: DeclarationAttibute[]) {
        assert(isParsePhase_Enabled(this.currentPhase, ParsePhase_CompleteParse));

        const sinfo = this.lexer.peekNext().getSourceInfo();

        this.ensureAndConsumeToken(KW_entity, "entity declaration");
        this.ensureToken(TokenStrings.IdentifierName, "entity declaration");

        const ename = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        const provides = this.parseProvides(sinfo, currentDecl.ns === "Core", [SYM_lbrace]);

        try {
            this.setRecover(this.scanCodeParens());
            this.ensureAndConsumeToken(SYM_lbrace, "entity declaration");

            const thisType = new NominalTypeSignature(sinfo, currentDecl.ns, [...currentTypeNest, ename], [...terms, ...currentTermNest].map((term) => new TemplateTypeSignature(sinfo, term.name)));

            const invariants: InvariantDecl[] = [];
            const validates: ValidateDecl[] = [];
            const staticMembers: StaticMemberDecl[] = [];
            const staticFunctions: StaticFunctionDecl[] = [];
            const memberFields: MemberFieldDecl[] = [];
            const memberMethods: MemberMethodDecl[] = [];
            const nestedEntities = new Map<string, EntityTypeDecl>();
            const statuseffect = new TaskStatusEffect([]);
            const eventeffect = new TaskEventEffect([]);
            const enveffect = new TaskEnvironmentEffect([]);
            this.parseOOPMembersCommon(sinfo, false, thisType, currentDecl, [...currentTypeNest, ename], [...currentTermNest, ...terms], new Set<string>([...currentTermNest, ...terms].map((tt) => tt.name)), nestedEntities, invariants, validates, staticMembers, staticFunctions, memberFields, memberMethods, [], statuseffect, eventeffect, enveffect, []);

            this.ensureAndConsumeToken(SYM_rbrace, "entity declaration");

            if (currentDecl.checkDeclNameClash([...currentTypeNest, ename].join("::"))) {
                this.raiseError(line, "Collision between object and other names");
            }

            if(currentDecl.ns === "Core") {
                if(ename === "StringOf") {
                    attributes.push("__stringof_type");
                }
                else if(ename === "ASCIIStringOf") {
                    attributes.push("__asciistringof_type");
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
                else if(ename === "MapEntry") {
                    attributes.push("__mapentry_type");
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
                else if(ename === "Path") {
                    attributes.push("__path_type");
                }
                else if(ename === "PathFragment") {
                    attributes.push("__pathfragment_type");
                }
                else if(ename === "PathGlob") {
                    attributes.push("__pathglob_type");
                }
                else {
                    //not special
                }
            }

            this.clearRecover();

            const fename = [...currentTypeNest, ename].join("::");
            const feterms = [...currentTermNest, ...terms];

            const edecl = new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), attributes, currentDecl.ns, fename, feterms, provides, invariants, validates, staticMembers, staticFunctions, memberFields, memberMethods, nestedEntities);
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

    private parseConcept(attributes: DeclarationAttibute[]) {
        assert(isParsePhase_Enabled(this.currentPhase, ParsePhase_CompleteParse));

        const sinfo = this.lexer.peekNext().getSourceInfo();

        this.ensureAndConsumeToken(KW_concept, "concept declaration");
        this.ensureToken(TokenStrings.IdentifierName, "concept declaration");

        const cname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        const provides = this.parseProvides(sinfo, currentDecl.ns === "Core", [SYM_lbrace]);

        try {
            this.setRecover(this.scanCodeParens());
            this.ensureAndConsumeToken(SYM_lbrace, "concept declaration");

            const thisType = new NominalTypeSignature(sinfo, currentDecl.ns, [cname], terms.map((term) => new TemplateTypeSignature(sinfo, term.name)));

            const invariants: InvariantDecl[] = [];
            const validates: ValidateDecl[] = [];
            const staticMembers: StaticMemberDecl[] = [];
            const staticFunctions: StaticFunctionDecl[] = [];
            const memberFields: MemberFieldDecl[] = [];
            const memberMethods: MemberMethodDecl[] = [];
            const nestedEntities = new Map<string, EntityTypeDecl>();
            const statuseffect = new TaskStatusEffect([]);
            const eventeffect = new TaskEventEffect([]);
            const enveffect = new TaskEnvironmentEffect([]);
            this.parseOOPMembersCommon(sinfo, false, thisType, currentDecl, [cname], [...terms], new Set<string>(terms.map((tt) => tt.name)), nestedEntities, invariants, validates, staticMembers, staticFunctions, memberFields, memberMethods, [], statuseffect, eventeffect, enveffect, []);

            this.ensureAndConsumeToken(SYM_rbrace, "concept declaration");

            if (currentDecl.checkDeclNameClash(cname)) {
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

            const cdecl = new ConceptTypeDecl(sinfo, this.m_penv.getCurrentFile(), attributes, currentDecl.ns, cname, terms, provides, invariants, validates, staticMembers, staticFunctions, memberFields, memberMethods, nestedEntities);
            currentDecl.concepts.set(cname, cdecl);
            this.m_penv.assembly.addConceptDecl((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + cname, cdecl);
        }
        catch (ex) {
            this.processRecover();
        }
    }

    

    private parseTask(currentDecl: NamespaceDeclaration, currentTermNest: TemplateTermDecl[]) {
        const line = this.getCurrentLine();

        //[attr] task NAME[T where C...] provides {...}
        const attributes = this.parseAttributes();

        const sinfo = this.getCurrentSrcInfo();
        this.ensureAndConsumeToken(KW_task, "task declaration");
        this.ensureToken(TokenStrings.Type, "task declaration");

        const ename = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();

        try {
            this.setRecover(this.scanCodeParens());
            this.ensureAndConsumeToken(SYM_lbrace, "task declaration");

            const thisType = new NominalTypeSignature(sinfo, currentDecl.ns, [ename], [...terms, ...currentTermNest].map((term) => new TemplateTypeSignature(sinfo, term.name)));

            const invariants: InvariantDecl[] = [];
            const validates: ValidateDecl[] = [];
            const staticMembers: StaticMemberDecl[] = [];
            const staticFunctions: StaticFunctionDecl[] = [];
            const memberFields: MemberFieldDecl[] = [];
            const memberMethods: MemberMethodDecl[] = [];
            const nestedEntities = new Map<string, EntityTypeDecl>();
            
            const controlfields: ControlFieldDecl[] = [];

            const statuseffect = new TaskStatusEffect([]);
            const eventeffect = new TaskEventEffect([]);
            const enveffect = new TaskEnvironmentEffect([]);
            const resourceeffects: TaskResourceEffect[] = [];
            this.parseOOPMembersCommon(sinfo, true, thisType, currentDecl, [ename], [...currentTermNest, ...terms], new Set<string>([...currentTermNest, ...terms].map((tt) => tt.name)), nestedEntities, invariants, validates, staticMembers, staticFunctions, memberFields, memberMethods, controlfields, statuseffect, eventeffect, enveffect, resourceeffects);

            if(invariants.length !== 0) {
                this.raiseError(sinfo.line, "Cannot define invariants on tasks (only validates)");
            }

            if(nestedEntities.size !== 0) {
                this.raiseError(sinfo.line, "Cannot define nested types on tasks");
            }

            this.ensureAndConsumeToken(SYM_rbrace, "task declaration");

            if (currentDecl.checkDeclNameClash(ename)) {
                this.raiseError(line, "Collision between task and other names");
            }

            this.clearRecover();

            const feterms = [...currentTermNest, ...terms];

            const mainfunc = staticFunctions.find((ff) => ff.name === "main");
            if(mainfunc === undefined) {
                this.raiseError(sinfo.line, "Does not have a \"main\" function defined")
            }

            const actions = memberMethods.filter((mf) => mf.attributes.includes("task_action"));
            const onfuncs = {
                onCanel: memberMethods.find((mf) => mf.name === "onCancel"),
                onFailure: memberMethods.find((mf) => mf.name === "onFailure"), 
                onTimeout: memberMethods.find((mf) => mf.name === "onTimeout")
            };

            const lfuncs = {
                logStart: memberMethods.find((mf) => mf.name === "logStart"),
                logEnd: memberMethods.find((mf) => mf.name === "logEnd"), 
                taskEnsures: memberMethods.find((mf) => mf.name === "taskEnsures"),
                taskWarns: memberMethods.find((mf) => mf.name === "taskWarns")
            };

            const edecl = new TaskTypeDecl(sinfo, this.m_penv.getCurrentFile(), attributes, currentDecl.ns, ename, feterms, validates, staticMembers, staticFunctions, memberFields, memberMethods, controlfields, mainfunc as StaticFunctionDecl, actions, onfuncs, lfuncs, statuseffect, eventeffect, enveffect, resourceeffects);
            this.m_penv.assembly.addTaskDecl((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + ename, edecl);
            currentDecl.tasks.set(ename, edecl);
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

        this.ensureAndConsumeToken(KW_enum, "enum declaration");
        this.ensureToken(TokenStrings.Type, "enum declaration");

        const ename = this.consumeTokenAndGetValue();
        const etype = new NominalTypeSignature(sinfo, currentDecl.ns, [ename]);

        if (currentDecl.checkDeclNameClash(ename)) {
            this.raiseError(line, "Collision between object and other names");
        }

        try {
            this.setRecover(this.scanCodeParens());

            const enums = this.parseListOf<string>("enum declaration", SYM_lbrace, SYM_rbrace, SYM_coma, () => {
                this.ensureToken(TokenStrings.Identifier, "enum member");
                return this.consumeTokenAndGetValue();
            });
            
            const provides = [
                [new NominalTypeSignature(sinfo, "Core", ["Some"]), undefined],
                [new NominalTypeSignature(sinfo, "Core", ["KeyType"]), undefined]
            ] as [TypeSignature, TypeConditionRestriction | undefined][];

            const invariants: InvariantDecl[] = [];
            const validates: ValidateDecl[] = [];
            const staticMembers: StaticMemberDecl[] = [];
            const staticFunctions: StaticFunctionDecl[] = [];
            const memberFields: MemberFieldDecl[] = [];
            const memberMethods: MemberMethodDecl[] = [];
    
            for(let i = 0; i < enums.length; ++i) {
                const exp = new LiteralIntegralExpression(sinfo, i.toString() + "n", this.m_penv.SpecialNatSignature);
                const enm = new StaticMemberDecl(sinfo, this.m_penv.getCurrentFile(), ["__enum"], enums[i], etype, new ConstantExpressionValue(exp, new Set<string>()));
                staticMembers.push(enm);
            }

            if(this.testAndConsumeTokenIf(SYM_amp)) {
                this.setRecover(this.scanCodeParens());
                this.ensureAndConsumeToken(SYM_lbrace, "enum extension code");
    
                const thisType = new NominalTypeSignature(sinfo, currentDecl.ns, [ename], []);
    
                const nestedEntities = new Map<string, EntityTypeDecl>();
                const statuseffect = new TaskStatusEffect([]);
                const eventeffect = new TaskEventEffect([]);
                const enveffect = new TaskEnvironmentEffect([]);
                this.parseOOPMembersCommon(sinfo, false, thisType, currentDecl, [ename], [], new Set<string>(), nestedEntities, invariants, validates, staticMembers, staticFunctions, memberFields, memberMethods, [], statuseffect, eventeffect, enveffect, []);
    
                if(invariants.length !== 0 || validates.length !== 0) {
                    this.raiseError(sinfo.line, "cannot declare invariants on enum");
                }

                if(memberFields.length !== 0) {
                    this.raiseError(sinfo.line, "cannot declare member fields on enum");
                }

                this.ensureAndConsumeToken(SYM_rbrace, "enum extension code");
    
                this.clearRecover();
            }

            if (currentDecl.checkDeclNameClash(ename)) {
                this.raiseError(line, "Collision between object and other names");
            }

            if(invariants.length !== 0) {
                this.raiseError(line, "Cannot have invariant function on Enum types");
            }

            attributes.push("__enum_type", "__constructable");

            this.clearRecover();
            currentDecl.objects.set(ename, new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), attributes, currentDecl.ns, ename, [], provides, invariants, validates, staticMembers, staticFunctions, memberFields, memberMethods, new Map<string, EntityTypeDecl>()));
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
       
        this.ensureAndConsumeToken(KW_typedecl, "typedecl");

        const iname = this.consumeTokenAndGetValue();
        if (currentDecl.checkDeclNameClash(iname)) {
            this.raiseError(line, "Collision between object and other names");
        }

        this.ensureAndConsumeToken(SYM_eq, "typedecl");
        if (this.testToken(TokenStrings.Regex)) {
            //[attr] typedecl NAME = regex;

            const vregex = this.consumeTokenAndGetValue();
            this.ensureAndConsumeToken(SYM_semicolon, "Validator");

            const re = BSQRegex.parse(this.m_penv.getCurrentNamespace(), iname, vregex);
            if (typeof (re) === "string") {
                this.raiseError(this.getCurrentLine(), re);
            }

            const param = new FunctionParameter("arg", new NominalTypeSignature(sinfo, "Core", ["String"]), undefined);

            const acceptsbody = new BodyImplementation(this.m_penv.getCurrentFile(), "validator_accepts");
            const acceptsinvoke = new InvokeDecl("Core", sinfo, sinfo, this.m_penv.getCurrentFile(), ["__safe"], "no", [], undefined, [param], false, new NominalTypeSignature(sinfo, "Core", ["Bool"]), [], [], [], false, false, new Set<string>(), new Set<string>(), acceptsbody);
            const accepts = new StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), ["__safe"], "accepts", acceptsinvoke);
            const provides = [[new NominalTypeSignature(sinfo, "Core", ["Some"]), undefined], [new NominalTypeSignature(sinfo, "Core", ["Validator"]), undefined]] as [TypeSignature, TypeConditionRestriction | undefined][];
            const validatortype = new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), ["__validator_type", ...attributes], currentDecl.ns, iname, [], provides, [], [], [], [accepts], [], [], new Map<string, EntityTypeDecl>());

            currentDecl.objects.set(iname, validatortype);
            this.m_penv.assembly.addObjectDecl((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + iname, currentDecl.objects.get(iname) as EntityTypeDecl);
            this.m_penv.assembly.addValidatorRegex(re as BSQRegex);
        }
        else if(this.testToken(SYM_lbrace)) {
            //[attr] typedecl NAME = pathvalidator;
            
            const vv = this.parsePathValidator(currentDecl, iname);
            this.ensureAndConsumeToken(SYM_semicolon, "PathValidator");

            const param = new FunctionParameter("arg", new NominalTypeSignature(sinfo, "Core", ["String"]), undefined);

            const acceptsbody = new BodyImplementation(this.m_penv.getCurrentFile(), "pathvalidator_accepts");
            const acceptsinvoke = new InvokeDecl("Core", sinfo, sinfo, this.m_penv.getCurrentFile(), ["__safe"], "no", [], undefined, [param], false, new NominalTypeSignature(sinfo, "Core", ["Bool"]), [], [], [], false, false, new Set<string>(), new Set<string>(), acceptsbody);
            const accepts = new StaticFunctionDecl(sinfo, this.m_penv.getCurrentFile(), ["__safe"], "accepts", acceptsinvoke);
            const provides = [[new NominalTypeSignature(sinfo, "Core", ["Some"]), undefined], [new NominalTypeSignature(sinfo, "Core", ["PathValidator"]), undefined]] as [TypeSignature, TypeConditionRestriction | undefined][];
            const validatortype = new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), ["__pathvalidator_type", ...attributes], currentDecl.ns, iname, [], provides, [], [], [], [accepts], [], [], new Map<string, EntityTypeDecl>());

            currentDecl.objects.set(iname, validatortype);
            this.m_penv.assembly.addObjectDecl((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + iname, currentDecl.objects.get(iname) as EntityTypeDecl);
            this.m_penv.assembly.addValidatorPath(vv);
        }
        else {
            //[attr] typedecl NAME = PRIMITIVE [& {...}];

            const idval = this.parseNominalType() as NominalTypeSignature;

            let provides = [[new NominalTypeSignature(sinfo, "Core", ["Some"]), undefined]] as [TypeSignature, TypeConditionRestriction | undefined][];
            provides.push([new NominalTypeSignature(sinfo, "Core", ["KeyType"]), new TypeConditionRestriction([new TemplateTypeRestriction(idval, false, false, new NominalTypeSignature(sinfo, "Core", ["KeyType"]))])]);

            const invariants: InvariantDecl[] = [];
            const validates: ValidateDecl[] = [];
            const staticMembers: StaticMemberDecl[] = [];
            const staticFunctions: StaticFunctionDecl[] = [];
            const memberFields: MemberFieldDecl[] = [];
            const memberMethods: MemberMethodDecl[] = [];

            if (this.testAndConsumeTokenIf(SYM_amp)) {
                this.setRecover(this.scanCodeParens());
                this.ensureAndConsumeToken(SYM_lbrace, "typedecl");

                const thisType = new NominalTypeSignature(sinfo, currentDecl.ns, [iname], []);

                const nestedEntities = new Map<string, EntityTypeDecl>();
                const statuseffect = new TaskStatusEffect([]);
                const eventeffect = new TaskEventEffect([]);
                const enveffect = new TaskEnvironmentEffect([]);
                this.parseOOPMembersCommon(sinfo, false, thisType, currentDecl, [iname], [], new Set<string>(), nestedEntities, invariants, validates, staticMembers, staticFunctions, memberFields, memberMethods, [], statuseffect, eventeffect, enveffect, []);

                this.ensureAndConsumeToken(SYM_rbrace, "typedecl");

                if (currentDecl.checkDeclNameClash(iname)) {
                    this.raiseError(line, "Collision between concept and other names");
                }

                this.clearRecover();
            }
            else {
                this.ensureAndConsumeToken(SYM_semicolon, "typedecl");
            }

            if(memberFields.length !== 0) {
                this.raiseError(sinfo.line, "Cannot declare additional member fields on typedecl");
            }

            const valuebody = new BodyImplementation(this.m_penv.getCurrentFile(), "special_extract");
            const valuedecl = new InvokeDecl("Core", sinfo, sinfo, this.m_penv.getCurrentFile(), ["__safe"], "no", [], undefined, [], false, idval, [], [], [], false, false, new Set<string>(), new Set<string>(), valuebody);
            const value = new MemberMethodDecl(sinfo, this.m_penv.getCurrentFile(), ["__safe"], "value", valuedecl);

            //
            //TODO: maybe want to do a special underlying operator that looks like a method to just get the base type
            //      we will need to do some fancy resolution on the type since we don't know the base type yet
            //      maybe even make this a string, int, float as the name of the method
            //

            memberMethods.push(value);

            attributes.push("__typedprimitive", "__constructable");

            currentDecl.objects.set(iname, new EntityTypeDecl(sinfo, this.m_penv.getCurrentFile(), attributes, currentDecl.ns, iname, [], provides, invariants, validates, staticMembers, staticFunctions, memberFields, memberMethods, new Map<string, EntityTypeDecl>()));
            this.m_penv.assembly.addObjectDecl((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + iname, currentDecl.objects.get(iname) as EntityTypeDecl);
        }
    }

    private parseDataTypeDecl(currentDecl: NamespaceDeclaration) {
        const line = this.getCurrentLine();
        const sinfo = this.getCurrentSrcInfo();
       
        this.ensureAndConsumeToken(KW_datatype, "datatype");

        const iname = this.consumeTokenAndGetValue();
        const terms = this.parseTermDeclarations();
        if (currentDecl.checkDeclNameClash(iname)) {
            this.raiseError(line, "Collision between object and other names");
        }

        //[attr] datatype NAME<...> [provides ... ] [using {...}] of
        // Foo {...}
        // | ...
        // [& {...}] | ;

        const concepttype = new NominalTypeSignature(sinfo, currentDecl.ns, [iname]);

        const provides = this.parseProvides(sinfo, currentDecl.ns === "Core", [KW_of, KW_using]);

        let complexheader = false;
        let cinvariants: InvariantDecl[] = [];
        let cvalidates: ValidateDecl[] = [];
        let cstaticMembers: StaticMemberDecl[] = [];
        let cstaticFunctions: StaticFunctionDecl[] = [];
        let cusing: MemberFieldDecl[] = [];
        let cmemberMethods: MemberMethodDecl[] = [];
        if (this.testAndConsumeTokenIf("using")) {
            if (this.testFollows(SYM_lbrace, TokenStrings.Identifier) && !Lexer.isAttributeKW(this.peekTokenData(1))) {
                cusing = this.parseListOf<MemberFieldDecl>("datatype concept", SYM_lbrace, SYM_rbrace, SYM_coma, () => {
                    const mfinfo = this.getCurrentSrcInfo();

                    this.ensureToken(TokenStrings.Identifier, "datatype concept field");
                    const name = this.consumeTokenAndGetValue();
                    this.ensureAndConsumeToken(SYM_colon, "datatype concept field");

                    const ttype = this.parseTypeSignature();
                    return new MemberFieldDecl(mfinfo, this.m_penv.getCurrentFile(), [], name, ttype);
                });
            }
            else {
                this.setRecover(this.scanCodeParens());
                this.ensureAndConsumeToken(SYM_lbrace, "datatype declaration");

                const thisType = new NominalTypeSignature(sinfo, currentDecl.ns, [iname], []);

                const nestedEntities = new Map<string, EntityTypeDecl>();
                const statuseffect = new TaskStatusEffect([]);
                const eventeffect = new TaskEventEffect([]);
                const enveffect = new TaskEnvironmentEffect([]);
                this.parseOOPMembersCommon(sinfo, false, thisType, currentDecl, [iname], [...terms], new Set<string>(terms.map((tt) => tt.name)), nestedEntities, cinvariants, cvalidates, cstaticMembers, cstaticFunctions, cusing, cmemberMethods, [], statuseffect, eventeffect, enveffect, []);

                this.ensureAndConsumeToken(SYM_rbrace, "datatype declaration");
                complexheader = cstaticMembers.length !== 0 || cstaticFunctions.length !== 0 || cmemberMethods.length !== 0;
            }
        }

        this.ensureAndConsumeToken(KW_of, "datatype");

        const edecls: EntityTypeDecl[] = [];
        while (!this.testToken(SYM_semicolon) && !this.testToken(SYM_amp)) {
            if (this.testToken(SYM_bar)) {
                this.consumeToken();
            }
            let esinfo = this.getCurrentSrcInfo();

            this.ensureToken(TokenStrings.Type, "datatype entities");
            const ename = this.consumeTokenAndGetValue();
            if (currentDecl.checkDeclNameClash(ename)) {
                this.raiseError(line, "Collision between object and other names");
            }

            const invariants: InvariantDecl[] = [];
            const validates: ValidateDecl[] = [];
            const staticMembers: StaticMemberDecl[] = [];
            const staticFunctions: StaticFunctionDecl[] = [];
            let memberFields: MemberFieldDecl[] = [];
            const memberMethods: MemberMethodDecl[] = [];
            if (this.testToken(SYM_lbrace)) {
                if (this.testFollows(SYM_lbrace, TokenStrings.Identifier) && !Lexer.isAttributeKW(this.peekTokenData(1))) {
                    memberFields = this.parseListOf<MemberFieldDecl>("datatype entity", SYM_lbrace, SYM_rbrace, SYM_coma, () => {
                        const mfinfo = this.getCurrentSrcInfo();

                        this.ensureToken(TokenStrings.Identifier, "datatype entity field");
                        const name = this.consumeTokenAndGetValue();
                        this.ensureAndConsumeToken(SYM_colon, "datatype entity field");

                        const ttype = this.parseTypeSignature();
                        return new MemberFieldDecl(mfinfo, this.m_penv.getCurrentFile(), [], name, ttype);
                    });
                }
                else {
                    this.setRecover(this.scanCodeParens());
                    this.ensureAndConsumeToken(SYM_lbrace, "datatype entry");

                    const thisType = new NominalTypeSignature(esinfo, currentDecl.ns, [ename], []);

                    const nestedEntities = new Map<string, EntityTypeDecl>();
                    const statuseffect = new TaskStatusEffect([]);
                    const eventeffect = new TaskEventEffect([]);
                    const enveffect = new TaskEnvironmentEffect([]);
                    this.parseOOPMembersCommon(esinfo, false, thisType, currentDecl, [ename], [...terms], new Set<string>(terms.map((tt) => tt.name)), nestedEntities, invariants, validates, staticMembers, staticFunctions, memberFields, memberMethods, [], statuseffect, eventeffect, enveffect, []);

                    this.ensureAndConsumeToken(SYM_rbrace, "datatype entry");
                }
            }

            const eprovides = [[concepttype, undefined]] as [TypeSignature, TypeConditionRestriction | undefined][];
            const edecl = new EntityTypeDecl(esinfo, this.m_penv.getCurrentFile(), ["__adt_entity_type"], currentDecl.ns, ename, terms, eprovides, invariants, validates, staticMembers, staticFunctions, memberFields, memberMethods, new Map<string, EntityTypeDecl>());

            edecls.push(edecl);
            currentDecl.objects.set(ename, edecl);
            this.m_penv.assembly.addObjectDecl((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + ename, currentDecl.objects.get(ename) as EntityTypeDecl);
        }

        if (this.testAndConsumeTokenIf(SYM_amp)) {
            this.setRecover(this.scanCodeParens());
            this.ensureAndConsumeToken(SYM_lbrace, "datatype");

            if (complexheader) {
                this.raiseError(this.getCurrentLine(), "Cannot define complex ADT++ concept in multiple parts");
            }

            const thisType = new NominalTypeSignature(sinfo, currentDecl.ns, [iname], []);

            const nestedEntities = new Map<string, EntityTypeDecl>();
            const memberFields: MemberFieldDecl[] = [];
            const statuseffect = new TaskStatusEffect([]);
            const eventeffect = new TaskEventEffect([]);
            const enveffect = new TaskEnvironmentEffect([]);
            this.parseOOPMembersCommon(sinfo, false, thisType, currentDecl, [iname], [...terms], new Set<string>(terms.map((tt) => tt.name)), nestedEntities, cinvariants, cvalidates, cstaticMembers, cstaticFunctions, memberFields, cmemberMethods, [], statuseffect, eventeffect, enveffect, []);

            if (cusing.length !== 0 && memberFields.length !== 0) {
                this.raiseError(this.getCurrentLine(), "Cannot define fields in multiple places in ADT++ decl");
            }
            cusing = [...cusing, ...memberFields];

            this.ensureAndConsumeToken(SYM_rbrace, "datatype");

            if (currentDecl.checkDeclNameClash(iname)) {
                this.raiseError(line, "Collision between concept and other names");
            }

            this.clearRecover();
        }
        else {
            this.ensureAndConsumeToken(SYM_semicolon, "datatype");
        }

        //
        //TODO: may want to do a bit more linking of adt concept and entities for things like exhaustive checking
        //

        const cdecl = new ConceptTypeDecl(sinfo, this.m_penv.getCurrentFile(), ["__adt_concept_type"], currentDecl.ns, iname, terms, provides, cinvariants, cvalidates, cstaticMembers, cstaticFunctions, cusing, cmemberMethods, new Map<string, EntityTypeDecl>());
        currentDecl.concepts.set(iname, cdecl);
        this.m_penv.assembly.addConceptDecl((currentDecl.ns !== "Core" ? (currentDecl.ns + "::") : "") + iname, cdecl);
    }

    private parseEndOfStream() {
        if(!this.testToken(TokenStrings.EndOfStream)) {
            this.raiseError(this.getCurrentLine(), "Expected end-of-file");
        }

        this.consumeToken();
    }

    ////
    //Public methods

    parseCompilationUnitPass1(file: string, contents: string, macrodefs: string[]): boolean {
        this.setNamespaceAndFile("[No Namespace]", file);

        const lexer = new Lexer(contents, macrodefs, undefined);
        this.initialize(lexer.lex());

        //namespace NS; ...
        this.ensureAndConsumeToken(KW_namespace, "namespace declaration");
        this.ensureToken(TokenStrings.ScopeName, "namespace declaration");
        const ns = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(SYM_semicolon, "namespace declaration");

        this.setNamespaceAndFile(ns, file);
        const nsdecl = this.m_penv.assembly.ensureNamespace(ns);

        let parseok = true;
        while (this.m_cpos < this.m_epos) {
            try {
                this.m_cpos = this.scanTokenOptions(...NS_KW);
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

                const op = this.peekToken();
                if(this.testToken(KW_import)) {
                    this.consumeToken();
                    //then don't care about the rest of the usings
                }
                else if (this.testToken(KW_function)  || this.testToken(KW_const) || this.testToken(KW_format)) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.Identifier, op);
                    const fname = this.consumeTokenAndGetValue();
                    if (nsdecl.declaredNames.has(fname)) {
                        this.raiseError(this.getCurrentLine(), `Duplicate definition of name "${fname}"`);
                    }

                    nsdecl.declaredNames.add(fname);
                }
                else if(this.testToken(KW_logmsg) || this.testToken(KW_eventmsg) || this.testToken(KW_statusmsg)) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.Type, op);
                    const tname = this.consumeTokenAndGetValue();
                    if (nsdecl.declaredNames.has(tname)) {
                        this.raiseError(this.getCurrentLine(), `Duplicate definition of name "${tname}"`);
                    }

                    nsdecl.declaredNames.add(tname);
                }
                else if (this.testToken(KW_operator)) {
                    this.consumeToken();

                    let nns = ns;
                    if (this.testToken(TokenStrings.ScopeName)) {
                        nns = this.consumeTokenAndGetValue();
                        this.ensureAndConsumeToken(SYM_coloncolon, op);
                    }

                    const fname = this.consumeTokenAndGetValue();

                    if (nns === ns) {
                        nsdecl.declaredNames.add(fname);
                    }
                }
                else if (this.testToken(KW_typedef)) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.ScopeName, op);
                    const tname = this.consumeTokenAndGetValue();

                    if (!lexer.isDeclTypeName(tname)) {
                        this.raiseError(this.getCurrentLine(), "Not a valid type name to define");
                    }
                    if (nsdecl.declaredNames.has(tname)) {
                        this.raiseError(this.getCurrentLine(), `Duplicate definition of name "${tname}"`);
                    }
                    nsdecl.declaredNames.add(tname);
                }
                else if (this.testToken(KW_typedecl)) {            
                    this.consumeToken();

                    this.ensureToken(TokenStrings.ScopeName, op);
                    const tname = this.consumeTokenAndGetValue();

                    if (!lexer.isDeclTypeName(tname)) {
                        this.raiseError(this.getCurrentLine(), "Not a valid type name to define");
                    }
                    if (nsdecl.declaredNames.has(tname)) {
                        this.raiseError(this.getCurrentLine(), `Duplicate definition of name "${tname}"`);
                    }
                    nsdecl.declaredNames.add(tname);

                    this.ensureAndConsumeToken(SYM_eq, op);
                    if (this.testToken(TokenStrings.Regex)) {
                        this.consumeToken();
                        this.ensureAndConsumeToken(SYM_semicolon, op);
                    }
                    else {
                        if (this.testAndConsumeTokenIf(SYM_amp)) {
                            this.ensureToken(SYM_lbrace, op); //we should be at the opening left paren 
                            this.m_cpos = this.scanCodeParens(); //scan to the closing paren
                        }
                    }
                }
                else if (this.testToken(KW_datatype)) {            
                    this.consumeToken();

                    this.ensureToken(TokenStrings.ScopeName, op);
                    const tname = this.consumeTokenAndGetValue();

                    if (!lexer.isDeclTypeName(tname)) {
                        this.raiseError(this.getCurrentLine(), "Not a valid type name to define");
                    }
                    if (nsdecl.declaredNames.has(tname)) {
                        this.raiseError(this.getCurrentLine(), `Duplicate definition of name "${tname}"`);
                    }
                    nsdecl.declaredNames.add(tname);

                    //[attr] typedecl NAME<...> [provides ... ] [using {...}] of
                    // Foo {...}
                    // | ...
                    // [& {...}] | ;

                    this.parseProvides(this.getCurrentSrcInfo(), false /*Doesn't matter since we arejust scanning*/, [KW_of, KW_using]);

                    if (this.testAndConsumeTokenIf(KW_using)) {
                        this.ensureToken(SYM_lbrace, op); //we should be at the opening left paren 
                        this.m_cpos = this.scanCodeParens(); //scan to the closing paren
                    }

                    this.ensureAndConsumeToken(KW_of, op);

                    while (!this.testToken(SYM_semicolon) && !this.testToken(SYM_amp)) {
                        if (this.testToken(SYM_bar)) {
                            this.consumeToken();
                        }

                        this.ensureToken(TokenStrings.ScopeName, op);
                        const ename = this.consumeTokenAndGetValue();

                        if (!lexer.isDeclTypeName(ename)) {
                            this.raiseError(this.getCurrentLine(), `Not a valid type name "${ename}" to define`);
                        }
                        if (nsdecl.declaredNames.has(ename)) {
                            this.raiseError(this.getCurrentLine(), `Duplicate definition of name "${ename}"`);
                        }
                        nsdecl.declaredNames.add(ename);

                        if (this.testToken(SYM_lbrace)) {
                            this.m_cpos = this.scanCodeParens(); //scan to the closing paren
                        }
                    }

                    if (this.testAndConsumeTokenIf(SYM_amp)) {
                        this.ensureToken(SYM_lbrace, op); //we should be at the opening left paren 
                        this.m_cpos = this.scanCodeParens(); //scan to the closing paren
                    }
                    else {
                        this.ensureAndConsumeToken(SYM_semicolon, op);
                    }
                }
                else if (this.testToken(KW_enum)) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.ScopeName, op);
                    const tname = this.consumeTokenAndGetValue();

                    if (!lexer.isDeclTypeName(tname)) {
                        this.raiseError(this.getCurrentLine(), `Not a valid type name "${tname}" to define`);
                    }
                    if (nsdecl.declaredNames.has(tname)) {
                        this.raiseError(this.getCurrentLine(), `Duplicate definition of name "${tname}"`);
                    }
                    nsdecl.declaredNames.add(tname);

                    this.ensureToken(SYM_lbrace, op); //we should be at the opening left paren 
                    this.m_cpos = this.scanCodeParens(); //scan to the closing paren

                    if (this.testToken(SYM_amp)) {
                        this.ensureToken(SYM_rbrace, op); //we should be at the opening left paren 
                        this.m_cpos = this.scanCodeParens(); //scan to the closing paren
                    }
                }
                else if (this.testToken(KW_concept) || this.testToken(KW_entity)) {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.ScopeName, op);
                    const tname = this.consumeTokenAndGetValue();

                    if (!lexer.isDeclTypeName(tname)) {
                        this.raiseError(this.getCurrentLine(), `Not a valid type name "${tname}" to define`);
                    }
                    if (nsdecl.declaredNames.has(tname)) {
                        this.raiseError(this.getCurrentLine(), `Duplicate definition of name "${tname}"`);
                    }
                    nsdecl.declaredNames.add(tname);

                    this.parseTermDeclarations();
                    this.parseProvides(this.getCurrentSrcInfo(), ns === "Core", [SYM_lbrace]);
            
                    this.ensureToken(SYM_lbrace, op); //we should be at the opening left paren 
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

    private static _s_nsre = /^\s*namespace[ ]+[_a-zA-Z][_a-zA-Z0-9]*;/;
    parseCompilationUnitPass2(file: string, contents: string, macrodefs: string[], namespacestrings: Set<string>): boolean {
        this.setNamespaceAndFile("[No Namespace]", file);
        const lexer = new Lexer(contents, macrodefs, namespacestrings);
        this.initialize(lexer.lex());

        //namespace NS; ...
        this.ensureAndConsumeToken("namespace", "namespace declaration");
        this.ensureToken(TokenStrings.Namespace, "namespace declaration");
        const ns = this.consumeTokenAndGetValue();
        this.ensureAndConsumeToken(SYM_semicolon, "namespace declaration");

        this.setNamespaceAndFile(ns, file);
        const nsdecl = this.m_penv.assembly.ensureNamespace(ns);

        let importok = true;
        let parseok = true;
        while (this.m_cpos < this.m_epos) {
            const rpos = this.scanTokenOptions(...NS_KW, TokenStrings.EndOfStream);

            try {
                if (rpos === this.m_epos) {
                    break;
                }

                const tk = this.m_tokens[rpos].kind;
                importok = importok && tk === KW_import;
                if (tk === KW_import) {
                    if (!importok) {
                        this.raiseError(this.getCurrentLine(), "Using statements must come before other declarations");
                    }

                    this.parseNamespaceUsing(nsdecl);
                }
                else if (tk === KW_function) {
                    this.parseNamespaceFunction(nsdecl);
                }
                else if (tk === KW_operator) {
                    this.parseNamespaceOperator(nsdecl);
                }
                else if (tk === KW_const) {
                    this.parseNamespaceConst(nsdecl);
                }
                else if(this.testToken(KW_logmsg)) {
                    this.parseNamespaceLogMsg(nsdecl);
                }
                else if(this.testToken(KW_eventmsg)) {
                    this.parseNamespaceEventMsg(nsdecl);
                }
                else if(this.testToken(KW_statusmsg)) {
                    this.parseNamespaceStatusMsg(nsdecl);
                }
                else if(this.testToken(KW_format)) {
                    this.parseNamespaceFormatString(nsdecl);
                }
                else if (tk === KW_typedef) {
                    this.parseNamespaceTypedef(nsdecl);
                }
                else if (tk === KW_concept) {
                    this.parseConcept(nsdecl);
                }
                else if (tk === KW_entity) {
                    this.parseObject(nsdecl, undefined, [], []);
                }
                else if (tk === KW_enum) {
                    this.parseEnum(nsdecl);
                }
                else if (tk === KW_typedecl) {
                    this.parseTypeDecl(nsdecl);
                }
                else if (tk === KW_datatype) {
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

export { 
    ParseError, Parser
};
