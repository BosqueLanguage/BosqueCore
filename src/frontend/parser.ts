
import assert from "node:assert";

import { LocalVariableDefinitionInfo, ParserEnvironment, StandardScopeInfo } from "./parser_env.js";
import { AutoTypeSignature, EListTypeSignature, ErrorTypeSignature, FullyQualifiedNamespace, FunctionParameter, LambdaTypeSignature, NominalTypeSignature, NoneableTypeSignature, RecordTypeSignature, TemplateTypeSignature, TupleTypeSignature, TypeSignature, UnionTypeSignature } from "./type.js";
import { AbortStatement, AbstractBodyImplementation, AccessNamespaceConstantExpression, AccessVariableExpression, ArgumentList, ArgumentValue, AssertStatement, BinAddExpression, BinDivExpression, BinKeyEqExpression, BinKeyNeqExpression, BinLogicAndExpression, BinLogicIFFExpression, BinLogicImpliesExpression, BinLogicOrExpression, BinMultExpression, BinSubExpression, BinderInfo, BlockStatement, BodyImplementation, BuiltinBodyImplementation, CallNamespaceFunctionExpression, ConstantExpressionValue, ConstructorEListExpression, ConstructorLambdaExpression, DebugStatement, EmptyStatement, ErrorExpression, ErrorStatement, Expression, ExpressionBodyImplementation, ExpressionTag, ITest, ITestErr, ITestLiteral, ITestNone, ITestNothing, ITestOk, ITestSome, ITestSomething, ITestType, IfElifElseStatement, IfElseStatement, IfExpression, IfStatement, IfTest, LetExpression, LiteralExpressionValue, LiteralPathExpression, LiteralRegexExpression, LiteralSimpleExpression, LiteralSingletonExpression, LiteralTemplateStringExpression, LiteralTypeDeclFloatPointValueExpression, LiteralTypeDeclIntegralValueExpression, LiteralTypeDeclValueExpression, LiteralTypedStringExpression, MapEntryConstructorExpression, MatchStatement, NamedArgumentValue, NumericEqExpression, NumericGreaterEqExpression, NumericGreaterExpression, NumericLessEqExpression, NumericLessExpression, NumericNeqExpression, ParseAsTypeExpression, PositionalArgumentValue, PostfixAsConvert, PostfixIsTest, PostfixOp, PostfixOperation, PostfixTypeDeclValue, PredicateUFBodyImplementation, PrefixNegateOrPlusOpExpression, PrefixNotOpExpression, RefArgumentValue, ReturnStatement, SpreadArgumentValue, StandardBodyImplementation, Statement, SwitchStatement, SynthesisBodyImplementation, ValidateStatement, VariableAssignmentStatement, VariableDeclarationStatement, VariableInitializationStatement, VariableMultiAssignmentStatement, VariableMultiDeclarationStatement, VariableMultiInitializationStatement, VariableRetypeStatement } from "./body.js";
import { APIDecl, APIResultTypeDecl, ExRegexValidatorTypeDecl, ExStringOfTypeDecl, AbstractNominalTypeDecl, AdditionalTypeDeclTag, Assembly, ConceptTypeDecl, ConstMemberDecl, DatatypeMemberEntityTypeDecl, DatatypeTypeDecl, DeclarationAttibute, EntityTypeDecl, EnumTypeDecl, EnvironmentVariableInformation, EventListTypeDecl, ExpandoableTypeDecl, FunctionInvokeDecl, InternalConceptTypeDecl, InvariantDecl, InvokeExample, InvokeExampleDeclFile, InvokeExampleDeclInline, InvokeTemplateTermDecl, InvokeTemplateTypeRestriction, InvokeTemplateTypeRestrictionClause, InvokeTemplateTypeRestrictionClauseSubtype, InvokeTemplateTypeRestrictionClauseUnify, LambdaDecl, ListTypeDecl, MapEntryTypeDecl, MapTypeDecl, MemberFieldDecl, MethodDecl, NamespaceConstDecl, NamespaceDeclaration, NamespaceFunctionDecl, NamespaceTypedef, NamespaceUsing, PathValidatorTypeDecl, PostConditionDecl, PreConditionDecl, PrimitiveConceptTypeDecl, PrimitiveEntityTypeDecl, QueueTypeDecl, RegexValidatorTypeDecl, ResourceAccessModes, ResourceInformation, ResultTypeDecl, SetTypeDecl, StackTypeDecl, StatusInfoFilter, StringOfTypeDecl, TaskActionDecl, TaskDecl, TaskMethodDecl, TypeFunctionDecl, TypeTemplateTermDecl, TypedeclTypeDecl, ValidateDecl, WELL_KNOWN_EVENTS_VAR_NAME, WELL_KNOWN_RETURN_VAR_NAME, WELL_KNOWN_SRC_VAR_NAME, SomethingTypeDecl, OptionTypeDecl, TemplateTermDeclExtraTag } from "./assembly.js";
import { BuildLevel, CodeFileInfo, CodeFormatter, SourceInfo } from "./build_decls.js";
import { AllAttributes, CoreOnlyAttributes, KW__debug, KW_abort, KW_action, KW_api, KW_as, KW_assert, KW_chktest, KW_concept, KW_const, KW_datatype, KW_debug, KW_declare, KW_elif, KW_else, KW_ensures, KW_entity, KW_enum, KW_env, KW_err, KW_errtest, KW_event, KW_example, KW_false, KW_field, KW_fn, KW_function, KW_if, KW_implements, KW_in, KW_invariant, KW_let, KW_match, KW_method, KW_namespace, KW_none, KW_nothing, KW_of, KW_ok, KW_pred, KW_predicate, KW_provides, KW_recursive, KW_recursive_q, KW_ref, KW_release, KW_requires, KW_resource, KW_return, KW_safety, KW_self, KW_softcheck, KW_some, KW_something, KW_spec, KW_status, KW_switch, KW_task, KW_test, KW_then, KW_this, KW_true, KW_type, KW_typedecl, KW_under, KW_using, KW_validate, KW_validator, KW_var, KW_when, KeywordStrings, LeftScanParens, ParenSymbols, RightScanParens, SYM_HOLE, SYM_amp, SYM_ampamp, SYM_arrow, SYM_at, SYM_atat, SYM_bang, SYM_bangeq, SYM_bangeqeq, SYM_bar, SYM_barbar, SYM_bigarrow, SYM_colon, SYM_coloncolon, SYM_coma, SYM_div, SYM_dotdotdot, SYM_eq, SYM_eqeq, SYM_eqeqeq, SYM_gt, SYM_gteq, SYM_iff, SYM_implies, SYM_langle, SYM_lbrace, SYM_lbracebar, SYM_lbrack, SYM_lparen, SYM_lt, SYM_lteq, SYM_minus, SYM_negate, SYM_plus, SYM_positive, SYM_question, SYM_rangle, SYM_rbrace, SYM_rbracebar, SYM_rbrack, SYM_rparen, SYM_semicolon, SYM_times, SYM_wildcard, SpaceFrontSymbols, SpaceRequiredSymbols, StandardSymbols } from "./parser_kw.js";

import { accepts, initializeLexer, lexFront } from "@bosque/jsbrex";

type ParsePhase = number;
const ParsePhase_RegisterNames: ParsePhase = 1;
const ParsePhase_CompleteParsing: ParsePhase = 2;

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
    ExString: "[LITERAL_EX_STRING]",
    TemplateString: "[LITERAL_TEMPLATE_STRING]",
    TemplateExString: "[LITERAL_TEMPLATE_EX_STRING]",

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

    ResourceUseMod: "[RESOURCE_USE_MOD]",

    EndOfStream: "[EOS]"
};


const NAMESPACE_DECL_FIRSTS = [
    TokenStrings.Attribute,
    TokenStrings.DocComment,
    KW_recursive, KW_recursive_q, 
    KW_function, KW_predicate, 
    KW_namespace, KW_api,
    KW_const,
    KW_enum, KW_type, KW_entity, KW_concept, KW_typedecl, KW_datatype, KW_task,
    KW_event, KW_status,
    KW_validator,
    KW_errtest, KW_chktest
].sort((a, b) => { return (a.length !== b.length) ? (b.length - a.length) : ((a !== b) ? (a < b ? -1 : 1) : 0); });

const TYPE_DECL_FIRSTS = [
    TokenStrings.Attribute,
    TokenStrings.DocComment,
    KW_recursive, KW_recursive_q, 
    KW_ref,
    KW_field, KW_const, KW_invariant, KW_validate, 
    KW_function, KW_method, KW_action,
    KW_env, KW_event, KW_status, KW_resource,
    KW_entity
].sort((a, b) => { return (a.length !== b.length) ? (b.length - a.length) : ((a !== b) ? (a < b ? -1 : 1) : 0); });

const PRIMITIVE_ENTITY_TYPE_NAMES = [
    "None", "Nothing", "Bool", 
    "Nat", "Int", "BigInt", "BigNat", "Rational", "Float", "Decimal", "DecimalDegree", "LatLongCoordinate", "Complex",
    "ByteBuffer", "UUIDv4", "UUIDv7", "SHAContentHash", 
    "DateTime", "UTCDateTime", "PlainDate", "PlainTime", "TickTime", "LogicalTime", "ISOTimestamp",
    "DeltaDateTime", "DeltaPlainDate", "DeltaPlainTime", "DeltaSeconds", "DeltaTickTime", "DeltaLogicalTime", "DeltaISOTimestamp",
    "String", "ExString", "UnicodeRegex", "ExRegex", "PathRegex", "TemplateString", "TemplateExString"
];

const PRIMITIVE_CONCEPT_TYPE_NAMES = [
    "Any", "Some", "KeyType", 
    "Comparable", "LinearArithmetic", "Numeric",
    "Tuple", "Record", "Object",
    "RegexValidator", "ExRegexValidator", "PathValidator",
    "IOption", "ISomething",
    "IResult", "IOk", "IError",
    "IAPIResult", "IAPIRejected", "IAPIFailed", "IAPIError", "IAPISuccess"
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
    readonly srcfile: string;
    readonly sinfo: SourceInfo;
    readonly message: string;

    constructor(srcfile: string, sinfo: SourceInfo, message: string) {
        this.srcfile = srcfile;
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

class Lexer {
    readonly iscore: boolean;
    readonly srcfile: string;

    readonly macrodefs: string[];
    readonly scanmode: LexerStateScanMode[];

    readonly input: string;
    readonly epos: number;
    cpos: number;

    cline: number;
    linestart: number;
    
    tokens: Token[];
    errors: ParserError[];

    constructor(iscore: boolean, srcfile: string, input: string, macrodefs: string[]) {
        this.iscore = iscore;
        this.srcfile = srcfile;
        this.macrodefs = macrodefs;
        this.scanmode = [LexerStateScanMode.Enabled];

        this.input = input;
        initializeLexer(this.input);

        this.epos = this.input.length;
        this.cpos = 0;

        this.cline = 1;
        this.linestart = 0;

        this.tokens = [];
        this.errors = [];
    }

    ////
    //Helpers
    pushError(sinfo: SourceInfo, message: string) {
        const cmode = this.scanmode[this.scanmode.length - 1];
        if(cmode === LexerStateScanMode.Enabled || cmode === LexerStateScanMode.EnabledIf || cmode === LexerStateScanMode.EnabledElse) {
            this.errors.push(new ParserError(this.srcfile, sinfo, message));
        }
    }

    pushToken(token: Token) {
        const cmode = this.scanmode[this.scanmode.length - 1];
        if(cmode === LexerStateScanMode.Enabled || cmode === LexerStateScanMode.EnabledIf || cmode === LexerStateScanMode.EnabledElse) {
            this.tokens.push(token);
        }
    }

    private recordLexToken(epos: number, kind: string) {
        this.pushToken(new Token(this.cline, this.cpos - this.linestart, this.cpos, epos - this.cpos, kind, kind)); //set data to kind string
        this.cpos = epos;
    }

    private recordLexTokenWData(epos: number, kind: string, data: string) {
        this.pushToken(new Token(this.cline, this.cpos - this.linestart, this.cpos, epos - this.cpos, kind, data));
        this.cpos = epos;
    }

    private updatePositionInfo(spos: number, epos: number) {
        for (let i = spos; i < epos; ++i) {
            if (this.input[i] === "\n") {
                this.cline++;
                this.linestart = i + 1;
            }
        }
    }
    
    private static readonly _s_resourceUseModRe = '/"["[?!+*-]+"]"/';

    private static readonly _s_spaceSensitiveOps = SpaceRequiredSymbols.map((op) => `"${op.trim()}"`).join("|")
    private static readonly _s_spaceSensitiveOpsRe = `/[ %n;%v;%f;%r;%t;]+(${Lexer._s_spaceSensitiveOps})[ %n;%v;%f;%r;%t;]+/`;

    private static readonly _s_spaceSensitiveFrontOps = SpaceFrontSymbols.map((op) => `"${op.trim()}"`).join("|")
    private static readonly _s_spaceSensitiveFrontOpsRe = `/<[ %n;%v;%f;%r;%t;]+(${Lexer._s_spaceSensitiveFrontOps})>$[^0-9+-]/`;

    private static readonly _s_whitespaceRe = '/[ %n;%v;%f;%r;%t;]+/';
    private tryLexWS(): boolean {
        const arop = lexFront(Lexer._s_spaceSensitiveOpsRe, this.cpos);
        if (arop !== null) {
            return false;
        }

        const frop = lexFront(Lexer._s_spaceSensitiveFrontOpsRe, this.cpos);
        if (frop !== null) {
            return false;
        }

        const m = lexFront(Lexer._s_whitespaceRe, this.cpos);
        if (m === null) {
            return false;
        }

        this.updatePositionInfo(this.cpos, this.cpos + m.length);
        this.cpos += m.length;

        return true;
    }

    private tryLexLineComment(): boolean {
        const m = this.input.startsWith("%%", this.cpos);
        if (!m) {
            return false;
        }

        let epos = this.input.slice(0, this.epos).indexOf("\n", this.cpos);

        if (epos === -1) {
            this.updatePositionInfo(this.cpos, epos);
            this.cpos = this.epos;
        }
        else {
            epos++;

            this.updatePositionInfo(this.cpos, epos);
            this.cpos = epos;
        }

        return true;
    }

    private tryLexDocComment(): boolean {
        const m = this.input.startsWith("%** ", this.cpos);
        if (!m) {
            return false;
        }

        let epos = this.input.slice(0, this.epos).indexOf(" **%", this.cpos + 4);
        if (epos !== -1) {
            epos += 4;

            this.updatePositionInfo(this.cpos, epos);
            this.recordLexTokenWData(epos, TokenStrings.DocComment, this.input.substring(this.cpos, epos));
            return true;
        }

        return false;
    }

    private tryLexSpanComment(): boolean {
        const m = this.input.startsWith("%*", this.cpos);
        if (!m) {
            return false;
        }

        let epos = this.input.slice(0, this.epos).indexOf("*%", this.cpos + 2);
        if (epos === -1) {
            this.pushError(new SourceInfo(this.cline, this.linestart, this.cpos, this.epos - this.cpos), "Unterminated span comment");
            
            this.updatePositionInfo(this.cpos, epos);
            this.cpos = this.epos;
        }
        else {
            epos += 2;

            this.updatePositionInfo(this.cpos, epos);
            this.cpos = epos;
        }

        return true;
    }

    private static readonly _s_templateNameRe = '/[A-Z]/';
    private static isTemplateName(str: string): boolean {
        return accepts(Lexer._s_templateNameRe, str);
    }

    private static readonly _s_literalTDOnlyTagRE = `"_"`;

    private static readonly _s_nonzeroIntValNoSignRE = `[1-9][0-9]*`;
    private static readonly _s_nonzeroIntValRE = `[+-]?${Lexer._s_nonzeroIntValNoSignRE}`;
    private static readonly _s_intValueNoSignRE = `("0"|${Lexer._s_nonzeroIntValNoSignRE})`;
    private static readonly _s_intValueRE = `("0"|"+0"|${Lexer._s_nonzeroIntValRE})`;

    private static readonly _s_floatValueNoSignRE = `[0-9]+"."[0-9]+([eE][-+]?[0-9]+)?`;
    private static readonly _s_floatValueRE = `[+-]?${Lexer._s_floatValueNoSignRE}([eE][-+]?[0-9]+)?`;

    private static readonly _s_floatSimpleValueNoSignRE = '[0-9]+"."[0-9]+';
    private static readonly _s_floatSimpleValueRE = `[+-]?${Lexer._s_floatSimpleValueNoSignRE}`;

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
    private static readonly _s_rationalRe = `/(${Lexer._s_intValueRE})("%slash;"(${Lexer._s_nonzeroIntValNoSignRE}))?"R"(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static readonly _s_complexRe = `/(${Lexer._s_floatValueRE})[+-](${Lexer._s_floatValueNoSignRE})"j"(${Lexer._s_literalTDOnlyTagRE})?/`;

    private static readonly _s_decimalDegreeRe = `/(${Lexer._s_floatSimpleValueRE})"dd"(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static readonly _s_latlongRe = `/(${Lexer._s_floatSimpleValueRE})"lat"[+-]${Lexer._s_floatSimpleValueNoSignRE}"long"(${Lexer._s_literalTDOnlyTagRE})?/`;
    
    private static readonly _s_ticktimeRe = `/(${Lexer._s_intValueRE})"t"(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static readonly _s_logicaltimeRe = `/(${Lexer._s_intValueRE})"l"(${Lexer._s_literalTDOnlyTagRE})?/`;

    private static readonly _s_deltasecondsRE = `/[+-](${Lexer._s_floatValueNoSignRE})"ds"(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static readonly _s_deltaticktimeRE = `/[+-](${Lexer._s_intValueNoSignRE})"dt"(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static readonly _s_deltalogicaltimeRE = `/[+-](${Lexer._s_intValueNoSignRE})"dl"(${Lexer._s_literalTDOnlyTagRE})?/`;

    private static readonly _s_zerodenomRationalTaggedNumberinoRe = `/(${Lexer._s_intValueRE})"%slash;""0"${Lexer._s_literalTDOnlyTagRE}/`;
    private static readonly _s_zerodenomRationalRe = `/(${Lexer._s_intValueRE})("%slash;""0")?"R"(${Lexer._s_literalTDOnlyTagRE})?/`;

    private static readonly _s_redundantSignRE = /[+-]{2,}/y;
    private checkRedundantSigns() {
        if(this.cpos !== this.epos && (this.input[this.cpos] === "+" || this.input[this.cpos] === "-")) {
            Lexer._s_redundantSignRE.lastIndex = this.cpos;
            const mm = Lexer._s_redundantSignRE.exec(this.input);
            if(mm !== null) {
                this.errors.push(new ParserError(this.srcfile, new SourceInfo(this.cline, this.linestart, this.cpos, this.epos - this.cpos), "Redundant sign"));
                this.cpos = Math.min(this.epos, this.cpos + mm.length - 1);
            }
        }
    }

    private tryLexFloatCompositeLikeToken(): boolean {
        const mcomplex = lexFront(Lexer._s_complexRe, this.cpos);
        if(mcomplex !== null) {
            this.recordLexTokenWData(this.cpos + mcomplex.length, TokenStrings.Complex, mcomplex);
            return true;
        }

        const mlatlong = lexFront(Lexer._s_latlongRe, this.cpos);
        if(mlatlong !== null) {
            this.recordLexTokenWData(this.cpos + mlatlong.length, TokenStrings.LatLong, mlatlong);
            return true;
        }

        return false;
    }

    private tryLexFloatLikeToken(): boolean {
        const mdecimaldegree = lexFront(Lexer._s_decimalDegreeRe, this.cpos);
        if(mdecimaldegree !== null) {
            this.recordLexTokenWData(this.cpos + mdecimaldegree.length, TokenStrings.DecimalDegree, mdecimaldegree);
            return true;
        }

        const mdeltaseconds = lexFront(Lexer._s_deltasecondsRE, this.cpos);
        if(mdeltaseconds !== null) {
            this.recordLexTokenWData(this.cpos + mdeltaseconds.length, TokenStrings.DeltaSeconds, mdeltaseconds);
            return true;
        }

        const mdecimal = lexFront(Lexer._s_decimalRe, this.cpos);
        if(mdecimal !== null) {
            this.recordLexTokenWData(this.cpos + mdecimal.length, TokenStrings.Decimal, mdecimal);
            return true;
        }

        const mfloat = lexFront(Lexer._s_floatRe, this.cpos);
        if(mfloat !== null) {
            this.recordLexTokenWData(this.cpos + mfloat.length, TokenStrings.Float, mfloat);
            return true;
        }

        const mnumberino = lexFront(Lexer._s_floatTaggedNumberinoRe, this.cpos);
        if(mnumberino !== null) {
            this.recordLexTokenWData(this.cpos + mnumberino.length, TokenStrings.TaggedNumberinoFloat, mnumberino);
            return true;
        }

        const unumberino = lexFront(Lexer._s_floatNumberinoRe, this.cpos);
        if(unumberino !== null) {
            this.recordLexTokenWData(this.cpos + unumberino.length, TokenStrings.NumberinoFloat, unumberino);
            return true;
        }

        return false;
    }

    private tryLexIntegralCompositeLikeToken(): boolean {
        const mrational = lexFront(Lexer._s_rationalRe, this.cpos);
        if(mrational !== null) {
            this.recordLexTokenWData(this.cpos + mrational.length, TokenStrings.Rational, mrational);
            return true;
        }

        const mnumberino = lexFront(Lexer._s_rationalTaggedNumberinoRe, this.cpos);
        if(mnumberino !== null) {
            this.recordLexTokenWData(this.cpos + mnumberino.length, TokenStrings.TaggedNumberinoRational, mnumberino);
            return true;
        }

        const mzerodenom = lexFront(Lexer._s_zerodenomRationalRe, this.cpos);
        if(mzerodenom !== null) {
            this.pushError(new SourceInfo(this.cline, this.linestart, this.cpos, this.epos - this.cpos), "Zero denominator in rational number");
            this.recordLexTokenWData(this.cpos + mzerodenom.length, TokenStrings.Rational, mzerodenom);
            return true;
        }

        const mzerodenomtagged = lexFront(Lexer._s_zerodenomRationalTaggedNumberinoRe, this.cpos);
        if(mzerodenomtagged !== null) {
            this.pushError(new SourceInfo(this.cline, this.linestart, this.cpos, this.epos - this.cpos), "Zero denominator in rational number");
            this.recordLexTokenWData(this.cpos + mzerodenomtagged.length, TokenStrings.TaggedNumberinoRational, mzerodenomtagged);
            return true;
        }

        return false;
    }

    private tryLexIntegralLikeToken(): boolean {
        const mtick = lexFront(Lexer._s_ticktimeRe, this.cpos);
        if(mtick !== null) {
            this.recordLexTokenWData(this.cpos + mtick.length, TokenStrings.TickTime, mtick);
            return true;
        }

        const mlogical = lexFront(Lexer._s_logicaltimeRe, this.cpos);
        if(mlogical !== null) {
            this.recordLexTokenWData(this.cpos + mlogical.length, TokenStrings.LogicalTime, mlogical);
            return true;
        }

        const m_deltatick = lexFront(Lexer._s_deltaticktimeRE, this.cpos);
        if(m_deltatick !== null) {
            this.recordLexTokenWData(this.cpos + m_deltatick.length, TokenStrings.DeltaTickTime, m_deltatick);
            return true;
        }

        const m_deltalogical = lexFront(Lexer._s_deltalogicaltimeRE, this.cpos);
        if(m_deltalogical !== null) {
            this.recordLexTokenWData(this.cpos + m_deltalogical.length, TokenStrings.DeltaLogicalTime, m_deltalogical);
            return true;
        }
        
        const mint = lexFront(Lexer._s_intRe, this.cpos);
        if(mint !== null) {
            this.recordLexTokenWData(this.cpos + mint.length, TokenStrings.Int, mint);
            return true;
        }

        const mnat = lexFront(Lexer._s_natRe, this.cpos);
        if(mnat !== null) {
            this.recordLexTokenWData(this.cpos + mnat.length, TokenStrings.Nat, mnat);
            return true;
        }

        const mbigint = lexFront(Lexer._s_bigintRe, this.cpos);
        if(mbigint !== null) {
            this.recordLexTokenWData(this.cpos + mbigint.length, TokenStrings.BigInt, mbigint);
            return true;
        }

        const mbignat = lexFront(Lexer._s_bignatRe, this.cpos);
        if(mbignat !== null) {
            this.recordLexTokenWData(this.cpos + mbignat.length, TokenStrings.BigNat, mbignat);
            return true;
        }

        const mtnumberino = lexFront(Lexer._s_intTaggedNumberinoRe, this.cpos);
        if(mtnumberino !== null) {
            this.recordLexTokenWData(this.cpos + mtnumberino.length, TokenStrings.TaggedNumberinoInt, mtnumberino);
            return true;
        }

        const mnumberino = lexFront(Lexer._s_intNumberinoRe, this.cpos);
        if(mnumberino !== null) {
            this.recordLexTokenWData(this.cpos + mnumberino.length, TokenStrings.NumberinoInt, mnumberino);
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
        const m = lexFront(Lexer._s_bytebufferRe, this.cpos);
        if(m !== null) {
            this.recordLexTokenWData(this.cpos + m.length, TokenStrings.ByteBuffer, m);
            return true;
        }

        return false;
    }

    private static _s_uuidRe = `/"uuid"[47]"{"[a-fA-F0-9]{8}"-"[a-fA-F0-9]{4}"-"[a-fA-F0-9]{4}"-"[a-fA-F0-9]{4}"-"[a-fA-F0-9]{12}"}"(${Lexer._s_literalTDOnlyTagRE})?/`;
    private tryLexUUID(): boolean {
        const m = lexFront(Lexer._s_uuidRe, this.cpos);
        if(m !== null) {
            this.recordLexTokenWData(this.cpos + m.length, TokenStrings.UUIDValue, m);
            return true;
        }

        return false;
    }

    private static _s_shaRe = `/"sha3{"[a-fA-F0-9]{64}"}"(${Lexer._s_literalTDOnlyTagRE})?/`;
    private tryLexHashCode(): boolean {
        const m = lexFront(Lexer._s_shaRe, this.cpos);
        if(m !== null) {
            this.recordLexTokenWData(this.cpos + m.length, TokenStrings.ShaHashcode, m);
            return true;
        }

        return false;
    }

    private static readonly _s_literalGeneralTagRE = /(_[_a-zA-Z])|[(]/y;
    private tryLexUnicodeString(): boolean {
        let ncpos = this.cpos;
        let istemplate = false;
        if(this.input.startsWith('$"', this.cpos)) {
            ncpos += 2;
            istemplate = true;
        }
        else if(this.input.startsWith('"', this.cpos)) {
            ncpos += 1;
        }
        else {
            return false;
        }


        let epos = this.input.slice(0, this.epos).indexOf('"', ncpos);
        if(epos === -1) {
            this.pushError(new SourceInfo(this.cline, this.linestart, this.cpos, this.epos - this.cpos), "Unterminated string literal");
            this.recordLexToken(this.epos, TokenStrings.Error);

            return true;
        }
        else {
            epos++;
            let strval = this.input.substring(ncpos, epos);

            Lexer._s_literalGeneralTagRE.lastIndex = epos;
            const mtag = Lexer._s_literalGeneralTagRE.exec(this.input);
            if(mtag !== null) {
                if(istemplate) {
                    this.pushError(new SourceInfo(this.cline, this.linestart, this.cpos, this.epos - this.cpos), "Template strings cannot have type tags");
                }
                else {
                    if(mtag[0].startsWith("(")) {
                        strval += "[OF]"; //put special marker on back of string value for later
                    }
                    else {
                        epos++; //eat the underscore and include it in the string
                        strval += "_";
                    }
                }   
            }

            this.updatePositionInfo(this.cpos, epos);
            this.recordLexTokenWData(epos, istemplate ? TokenStrings.TemplateString : TokenStrings.String, strval);
            return true;
        }
    }

    static _s_validExStringChars = /[ -~]*/;
    private tryLexExString(): boolean {
        let ncpos = this.cpos;
        let istemplate = false;
        if(this.input.startsWith("$'", this.cpos)) {
            ncpos += 2;
            istemplate = true;
        }
        else if(this.input.startsWith("'", this.cpos)) {
            ncpos += 1;
        }
        else {
            return false;
        }

        let epos = this.input.slice(0, this.epos).indexOf("'", ncpos);

        const mstr = this.input.slice(ncpos, this.epos);
        if(Lexer._s_validExStringChars.test(mstr)) {
            this.pushError(new SourceInfo(this.cline, this.linestart, this.cpos, this.epos - this.cpos), "Invalid chacaters in Ex string literal");
            this.recordLexToken(this.epos, TokenStrings.Error);

            return true;
        }

        if(epos === -1) {
            this.pushError(new SourceInfo(this.cline, this.linestart, this.cpos, this.epos - this.cpos), "Unterminated Ex string literal");
            this.recordLexToken(this.epos, TokenStrings.Error);

            return true;
        }
        else {
            epos++;
            let strval = this.input.substring(ncpos, epos);

            Lexer._s_literalGeneralTagRE.lastIndex = epos;
            const mtag = Lexer._s_literalGeneralTagRE.exec(this.input);
            if(mtag !== null) {
                if(istemplate) {
                    this.pushError(new SourceInfo(this.cline, this.linestart, this.cpos, this.epos - this.cpos), "Template strings cannot have type tags");
                }
                else {
                    if(mtag[0].startsWith("(")) {
                        strval += "[OF]"; //put special marker on back of string value for later
                    }
                    else {
                        epos++; //eat the underscore and include it in the string
                        strval += "_";
                    }
                }   
            }

            this.updatePositionInfo(this.cpos, epos);
            this.recordLexTokenWData(epos, istemplate ? TokenStrings.TemplateExString : TokenStrings.ExString, strval);
            return true;
        }
    }

    private tryLexStringLike() {
        const us = this.tryLexUnicodeString();
        if(us) {
            return true;
        }

        const as = this.tryLexExString();
        if(as) {
            return true;
        }

        return false;
    }

    private static _s_regexRe = '/"%slash;"[!-.0-~ %t;%n;]+"%slash;"[ap]?/';
    private tryLexRegex() {
        const rem = lexFront(Lexer._s_regexRe, this.cpos);
        if(rem === null) {
            return false;
        }

        this.recordLexTokenWData(this.cpos + rem.length, TokenStrings.Regex, rem);
        return true;
    }

    
    private static _s_pathRe = /[gf]?\\[ !-Z^-~\[\]]\\/y;
    private static readonly _s_literalPathTagRE = /(_[_a-zA-Z])|[(*]/y;
    private tryLexPath() {
        Lexer._s_pathRe.lastIndex = this.cpos;
        const mpth = Lexer._s_pathRe.exec(this.input);
        if(mpth !== null) {
            let epos = this.cpos + mpth[0].length;
            let pthval = mpth[0];

            Lexer._s_literalPathTagRE.lastIndex = epos;
            const mtag = Lexer._s_literalPathTagRE.exec(this.input);
            if(mtag !== null) {
                if(mtag[0].startsWith("_")) {
                    epos++; //eat the underscore and include it in the string
                    pthval += "_"; 
                }
                else if(mtag[0].startsWith("(")) {
                    pthval += "[OF]"; //put special marker on back of string value for later
                }
                else {
                    //implicit path of URI
                    pthval += "*";

                    if(mtag[0] === "*") {
                        epos++; //eat the *
                    }
                }
            }

            this.updatePositionInfo(this.cpos, epos);
            this.recordLexTokenWData(epos, TokenStrings.PathItem, pthval);
            return true;
        }

        return false;
    }

    private static _s_datevalueRE = '([0-9]{4})"-"([0-9]{2})"-"([0-9]{2})';
    private static _s_timevalueRE = '([0-9]{2})":"([0-9]{2})":"([0-9]{2})';
    private static _s_tzvalueRE = '(("%lbrace;"[a-zA-Z0-9/, _-]+"%rbrace;")|[A-Z]+)';

    private static _s_datatimeRE = `/${Lexer._s_datevalueRE}"T"${Lexer._s_timevalueRE}"@"${Lexer._s_tzvalueRE}(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static _s_utcdatetimeRE = `/${Lexer._s_datevalueRE}"T"${Lexer._s_timevalueRE}"Z"?(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static _s_plaindateRE = `/${Lexer._s_datevalueRE}(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static _s_plaintimeRE = `/${Lexer._s_timevalueRE}(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static _s_timestampRE = `/${Lexer._s_datevalueRE}"T"${Lexer._s_timevalueRE}"."([0-9]{3})"Z"(${Lexer._s_literalTDOnlyTagRE})?/`;

    private tryLexDateTime() {
        const mdt = lexFront(Lexer._s_datatimeRE, this.cpos);
        if(mdt !== null) {
            this.recordLexTokenWData(this.cpos + mdt.length, TokenStrings.DateTime, mdt);
            return true;
        }

        const mutcdt = lexFront(Lexer._s_utcdatetimeRE, this.cpos);
        if(mutcdt !== null) {
            this.recordLexTokenWData(this.cpos + mutcdt.length, TokenStrings.UTCDateTime, mutcdt);
            return true;
        }

        const mts = lexFront(Lexer._s_timestampRE, this.cpos);
        if(mts !== null) {
            this.recordLexTokenWData(this.cpos + mts.length, TokenStrings.Timestamp, mts);
            return true;
        }

        const mpd = lexFront(Lexer._s_plaindateRE, this.cpos);
        if(mpd !== null) {
            this.recordLexTokenWData(this.cpos + mpd.length, TokenStrings.PlainDate, mpd);
            return true;
        }

        const mpt = lexFront(Lexer._s_plaintimeRE, this.cpos);
        if(mpt !== null) {
            this.recordLexTokenWData(this.cpos + mpt.length, TokenStrings.PlainTime, mpt);
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
        const mdt = lexFront(Lexer._s_datatimeDeltaRE, this.cpos);
        if(mdt !== null) {
            this.recordLexTokenWData(this.cpos + mdt.length, TokenStrings.DeltaDateTime, mdt);
            return true;
        }

        const mutcdt = lexFront(Lexer._s_utcdatetimeDeltaRE, this.cpos);
        if(mutcdt !== null) {
            this.recordLexTokenWData(this.cpos + mutcdt.length, TokenStrings.DeltaUTCDateTime, mutcdt);
            return true;
        }

        const mts = lexFront(Lexer._s_timestampDeltaRE, this.cpos);
        if(mts !== null) {
            this.recordLexTokenWData(this.cpos + mts.length, TokenStrings.DeltaTimestamp, mts);
            return true;
        }

        const mpd = lexFront(Lexer._s_plaindateDeltaRE, this.cpos);
        if(mpd !== null) {
            this.recordLexTokenWData(this.cpos + mpd.length, TokenStrings.DeltaPlainDate, mpd);
            return true;
        }

        const mpt = lexFront(Lexer._s_plaintimeDeltaRE, this.cpos);
        if(mpt !== null) {
            this.recordLexTokenWData(this.cpos + mpt.length, TokenStrings.DeltaPlainTime, mpt);
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
        const usemodop = lexFront(Lexer._s_resourceUseModRe, this.cpos);
        const spaceop = lexFront(Lexer._s_spaceSensitiveOpsRe, this.cpos);
        const frontop = lexFront(Lexer._s_spaceSensitiveFrontOpsRe, this.cpos);
        if(usemodop !== null) {
            this.recordLexTokenWData(this.cpos + usemodop.length, TokenStrings.ResourceUseMod, usemodop);
            return true;
        }
        else if(spaceop !== null) {
            const realstr = " " + spaceop.trim() + " ";

            this.recordLexToken(this.cpos + spaceop.length, realstr);
            return true; 
        }
        else if(frontop !== null) {
            const realstr = " " + frontop.trim();

            this.recordLexToken(this.cpos + frontop.length, realstr);
            return true; 
        }
        else {
            const mm = StandardSymbols.find((value) => this.input.startsWith(value, this.cpos)) || ParenSymbols.find((value) => this.input.startsWith(value, this.cpos));
            if(mm !== undefined) {
                this.recordLexToken(this.cpos + mm.length, mm);
                return true;
            }

        
            return false;
        }
    }

    private tryLexAttribute() {
        const mm = AllAttributes.find((value) => this.input.startsWith(value, this.cpos));
        if(mm !== undefined) {
            let epos = this.cpos + mm.length;
            if(this.input.startsWith("[", epos)) {
                epos = this.input.slice(epos, this.epos).indexOf("]", epos);
                if(epos === -1) {
                    this.pushError(new SourceInfo(this.cline, this.linestart, this.cpos, this.epos - this.cpos), "Unterminated attribute");
                    this.recordLexToken(this.epos, TokenStrings.Error);
                    return true;
                }
                epos++;
            }

            this.recordLexTokenWData(epos, TokenStrings.Attribute, this.input.substring(this.cpos, epos));
            return true;
        }

        if(this.iscore) {
            const cmm = CoreOnlyAttributes.find((value) => this.input.startsWith(value, this.cpos));
        
            if(cmm !== undefined) {
                this.recordLexTokenWData(this.cpos + cmm.length, TokenStrings.Attribute, cmm);
                return true;
            }
        }

        return false;
    }

    private processIdentifierOptions(idm: string): boolean {
        if(Lexer.isTemplateName(idm)) {
            this.recordLexTokenWData(this.cpos + idm.length, TokenStrings.Template, idm);
            return true;
        }
        else {        
            this.recordLexTokenWData(this.cpos + idm.length, TokenStrings.IdentifierName, idm);
            return true;
        }
    }

    private static readonly _s_taggedBooleanRE = `/<("true"|"false")"_">$[_a-zA-Z(]/`;
    private static readonly _s_identiferName = '/"$"?[_a-zA-Z][_a-zA-Z0-9]*/';
    private tryLexName(): boolean {
        const mtb = lexFront(Lexer._s_taggedBooleanRE, this.cpos);
        if (mtb !== null) {
            this.recordLexTokenWData(this.cpos + mtb.length, TokenStrings.TaggedBoolean, mtb);
            return true;
        }

        const identifiermatch = lexFront(Lexer._s_identiferName, this.cpos);
        const kwmatch = KeywordStrings.find((value) => this.input.startsWith(value, this.cpos));

        if(identifiermatch === null && kwmatch === undefined) {
            return false;
        }

        if (identifiermatch !== null && kwmatch === undefined) {
            return this.processIdentifierOptions(identifiermatch);
        }
        else if(identifiermatch === null && kwmatch !== undefined) {
            this.recordLexToken(this.cpos + kwmatch.length, kwmatch);
            return true;
        }
        else {
            const nnid = identifiermatch as string;
            const nnkw = kwmatch as string;

            if (nnid.length > nnkw.length) {
                return this.processIdentifierOptions(nnid);
            }
            else {
                this.recordLexToken(this.cpos + nnkw.length, nnkw);
                return true;
            }
        }
    }

    private static readonly _s_macroRe = '/("#if"" "+([A-Z][_A-Z0-9]*)|"#else"|"#endif")/';
    tryLexMacroOp(): [string, string | undefined] | undefined {
        const m = lexFront(Lexer._s_macroRe, this.cpos);
        if (m === null) {
            return undefined;
        }

        this.cpos += m.length;

        if(m.slice(0, "#if".length) === "#if") {
            return ["#if", m.slice("#if".length).trim()];
        }
        else {
            return [m, undefined]
        }
    }

    lex(): Token[] {
        while (this.cpos < this.epos) {
            const macro = this.tryLexMacroOp();
            if(macro !== undefined) {
                if(macro[0] === "#if") {
                    const ifenabled = this.macrodefs.includes(macro[1] as string);
                    const cmode = this.scanmode[this.scanmode.length - 1];
                    const cenabled = cmode === LexerStateScanMode.Enabled || cmode === LexerStateScanMode.EnabledIf || cmode === LexerStateScanMode.EnabledElse;

                    let nscanmode = LexerStateScanMode.Disabled;
                    if(cenabled) {
                        nscanmode = ifenabled ? LexerStateScanMode.EnabledIf : LexerStateScanMode.DisabledIf;
                    }

                    this.scanmode.push(nscanmode);
                }
                else if(macro[0] === "#else") {
                    const ifmode = this.scanmode[this.scanmode.length - 1];
                    this.scanmode.pop();

                    if(ifmode === LexerStateScanMode.Disabled) {
                        this.scanmode.push(LexerStateScanMode.Disabled);
                    }
                    else {
                        let nscanmode = ifmode === LexerStateScanMode.EnabledIf ? LexerStateScanMode.DisabledElse : LexerStateScanMode.EnabledElse;
                        this.scanmode.push(nscanmode);
                    }
                }
                else {
                    this.scanmode.pop();
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
                    this.errors.push(new ParserError(this.srcfile, new SourceInfo(this.cline, this.linestart, this.cpos, this.epos - this.cpos), "Unrecognized token"));
                    this.recordLexToken(this.cpos + 1, TokenStrings.Error);
                }
            }
        }

        if(this.cpos === this.input.length) {
            this.recordLexToken(this.input.length, TokenStrings.EndOfStream);
        }
        
        return this.tokens;
    }
}

class ParserState {
    readonly modetag: string;

    readonly epos: number;
    cpos: number;

    tokens: Token[];
    errors: ParserError[] = [];

    constructor(modetag: string, cpos: number, epos: number, tokens: Token[], errors: ParserError[]) {
        this.modetag = modetag;
        this.epos = epos;

        this.cpos = cpos;

        this.tokens = tokens;
        this.errors = errors;
    }

    static createFileToplevelState(tokens: Token[]): ParserState {
        return new ParserState("toplevel", 0, tokens.length, tokens, []);
    }

    cloneForNested(modetag: string, epos: number): ParserState {
        assert(this.cpos <= epos);
        return new ParserState(modetag, this.cpos, epos, this.tokens, []);
    }

    moveStateIntoParent(child: ParserState) {
        this.cpos = child.cpos;
        this.errors.push(...child.errors);
    }

    moveToRecoverPosition() {
        this.cpos = this.epos;
    }

    skipToPosition(pos: number | undefined) {
        assert(pos === undefined || pos <= this.epos);
        this.cpos = (pos !== undefined ? pos : this.epos);
    }
}

class Parser {
    private readonly currentPhase: ParsePhase;
    private readonly tokens: Token[];

    private readonly stateStack: ParserState[];
    private readonly env: ParserEnvironment;

    private wellknownTypes: Map<string, NominalTypeSignature> = new Map<string, NominalTypeSignature>();

    constructor(currentFile: string, toplevelns: string, tokens: Token[], assembly: Assembly, currentPhase: ParsePhase) {
        this.currentPhase = currentPhase;
        this.tokens = tokens;

        this.stateStack = [ParserState.createFileToplevelState(tokens)]

        const nns = assembly.ensureToplevelNamespace(toplevelns);
        this.env = new ParserEnvironment(assembly, currentFile, nns);
    }

    ////
    //Helpers

    private currentState(): ParserState {
        return this.stateStack[this.stateStack.length - 1];
    }

    private prepStateStackForNested(mode: string, epos?: number) {
        const repos = epos !== undefined ? epos : this.currentState().epos;
        this.stateStack.push(this.currentState().cloneForNested(mode, repos));
    }

    private popStateIntoParentOk() {
        const cf = this.stateStack.pop() as ParserState;
        this.currentState().moveStateIntoParent(cf);
    }

    private popStateReset() {
        this.stateStack.pop();
    }

    private recordExpectedError(token: Token, expected: string, contextinfo: string) {
        const cstate = this.currentState();
        cstate.errors.push(new ParserError(this.env.currentFile, token.getSourceInfo(), `Expected "${expected}" but got "${token.data || token.kind}" when parsing "${contextinfo}"`));
    }

    private recordErrorGeneral(sinfo: SourceInfo, msg: string) {
        const cstate = this.currentState();
        cstate.errors.push(new ParserError(this.env.currentFile, sinfo, msg));
    }

    private peekToken(pos?: number): Token {
        const cstate = this.currentState();
        
        const tpos = cstate.cpos + (pos || 0);
        if(cstate.cpos >= cstate.epos) {
            if(cstate.epos === this.tokens.length) {
                return this.tokens[this.tokens.length - 1];
            }
            else {
                return new Token(-1, -1, -1, 0, TokenStrings.Recover, undefined);
            }
        }
        else {
            return cstate.tokens[tpos];
        }
    }

    private peekTokenKind(pos?: number): string {
        return this.peekToken(pos || 0).kind;
    }

    private peekTokenData(pos?: number): string {
        return this.peekToken(pos || 0).data as string;
    }

    private testToken(kind: string): boolean {
        return this.peekTokenKind() === kind;
    }

    private testFollows(...kinds: string[]): boolean {
        for (let i = 0; i < kinds.length; ++i) {
            if (this.peekTokenKind(i) !== kinds[i]) {
                return false;
            }
        }

        return true;
    }

    private consumeToken() {
        if(this.currentState().cpos < this.currentState().epos) {
            this.currentState().cpos++;
        }
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
        const td = this.peekTokenData();
        this.consumeToken();

        return td;
    }

    private ensureToken(kind: string, contextinfo: string): boolean {
        if (this.testToken(kind)) {
            return true;
        }
        else {
            this.recordExpectedError(this.peekToken(), kind, contextinfo);
            return false;
        }
    }

    private ensureAndConsumeTokenAlways(kind: string, contextinfo: string) {
        this.ensureToken(kind, contextinfo);
        this.consumeToken();
    }

    private ensureAndConsumeTokenIf(kind: string, contextinfo: string) {
        const ok = this.ensureToken(kind, contextinfo);
        if(ok) {
            this.consumeToken();
        }
    }

    private ensureTokenOptions(...kinds: string[]): boolean {
        for (let i = 0; i < kinds.length; ++i) {
            if (this.testToken(kinds[i])) {
                return true;
            }
        }

        this.recordErrorGeneral(this.peekToken().getSourceInfo(), `Expected one of ${kinds.join(", ")}`);
        return false;
    }

    private scanMatchingParens(lp: string, rp: string): number | undefined {
        this.prepStateStackForNested("scan-matching-parens", undefined);

        this.ensureAndConsumeTokenAlways(lp, "scan-matching-parens");
        let pscount = 1;

        let tpos = this.currentState().cpos;
        let tok = this.peekToken();
        while (tok.kind !== TokenStrings.EndOfStream && tok.kind !== TokenStrings.Recover) {
            if (tok.kind === lp) {
                pscount = pscount + 1;
            }
            else if (tok.kind === rp) {
                pscount = Math.max(pscount - 1, 0);
            }
            else {
                //nop
            }

            if (pscount === 0) {
                this.popStateReset();
                return tpos + 1;
            }

            tpos++;
            this.consumeToken();
            tok = this.peekToken();
        }

        this.popStateReset();
        return undefined;
    }

    private scanToRecover(trecover: string): number | undefined {
        this.prepStateStackForNested("scan-to-recover", undefined);
        let pscount = 0;

        let tpos = this.currentState().cpos;
        let tok = this.peekToken();
        while (tok.kind !== TokenStrings.EndOfStream && tok.kind !== TokenStrings.Recover) {
            if(tok.kind === trecover && pscount === 0) {
                this.popStateReset();
                return tpos + 1;
            }

            if (LeftScanParens.indexOf(tok.kind) !== -1) {
                pscount = pscount + 1;
            }
            else if (RightScanParens.indexOf(tok.kind) !== -1) {
                pscount = Math.max(pscount - 1, 0);
            }
            else {
                //nop
            }

            tpos++;
            this.consumeToken();
            tok = this.peekToken();
        }

        this.popStateReset();
        return undefined;
    }

    private scanToSyncPos(...tsync: string[]): number | undefined {
        this.prepStateStackForNested("scan-to-sync", undefined);
        let pscount = 0;

        let tpos = this.currentState().cpos;
        let tok = this.peekToken();
        while (tok.kind !== TokenStrings.EndOfStream && tok.kind !== TokenStrings.Recover) {
            if(tsync.includes(tok.kind) && pscount === 0) {
                this.popStateReset();
                return tpos;
            }

            if (LeftScanParens.indexOf(tok.kind) !== -1) {
                pscount = pscount + 1;
            }
            else if (RightScanParens.indexOf(tok.kind) !== -1) {
                pscount = Math.max(pscount - 1, 0);
            }
            else {
                //nop
            }

            tpos++;
            this.consumeToken();
            tok = this.peekToken();
        }

        this.popStateReset();
        return undefined;
    }

    private scanToSyncEatParens(lp: string, rp: string): number | undefined {
        this.prepStateStackForNested("scan-to-sync-eat-parens", undefined);

        this.ensureAndConsumeTokenAlways(lp, "sync-eat-parens");
        let pscount = 1;

        let tpos = this.currentState().cpos;
        let tok = this.peekToken();
        while (tok.kind !== TokenStrings.EndOfStream && tok.kind !== TokenStrings.Recover) {
            if (tok.kind === lp) {
                pscount = pscount + 1;
            }
            else if (tok.kind === rp) {
                pscount = Math.max(pscount - 1, 0);
            }
            else {
                //nop
            }

            if (pscount === 0) {
                this.popStateReset();
                return tpos + 1;
            }

            tpos++;
            this.consumeToken();
            tok = this.peekToken();
        }

        this.popStateReset();
        return undefined;
    }

    private parseListOf<T>(contextinfobase: string, start: string, end: string, sep: string, fn: () => T): T[] {
        const closeparen = this.scanMatchingParens(start, end);
        this.prepStateStackForNested("list-" + contextinfobase, closeparen);

        let result: T[] = [];
        this.ensureAndConsumeTokenAlways(start, contextinfobase);
        while (!this.testToken(end) && !this.testToken(TokenStrings.Recover) && !this.testToken(TokenStrings.EndOfStream)) {
            const nextcomma = this.scanToRecover(sep);
            this.prepStateStackForNested("element-" + contextinfobase, nextcomma);

            const v = fn();
            result.push(v);
            
            if(this.testToken(end)) {
                //great this is the happy path we will exit next iter
                this.popStateIntoParentOk();
            }
            else if(this.testToken(sep)) {
                //consume the sep
                this.consumeToken();

                //check for a stray ,) type thing at the end of the list -- if we have it report and then continue
                if(this.testToken(end)) {
                    this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Stray , at end of list");
                }

                this.popStateIntoParentOk();
            }
            else {
                //ok all going wrong lets get out of here 
                this.popStateIntoParentOk();
                this.currentState().moveToRecoverPosition();
            }
        }

        this.ensureAndConsumeTokenIf(end, contextinfobase);
        this.popStateIntoParentOk();

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

    private identifierResolvesAsScopedConstOrFunction(name: string): NamespaceFunctionDecl | NamespaceConstDecl | undefined {
        const coredecl = this.env.assembly.getCoreNamespace();
        const cdm = coredecl.functions.find((f) => f.name === name) || coredecl.consts.find((c) => c.name === name);
        if(cdm !== undefined) {
            return cdm;
        }

        const nsdecl = this.env.currentNamespace;
        const ndm = nsdecl.functions.find((f) => f.name === name) || nsdecl.consts.find((c) => c.name === name);
        if(ndm !== undefined) {
            return ndm;
        }

        return undefined;
    }

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
        const hasterms = this.peekTokenKind(leadingscoper ? 2 : 1) === SYM_langle;

        if(nsroot === "Core") {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Cannot shadow the Core namespace");
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
        assert(isParsePhase_Enabled(this.currentPhase, ParsePhase_CompleteParsing));

        const nsroot = this.peekTokenData();

        const coredecl = this.env.assembly.getCoreNamespace();
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
            return this.parseIdentifierAccessChainHelper(false, coredecl, ["Core"]);
        }
        else if(this.env.currentNamespace.declaredNames.has(nsroot)) {
            return this.parseIdentifierAccessChainHelper(false, this.env.currentNamespace, [nsroot]);
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

    private normalizeTypeNameChain(sinfo: SourceInfo, ns: NamespaceDeclaration, typeTokens: {tname: string, terms: TypeSignature[]}[]): [NamespaceTypedef | undefined, AbstractNominalTypeDecl | undefined] | undefined {
        const tydef = ns.typeDefs.find((t) => t.name === typeTokens[0].tname);
        if(tydef !== undefined) {
            return [tydef, undefined];
        }
        
        const taskdef = ns.tasks.find((t) => t.name === typeTokens[0].tname);
        if(taskdef !== undefined) {
            return [undefined, taskdef];
        }

        //handle special Core types first
        if(ns.name === "Core") {
            const ndecl = this.tryNormalizeCoreType(ns, typeTokens);
            if(ndecl !== undefined) {
                return [undefined, ndecl];
            }
        }

        const nnt = ns.typedecls.find((t) => t.name === typeTokens[0].tname);
        if(nnt !== undefined) {
            return [undefined, nnt];
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
                    this.ensureAndConsumeTokenAlways(SYM_coloncolon, "attribute args");

                    this.ensureToken(TokenStrings.IdentifierName, "attribute args");
                    const tag = this.consumeTokenAndGetValue();

                    return {enumType: etype, tag: tag};
                });
            }

            return new DeclarationAttibute(attr, args, undefined);
        }
    }

    private parseAdditionalTypeDeclTag(): AdditionalTypeDeclTag {
        let isStatus = false;
        let isEvent = false;

        while(this.testToken(KW_status) || this.testToken(KW_event)) {
            if(isStatus || isEvent) {
                this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Cannot have multiple status/event tags");
            }

            isStatus = isStatus || this.testAndConsumeTokenIf(KW_status);
            isEvent = isEvent || this.testAndConsumeTokenIf(KW_event);
        }

        if(isStatus) {
            return AdditionalTypeDeclTag.Status;
        }
        else if(isEvent) {
            return AdditionalTypeDeclTag.Event;
        }
        else {
            return AdditionalTypeDeclTag.Std;
        }
    }

    private parseIdentifierAsTemplateVariable(): string {
        const vv = this.consumeTokenAndGetValue();
        if(!/[A-Z]/.test(vv)) {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Invalid template variable name -- must be an uppercase letter");
        }

        return vv;
    }

    private parseIdentifierAsNamespaceOrTypeName(): string {
        const vv = this.consumeTokenAndGetValue();
        if(!/^[A-Z][_a-zA-Z0-9]+/.test(vv)) {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Invalid namespace or type name -- must start with an uppercase letter");
        }

        return vv;
    }

    private parseIdentifierAsEnumMember(): string {
        const vv = this.consumeTokenAndGetValue();
        if(!/^[A-Z][_a-zA-Z0-9]+/.test(vv)) {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Invalid enum member name -- must start with an uppercase letter");
        }

        return vv;
    }

    private parseIdentifierAsStdVariable(): string {
        const vv = this.consumeTokenAndGetValue();
        if(vv === "_") {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Cannot use _ as an identifier name -- it is special ignored variable");
        }

        if(!/^[_a-z][_a-zA-Z0-9]*/.test(vv)) {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Invalid identifier name -- must start with a lowercase letter or _");
        }

        return vv;
    }

    private parseIdentifierAsIgnoreableVariable(): string {
        const vv = this.consumeTokenAndGetValue();
        
        if(!/^[_a-z][_a-zA-Z0-9]*/.test(vv)) {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Invalid identifier name -- must start with a lowercase letter or _");
        }

        return vv;
    }

    private parseInvokeTermRestriction(): InvokeTemplateTypeRestriction  {
        this.ensureAndConsumeTokenAlways(SYM_lbrace, "template term restiction");
        this.ensureAndConsumeTokenAlways(KW_when, "template term restiction");
        
        const trl = this.parseListOf<InvokeTemplateTypeRestrictionClause>("template term restiction list", SYM_lbrace, SYM_rbrace, SYM_semicolon, () => {
            if(this.testToken(KW_type)) {
                this.consumeToken();
                this.ensureAndConsumeTokenAlways(SYM_lparen, "template term restiction");

                this.ensureToken(TokenStrings.IdentifierName, "template term restiction");
                const vname = this.testToken(TokenStrings.IdentifierName) ? this.parseIdentifierAsTemplateVariable() : "[error]";

                this.ensureAndConsumeTokenAlways(SYM_rparen, "template term restiction");
                this.ensureAndConsumeTokenAlways(SYM_arrow, "template term restiction");

                const tunify = this.parseTypeSignature();

                return new InvokeTemplateTypeRestrictionClauseUnify(vname, tunify);
            }
            else {
                const ts = this.parseTemplateTypeReference();
                this.ensureAndConsumeTokenAlways(SYM_at, "template term restiction");
                const subtype = this.parseTypeSignature();

                return new InvokeTemplateTypeRestrictionClauseSubtype(ts as TemplateTypeSignature, subtype);
            }
        });

        this.ensureAndConsumeTokenAlways(SYM_rbrace, "template term restiction");
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

    private parsePreAndPostConditions(sinfo: SourceInfo, argnames: Set<string>, refParams: Set<string>, boundtemplates: Set<string>, taskcond: boolean, apicond: boolean): [PreConditionDecl[], PostConditionDecl[]] {
        let preconds: PreConditionDecl[] = [];

        this.env.scope = new StandardScopeInfo([...argnames].map((v) => new LocalVariableDefinitionInfo(v, true)), boundtemplates, this.wellknownTypes.get("Bool") as TypeSignature);
        while (this.testToken(KW_requires)) {
            this.consumeToken();
            
            let tag: string | undefined = undefined;
            if(this.testAndConsumeTokenIf(SYM_lbrack)) {
                if(this.ensureToken(TokenStrings.ExString, "requires tag")) {
                    tag = this.consumeTokenAndGetValue();
                }
                
                this.ensureAndConsumeTokenAlways(SYM_rbrack, "requires tag");
            }

            let softcheck = apicond && this.testToken(KW_softcheck);
            if(this.testAndConsumeTokenIf(KW_softcheck)) {
                if(!apicond) {   
                    this.recordErrorGeneral(sinfo, "Softcheck is only allowed in API pre/post conditions");
                }
            }

            const level = this.parseBuildInfo(KW_release);
            const exp = this.parseExpression();

            preconds.push(new PreConditionDecl(this.env.currentFile, sinfo, tag, level, softcheck, exp));

            this.ensureAndConsumeTokenIf(SYM_semicolon, "requires");
        }
        this.env.scope = undefined;

        let postconds: PostConditionDecl[] = [];

        const refnames = [...refParams].map((v) => new LocalVariableDefinitionInfo("$" + v, true));

        const postvardecls = [...[...argnames].map((v) => new LocalVariableDefinitionInfo(v, true)), ...refnames, new LocalVariableDefinitionInfo(WELL_KNOWN_RETURN_VAR_NAME, true)];
        if(taskcond || apicond) {
            postvardecls.push(new LocalVariableDefinitionInfo(WELL_KNOWN_EVENTS_VAR_NAME, true));
        }

        this.env.scope = new StandardScopeInfo(postvardecls, boundtemplates, this.wellknownTypes.get("Bool") as TypeSignature);
        
        while (this.testToken(KW_ensures)) {
            this.consumeToken();

            let tag: string | undefined = undefined;
            if(this.testAndConsumeTokenIf(SYM_lbrack)) {
                if(this.ensureToken(TokenStrings.ExString, "requires tag")) {
                    tag = this.consumeTokenAndGetValue();
                }
                
                this.ensureAndConsumeTokenAlways(SYM_rbrack, "requires tag");
            }

            let softcheck = apicond && this.testToken(KW_softcheck);
            if(this.testAndConsumeTokenIf(KW_softcheck)) {
                if(!apicond) {   
                    this.recordErrorGeneral(sinfo, "Softcheck is only allowed in API pre/post conditions");
                }
            }

            const level = this.parseBuildInfo(KW_release);
            const exp = this.parseExpression();

            postconds.push(new PostConditionDecl(this.env.currentFile, sinfo, tag, level, softcheck, exp));

            this.ensureAndConsumeTokenIf(SYM_semicolon, "ensures");
        }
        this.env.scope = undefined;

        return [preconds, postconds];
    }

    private parseSamples(sinfo: SourceInfo, boundtemplates: Set<string>): InvokeExample[] {
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
                    this.env.scope = new StandardScopeInfo([], boundtemplates, undefined);
                    const args = this.parseListOf<Expression>("example args", SYM_lparen, SYM_rparen, SYM_coma, () => this.parseExpression());
                    this.env.scope = undefined;

                    this.ensureAndConsumeTokenAlways(SYM_bigarrow, "example");

                    this.env.scope = new StandardScopeInfo([new LocalVariableDefinitionInfo(WELL_KNOWN_SRC_VAR_NAME, true)], boundtemplates, undefined);
                    const result = this.parseExpression();
                    this.env.scope = undefined;

                    return {args: args, output: result};
                });
                
                samples.push(new InvokeExampleDeclInline(this.env.currentFile, sinfo, istest, examples));
            }

            this.ensureAndConsumeTokenIf(SYM_semicolon, "example");
        }

        return samples;
    }

    private parseInvokeSignatureParameter(autotypeok: boolean): FunctionParameter {
        const cinfo = this.peekToken().getSourceInfo();

        const isref = this.testAndConsumeTokenIf(KW_ref);
        const isspread = this.testAndConsumeTokenIf(SYM_dotdotdot);

        if(isref && isspread) {
            this.recordErrorGeneral(cinfo, "Cannot have a parameter that is both a reference and a spread");
        }

        const idok = this.ensureToken(TokenStrings.IdentifierName, "function parameter");
        const pname = idok ? this.parseIdentifierAsStdVariable() : "[error]";

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
        let tags: TemplateTermDeclExtraTag[] = [];
        if(this.testAndConsumeTokenIf(SYM_colon)) {
            while(this.testToken(TokenStrings.IdentifierName) && (this.peekTokenData() === "unique" || this.peekTokenData() === "atomic")) {
                const data = this.consumeTokenAndGetValue();
                let tag = data === "unique" ? TemplateTermDeclExtraTag.Unique : TemplateTermDeclExtraTag.Atomic;
                if(tags.some((t) => t === tag)) {
                    this.recordErrorGeneral(this.peekToken(), "Cannot have duplicate template tags");
                }
            }

            ttype = this.parseTypeSignature();
        }

        return new InvokeTemplateTermDecl(tname, tags, ttype, isinferable);
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
        const cinfo = this.peekToken().getSourceInfo();

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
            this.recordErrorGeneral(this.peekToken(), "Lambda cannot be marked as both a pred and a fn");
        }
        if(!ispred && !isfn) {
            this.recordErrorGeneral(this.peekToken(), "Lambda must be either a pred or fn");
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
            this.recordExpectedError(this.peekToken(), SYM_bigarrow, "lambda declaration");
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
        const cinfo = this.peekToken().getSourceInfo();

        let isrecursive: "yes" | "no" | "cond" = "no";
        if(this.testToken(KW_recursive) || this.testToken(KW_recursive_q)) {
            isrecursive = this.testToken(KW_recursive) ? "yes" : "cond";
            this.consumeToken();
        }

        let fkind: "function" | "predicate" | "chktest" | "errtest" = "function";
        if(functionkind === "predicate") { 
            fkind = "predicate";
            this.ensureAndConsumeTokenAlways(KW_predicate, "predicate declaration");
        }
        else if(functionkind === "errtest") {
            fkind = "errtest";
            this.ensureAndConsumeTokenAlways(KW_errtest, "errtest declaration");
        }
        else if(functionkind === "chktest") {
            fkind = "chktest";
            this.ensureAndConsumeTokenAlways(KW_chktest, "chktest declaration");
        }
        else {
            this.ensureAndConsumeTokenAlways(KW_function, "function declaration");
        }

        const termRestrictions = this.parseInvokeTermRestrictionInfo();

        this.ensureToken(TokenStrings.IdentifierName, "function name");
        const fname = this.testToken(TokenStrings.IdentifierName) ? this.parseIdentifierAsStdVariable() : "[error]";

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

        const [preconds, postconds] = this.parsePreAndPostConditions(cinfo, argNames, refparams, boundtemplates, false, false);
        const samples = this.parseSamples(cinfo, boundtemplates);
    
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
        const cinfo = this.peekToken().getSourceInfo();

        let isrecursive: "yes" | "no" | "cond" = "no";
        if(this.testToken(KW_recursive) || this.testToken(KW_recursive_q)) {
            isrecursive = this.testToken(KW_recursive) ? "yes" : "cond";
            this.consumeToken();
        }

        const isref = this.testAndConsumeTokenIf(KW_ref);
        this.ensureAndConsumeTokenAlways(KW_method, "method declaration");

        const termRestrictions = this.parseInvokeTermRestrictionInfo();

        this.ensureToken(TokenStrings.IdentifierName, "method name");
        const fname = this.testToken(TokenStrings.IdentifierName) ? this.parseIdentifierAsStdVariable() : "[error]";

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

        const [preconds, postconds] = this.parsePreAndPostConditions(cinfo, argNames, refparams, boundtemplates, false, false);
        const samples = this.parseSamples(cinfo, boundtemplates);
    
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

    private parseActionInvokeDecl(attributes: DeclarationAttibute[], typeTerms: Set<string>, taskmain: string): TaskActionDecl | undefined {
        const cinfo = this.peekToken().getSourceInfo();

        this.ensureAndConsumeTokenAlways(KW_action, "action declaration");

        const termRestrictions = this.parseInvokeTermRestrictionInfo();

        this.ensureToken(TokenStrings.IdentifierName, "action name");
        const fname = this.testToken(TokenStrings.IdentifierName) ? this.parseIdentifierAsStdVariable() : "[error]";

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
    
        const [preconds, postconds] = this.parsePreAndPostConditions(cinfo, argNames, refparams, boundtemplates, fname === taskmain, false);
        const samples = this.parseSamples(cinfo, boundtemplates);
    
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
        const ltype = this.parseNoneableType();
        if (!this.testToken(SYM_bar)) {
            return ltype;
        }
        else {
            const sinfo = this.peekToken().getSourceInfo();
            this.consumeToken();
            const rtype = this.parseOrCombinatorType();

            return new UnionTypeSignature(sinfo, ltype, rtype);
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
        switch (this.peekTokenKind()) {
            case TokenStrings.Template: {
                return this.parseTemplateTypeReference();
            }
            case TokenStrings.IdentifierName: {
                return this.parseNominalType();
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
                const sinfo = this.peekToken().getSourceInfo();

                const closeparen = this.scanMatchingParens(SYM_lparen, SYM_rparen);
                this.prepStateStackForNested("paren-type", closeparen);

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
                            this.currentState().moveToRecoverPosition();
                        }
                    }
                }

                return ptype;
            }
            default: {
                return new ErrorTypeSignature(this.peekToken().getSourceInfo(), undefined);
            }
        }
    }

    private parseTemplateTypeReference(): TypeSignature {
        const sinfo = this.peekToken().getSourceInfo();

        const tname = this.parseIdentifierAsTemplateVariable();
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
        const sinfo = this.peekToken().getSourceInfo();

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
        const sinfo = this.peekToken().getSourceInfo();

        const entries = this.parseListOf<TypeSignature>("tuple type", SYM_lbrack, SYM_rbrack, SYM_coma, () => {
            return this.parseTypeSignature();
        });

        return new TupleTypeSignature(sinfo, entries);
    }

    private parseRecordType(): TypeSignature {
        const sinfo = this.peekToken().getSourceInfo();

        let pnames = new Set<string>();
        const entries = this.parseListOf<[string, TypeSignature]>("record type", SYM_lbrace, SYM_rbrace, SYM_coma, () => {
            this.ensureToken(TokenStrings.IdentifierName, "record type entry property name");

            const name = this.parseIdentifierAsStdVariable();
            if(pnames.has(name)) {
                this.recordErrorGeneral(this.peekToken(), `Duplicate property name ${name} in record type`);
            }
            pnames.add(name);

            this.ensureAndConsumeTokenIf(SYM_colon, "record type property type");
            const rtype = this.parseTypeSignature();

            return [name, rtype];
        });

        return new RecordTypeSignature(sinfo, entries);
    }

    private parseLambdaType(): TypeSignature {
        const sinfo = this.peekToken().getSourceInfo();

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
            this.recordErrorGeneral(this.peekToken(), "Lambda type must be either a fn or pred");

            if(!this.testToken(SYM_lparen)) {
                this.consumeToken();
            }
        }

        const params = this.parseInvokeSignatureParameters(sinfo, false, false);

        this.ensureAndConsumeTokenAlways(SYM_arrow, "lambda type reference");
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
                    this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Stray , at end of list");
                }
            }
            else {
                //error token check here -- we have a valid parse then assume a missing , and continue -- otherwise try to cleanup as best possible and continue
                //maybe this is where we want to do some tryParse stuff to recover as robustly as possible -- like in the TypeSpec list parse implementation

                if(!canrecover) {
                    break; //we can't scan to a known recovery token so just break and let it sort itself out
                }
                else {
                    this.currentState().moveToRecoverPosition();
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
            let vname = this.parseIdentifierAsIgnoreableVariable();
            this.consumeToken();

            if(/^\$[a-z_]/.test(vname)) {
                return vname;
            }
            else {
                this.recordErrorGeneral(this.peekToken(), "Binder name must start with $ and be lower case");
                return undefined;
            }
        }
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
                this.recordErrorGeneral(this.peekToken(), "Expected ITest");
                return undefined;
            }
        }
    }

    private parseITypeTest(isnot: boolean): ITest {
        this.consumeToken();
        const ttype = this.parseTypeSignature();
        this.ensureAndConsumeTokenAlways(SYM_rangle, "ITest");

        return new ITestType(isnot, ttype);
    }

    private parseILiteralTest(isnot: boolean): ITest {
        this.consumeToken();
        const literal = this.parseLiteralExpression();
        this.ensureAndConsumeTokenAlways(SYM_rbrack, "ITest");

        return new ITestLiteral(isnot, literal);
    }

    private parseInvokeTemplateArguments() {
        let args: TypeSignature[] = [];
        if (this.testToken(SYM_langle)) {
            args = this.parseListOf<TypeSignature>("template arguments", SYM_langle, SYM_rangle, SYM_coma, () => {
                return this.parseTypeSignature();
            });
        }

        return args;
    }

    private parseInvokeRecursiveArgs(): "yes" | "no" | "cond" {
        let recursive: "yes" | "no" | "cond" = "no";
         
        if(this.testToken(SYM_lbrack)) {
            this.consumeToken();
            if (!this.testToken(KW_recursive) && !this.testToken(KW_recursive_q)) {
                this.recordErrorGeneral(this.peekToken(), "Expected recursive annotation");
            }
    
            recursive = this.testToken("recursive") ? "yes" : "cond";
            if(!this.testToken(SYM_rbrack)) {
                this.consumeToken();
            }
    
            this.ensureAndConsumeTokenIf(SYM_rbrack, "recursive annotation");
        }
             
        return recursive;
    }

    private parseArguments(lparen: string, rparen: string, sep: string, refok: boolean, spreadok: boolean, mapargs: boolean, lambdaok: boolean): ArgumentList {
        const args = this.parseListOf<ArgumentValue>("argument list", lparen, rparen, sep, () => {
            if(this.testToken(KW_ref)) {
                if(!refok) {
                    this.recordErrorGeneral(this.peekToken(), "Cannot have a reference argument in this context");
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
                    this.recordErrorGeneral(this.peekToken(), "Cannot have a spread argument in this context");
                }
                this.consumeToken();
                const exp = this.parseExpression();

                return new SpreadArgumentValue(exp);
            }
            else if(this.testFollows(TokenStrings.IdentifierName, SYM_eq)) {
                const name = this.parseIdentifierAsStdVariable();
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
            this.recordErrorGeneral(this.peekToken(), `Duplicate argument name ${duplicateNames}`);
        }

        const multiplerefs = args.filter((arg) => arg instanceof RefArgumentValue).length > 1;
        if(multiplerefs) {
            this.recordErrorGeneral(this.peekToken(), "Cannot have multiple reference arguments");
        }

        const spreadidx = args.findIndex((arg, index) => arg instanceof SpreadArgumentValue && index !== args.length - 1);
        const badspread = spreadidx !== -1 && args.slice(spreadidx).some((arg) => !(arg instanceof NamedArgumentValue));
        if(badspread) {
            this.recordErrorGeneral(this.peekToken(), "Spread argument must be the last argument");
        }

        return new ArgumentList(args);
    }
    
    private parseLambdaTerm(): Expression {
        const sinfo = this.peekToken().getSourceInfo();

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

    private parseConstResourceExpression(): ConstantExpressionValue {
        this.env.pushStandardFunctionScope([], this.env.getScope().boundtemplates, undefined);
        this.env.pushBinderUnknownInConstantExpressionScope();
        const exp = this.parsePrimaryExpression(); //just a primary expression
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

    private parseImplicitNamespaceScopedConstOrFunc(decl: NamespaceFunctionDecl | NamespaceConstDecl): Expression {
        assert(false, "Not implemented -- parseImplicitNamespaceScopedConstOrFunc");
    }

    private parseNamespaceScopedFirstExpression(nspace: NamespaceDeclaration): Expression {
        const sinfo = this.peekToken().getSourceInfo();

        this.ensureAndConsumeTokenAlways(SYM_coloncolon, "namespace scoped expression");
        this.ensureToken(TokenStrings.IdentifierName, "namespace scoped expression");

        const idname = this.parseIdentifierAsStdVariable();

        const constOpt = nspace.consts.find((c) => c.name === idname);
        const funOpt = nspace.functions.find((f) => f.name === idname);
        if(constOpt) {
            return new AccessNamespaceConstantExpression(sinfo, nspace.fullnamespace, idname);
        }
        else if(funOpt) {
            const targs = this.parseInvokeTemplateArguments();
            const rec = this.parseInvokeRecursiveArgs();
            const args = this.parseArguments(SYM_lparen, SYM_rparen, SYM_coma, true, true, false, true);

            return new CallNamespaceFunctionExpression(sinfo, nspace.fullnamespace, idname, targs, rec, args);
        }
        else {
            this.recordErrorGeneral(sinfo, `Name '${nspace.fullnamespace.emit()}::${idname}' is not defined in this context`);
            return new ErrorExpression(sinfo, {ns: nspace, typeopt: undefined}, undefined);
        }
    }

    private parseTypeScopedFirstExpression(access: {nsScope: NamespaceDeclaration, scopeTokens: string[], typeTokens: {tname: string, terms: TypeSignature[]}[]}): Expression {
        assert(false, "Not implemented -- parseTypeScopedFirstExpression");

        //TODO: make sure to handle the #enum case here
    }

    private parseIdentifierFirstExpression(): Expression {
        const sinfo = this.peekToken().getSourceInfo();
        if (this.peekTokenData().startsWith("$")) {
            const idname = this.parseIdentifierAsStdVariable();
            
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
            const idname = this.parseIdentifierAsStdVariable();
            
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
            const peekname = this.peekTokenData();

            const isScopedConstOrFunc = this.identifierResolvesAsScopedConstOrFunction(this.peekTokenData());
            if(isScopedConstOrFunc !== undefined) {
                return this.parseImplicitNamespaceScopedConstOrFunc(isScopedConstOrFunc);
            }
            else {
                const access = this.parseIdentifierAccessChain();
                if(access === undefined) {
                    this.recordErrorGeneral(sinfo, `Could not resolve '${peekname}' in this context`);
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
    }

    private parseLetExpression(): Expression {
        const sinfo = this.peekToken().getSourceInfo();

        this.ensureAndConsumeTokenAlways(SYM_lbracebar, "let expression");

        const decls = this.parseListOf<{vname: string, vtype: TypeSignature | undefined, value: Expression}>("let expression", KW_let, KW_in, SYM_coma, () => {
            this.ensureToken(TokenStrings.IdentifierName, "let expression variable name");
            const vname = this.parseIdentifierAsIgnoreableVariable();

            let vtype: TypeSignature | undefined = undefined;
            if(this.testAndConsumeTokenIf(SYM_colon)) {
                vtype = this.parseTypeSignature();
            }

            this.ensureAndConsumeTokenIf(SYM_eq, "let expression");

            const value = this.parseExpression();

            return {vname: vname, vtype: vtype, value: value};
        });

        const body = this.parseExpression();

        this.ensureAndConsumeTokenAlways(SYM_rbracebar, "let expression");

        return new LetExpression(sinfo, decls, body);
    }

    private parsePrimaryExpression(): Expression {
        const sinfo = this.peekToken().getSourceInfo();

        const tk = this.peekTokenKind();
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
            return new LiteralRegexExpression(rstr.endsWith("/") ? ExpressionTag.LiteralUnicodeRegexExpression : ExpressionTag.LiteralExRegexExpression, sinfo, rstr);
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
        else if(tk === TokenStrings.ExString) {
            const sstr = this.consumeTokenAndGetValue();
            if(sstr.endsWith("_")) {
                const vval = sstr.slice(0, sstr.length - 1);
                const ttype = this.parseTypeSignature();
                return new LiteralTypeDeclValueExpression(sinfo, new LiteralSimpleExpression(ExpressionTag.LiteralExStringExpression, sinfo, vval), ttype);
            }
            else if(sstr.endsWith("[OF]")) {
                const vval = sstr.slice(0, sstr.length - "[OF]".length);
                const oftype = this.parseTypeSignature();
                return new LiteralTypedStringExpression(ExpressionTag.LiteralExTypedStringExpression, sinfo, vval, oftype);
            }
            else {
                return new LiteralSimpleExpression(ExpressionTag.LiteralExStringExpression, sinfo, sstr);
            }
        }
        else if(tk === TokenStrings.TemplateString) {
            const sstr = this.consumeTokenAndGetValue();
            return new LiteralTemplateStringExpression(ExpressionTag.LiteralTemplateStringExpression, sinfo, sstr);
        }
        else if(tk === TokenStrings.TemplateExString) {
            const sstr = this.consumeTokenAndGetValue();
            return new LiteralTemplateStringExpression(ExpressionTag.LiteralTemplateExStringExpression, sinfo, sstr);
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
        else if (tk === SYM_lbracebar) {
            return this.parseLetExpression();
        }
        else if(tk === SYM_lparen) {
            const closeparen = this.scanMatchingParens(SYM_lparen, SYM_rparen);
            this.prepStateStackForNested("paren-type", closeparen);

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
                        this.currentState().moveToRecoverPosition();
                    }
                }
            }

            this.popStateIntoParentOk();
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
                    this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Stray , at end of list");
                }
            }
            else {
                //error token check here -- we have a valid parse then assume a missing , and continue -- otherwise try to cleanup as best possible and continue
                //maybe this is where we want to do some tryParse stuff to recover as robustly as possible -- like in the TypeSpec list parse implementation

                if(!canrecover) {
                    break; //we can't scan to a known recovery token so just break and let it sort itself out
                }
                else {
                    this.currentState().moveToRecoverPosition();
                }
            }
        }

        return new ConstructorEListExpression(sinfo, new ArgumentList(exps));
    }

    private parsePostfixExpression(): Expression {
        let rootexp = this.parsePrimaryExpression();

        let ops: PostfixOperation[] = [];
        while (true) {
            const sinfo = this.peekToken().getSourceInfo();

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
            else if(this.testToken(SYM_bang) || this.testFollows(SYM_bang, SYM_bang)) {
                this.consumeToken();
                const opr = this.testAndConsumeTokenIf(SYM_bang) ? "base" : "value";
                
                ops.push(new PostfixTypeDeclValue(sinfo, opr));
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

    private prefixStackApplicationHandler(exp: Expression, sinfo: SourceInfo, ops: [string, TypeSignature | undefined][]): Expression {
        for (let i = 0; i < ops.length; ++i) {
            const op = ops[i];

            if (op[0] === "as") {
                exp = new ParseAsTypeExpression(sinfo, exp, op[1] as TypeSignature);
            }
            else if (op[0] === SYM_bang) {
                exp = new PrefixNotOpExpression(sinfo, exp);
            }
            else if (op[0] === SYM_negate) {
                exp = new PrefixNegateOrPlusOpExpression(sinfo, exp, "-");
            }
            else if (op[0] === SYM_positive) {
                exp = new PrefixNegateOrPlusOpExpression(sinfo, exp, "+");
            }
            else {
                ;
            }
        }

        return exp;
    }

    private parsePrefixExpression(): Expression {
        const sinfo = this.peekToken().getSourceInfo();

        let ops: [string, TypeSignature | undefined][] = [];
        while(this.testToken(SYM_bang) || this.testToken(SYM_positive) || this.testToken(SYM_negate) || this.testToken(SYM_langle)) {
            if(this.testToken(SYM_langle)) {
                this.consumeToken();
                const ttype = this.parseTypeSignature();
                this.ensureAndConsumeTokenAlways(SYM_rangle, "parse type as");
                ops.push(["as", ttype]);
            }
            else {
                ops.push([this.consumeTokenAndGetValue(), undefined]);
            }
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
        const sinfo = this.peekToken().getSourceInfo();
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
        const sinfo = this.peekToken().getSourceInfo();
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
        const sinfo = this.peekToken().getSourceInfo();
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
        const sinfo = this.peekToken().getSourceInfo();
        const exp = this.parseRelationalExpression();

        if (this.testAndConsumeTokenIf(SYM_ampamp)) {
            return new BinLogicAndExpression(sinfo, exp, this.parseAndExpression());
        }
        else {
            return exp;
        }
    }

    private parseOrExpression(): Expression {
        const sinfo = this.peekToken().getSourceInfo();
        const exp = this.parseAndExpression();

        if (this.testAndConsumeTokenIf(SYM_barbar)) {
            return new BinLogicOrExpression(sinfo, exp, this.parseOrExpression());
        }
        else {
            return exp;
        }
    }

    private parseImpliesExpression(): Expression {
        const sinfo = this.peekToken().getSourceInfo();
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

    private parseIfTest(isexp: boolean): [Expression, string | undefined, boolean, boolean, ITest | undefined] {
        let exp: Expression;
        let bindername: string | undefined = undefined;
        let implicitdef: boolean = true;
        let ispostflow: boolean;
        let itest: ITest | undefined = undefined;
        let dobind: boolean;

        this.ensureAndConsumeTokenIf(SYM_lparen, "if test");
        if(this.testFollows(TokenStrings.IdentifierName, SYM_eq)) {
            bindername = this.parseBinderInfo();
            implicitdef = false;
            this.ensureAndConsumeTokenAlways(SYM_eq, "if test");
        }
        
        exp = this.parseExpression();
        this.ensureAndConsumeTokenIf(SYM_rparen, "if test");

        if(this.testAndConsumeTokenIf(SYM_atat)) {
            ispostflow = true;
            dobind = true
        }
        else if(this.testAndConsumeTokenIf(SYM_at)) {
            ispostflow = false;
            dobind = true;
        }
        else {
            ispostflow = false;
            dobind = false;
        }
        itest = !this.testToken(isexp ? KW_then : SYM_lbrace) ? this.parseITest() : undefined;

        if(isexp && ispostflow) {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Cannot have postflow in if-expression");
            ispostflow = false;
        }

        if(dobind && itest === undefined) {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Cannot have binder without itest");
            bindername = undefined;
        }

        if(bindername !== undefined && !dobind) {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Cannot have binder name without '@' or '@@'");
            bindername = undefined;
        }

        if(itest !== undefined && implicitdef) {
            if(exp instanceof AccessVariableExpression) {
                bindername = "$" + exp.srcname;
            }
            else {
                bindername = "$_";
            }
        }

        if(ispostflow && (!implicitdef || !(exp instanceof AccessVariableExpression))) {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Cannot have postflow without implicitdef or using a non-variable expression");
            ispostflow = false;
        }

        return [exp, bindername, implicitdef, ispostflow, itest];
    }

    private parseSwitchOrMatchTest(isexp: boolean): [Expression, string | undefined, boolean, boolean] {
        let exp: Expression;
        let bindername: string | undefined = undefined;
        let implicitdef: boolean = true;
        let ispostflow: boolean;
        let dobind: boolean;

        this.ensureAndConsumeTokenIf(SYM_lparen, "swtich/match test");
        if(this.testFollows(TokenStrings.IdentifierName, SYM_eq)) {
            bindername = this.parseBinderInfo();
            implicitdef = false;
            this.ensureAndConsumeTokenAlways(SYM_eq, "if test");
        }
        
        exp = this.parseExpression();
        this.ensureAndConsumeTokenIf(SYM_rparen, "swtich/match test");

        if(this.testAndConsumeTokenIf(SYM_atat)) {
            ispostflow = true;
            dobind = true;
        }
        else if(this.testAndConsumeTokenIf(SYM_at)) {
            ispostflow = false;
            dobind = true;
        }
        else {
            ispostflow = false;
            dobind = false;
        }

        if(isexp && ispostflow) {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Cannot have postflow in switch/match expression");
            ispostflow = false;
        }

        if(bindername !== undefined && !dobind) {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Cannot have binder name without '@' or '@@'");
            bindername = undefined;
        }

        if(dobind && implicitdef) {
            if(exp instanceof AccessVariableExpression) {
                bindername = "$" + exp.srcname;
            }
            else {
                bindername = "$_";
            }
        }

        if(ispostflow && (!implicitdef || !(exp instanceof AccessVariableExpression))) {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Cannot have postflow without implicitdef or using a non-variable expression");
            ispostflow = false;
        }

        return [exp, bindername, implicitdef, ispostflow];
    }

    private parseIfExpression(): Expression {
        const sinfo = this.peekToken().getSourceInfo();

        this.consumeToken();
        const [iexp, binder, implicitdef, _, itest] = this.parseIfTest(true);

        this.ensureAndConsumeTokenIf(KW_then, "if expression value")

        const ifvalueinfo = this.parseExpressionWithBinder(binder === undefined ? [] : [binder]);
        let btrue: BinderInfo | undefined = undefined;
        if(ifvalueinfo.used.length > 0) {
            btrue = new BinderInfo(ifvalueinfo.used[0].srcname, ifvalueinfo.used[0].scopedname, implicitdef, false);
        }

        this.ensureAndConsumeTokenIf(KW_else, "if expression else value");
        const elsevalueinfo = this.parseExpressionWithBinder(binder === undefined ? [] : [binder]);

        let belse: BinderInfo | undefined = undefined;
        if(elsevalueinfo.used.length > 0) {
            belse = new BinderInfo(elsevalueinfo.used[0].srcname, elsevalueinfo.used[0].scopedname, implicitdef, false);
        }

        return new IfExpression(sinfo, new IfTest(iexp, itest), ifvalueinfo.exp, btrue, elsevalueinfo.exp, belse);
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
        const sinfo = this.peekToken().getSourceInfo();
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
            const sinfo = this.peekToken().getSourceInfo();
            const name = this.parseIdentifierAsStdVariable();
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
        const sinfo = this.peekToken().getSourceInfo();

        this.ensureTokenOptions(TokenStrings.IdentifierName, KW_under);
        const name = this.parseIdentifierAsIgnoreableVariable();

        let itype = this.env.SpecialAutoSignature;
        if (this.testAndConsumeTokenIf(":")) {
            itype = this.parseTypeSignature();
        }

        if(!/^[a-z_]/.test(name)) {
            this.recordErrorGeneral(sinfo, `Local variables must start with a lowercase letter or underscore but got "${name}"`);
        }

        return { name: name, vtype: itype };
    }

    parseMultiDeclarationVarInfo(isfirst: boolean): {name: string, vtype: TypeSignature}[] {
        let decls: {name: string, vtype: TypeSignature}[] = [];

        if(isfirst && this.testToken(SYM_coma)) {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Extranious comma in declaration list");
        }

        while(isfirst || this.testAndConsumeTokenIf(SYM_coma)) {
            isfirst = false;

            const dd = this.parseSingleDeclarationVarInfo();
            decls.push(dd);
        }

        return decls;
    }

    parseSingleAssignmentVarInfo(): string {
        const sinfo = this.peekToken().getSourceInfo();

        this.ensureTokenOptions(TokenStrings.IdentifierName, KW_under);
        const name = this.parseIdentifierAsIgnoreableVariable();

        if(!/^[a-z_]/.test(name)) {
            this.recordErrorGeneral(sinfo, `Local variables must start with a lowercase letter or underscore but got "${name}"`);
        }

        return name;
    }

    parseMultiAssignmentVarInfo(isfirst: boolean): string[] {
        let assigns: string[] = [];

        if(isfirst && this.testToken(SYM_coma)) {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Extranious comma in declaration list");
        }

        while(isfirst || this.testAndConsumeTokenIf(SYM_coma)) {
            isfirst = false;

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
        const sinfo = this.peekToken().getSourceInfo();

        if (this.testToken(SYM_semicolon)) {
            return new EmptyStatement(sinfo);
        }
        else if (this.testToken(KW_var) || this.testToken(KW_let)) {
            const isConst = this.testToken(KW_let);
            
            this.consumeToken();
            const assigns = this.parseMultiDeclarationVarInfo(true);

            if(this.testToken(SYM_semicolon)) {
                if(isConst) {
                    this.recordErrorGeneral(sinfo, "Cannot declare as const without an assignment");
                }

                if(assigns.some((vv) => vv.vtype instanceof AutoTypeSignature)) {
                    this.recordErrorGeneral(sinfo, "Cannot declare a variable with an auto type without an assignment");
                }

                assigns.forEach((vv) => {
                    const okadd = this.env.addVariable(vv.name, isConst, false);
                    if(!okadd) {
                        this.recordErrorGeneral(sinfo, `Variable ${vv.name} cannot be defined`);
                    }
                });

                return assigns.length === 1 ? new VariableDeclarationStatement(sinfo, assigns[0].name, assigns[0].vtype) : new VariableMultiDeclarationStatement(sinfo, assigns);
            }
            else if(this.testToken(SYM_eq)) {
                this.consumeToken();

                const exp = this.parseRHSExpression();
                if(this.testToken(SYM_semicolon)) {
                    //could be elist type expression but we need to wait for type checking
                    assigns.forEach((vv) => {
                        const okadd = this.env.addVariable(vv.name, isConst, assigns.length > 1);
                        if(!okadd) {
                            this.recordErrorGeneral(sinfo, `Variable ${vv.name} cannot be defined`);
                        }
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
                        const okadd = this.env.addVariable(vv.name, isConst, true);
                        if(!okadd) {
                            this.recordErrorGeneral(sinfo, `Variable ${vv.name} is already defined`);
                        }
                    });

                    return assigns.length === 1 ? new VariableInitializationStatement(sinfo, isConst, assigns[0].name, assigns[0].vtype, exps[0]) : new VariableMultiInitializationStatement(sinfo, isConst, assigns, exps);
                }
            }
            else {
                this.recordErrorGeneral(sinfo, `Expected a \";\" or an assignment after variable declaration but got ${this.peekTokenKind()}`);
                return new ErrorStatement(sinfo);
            }
        }
        else if (this.testFollows(TokenStrings.IdentifierName, SYM_eq) || this.testFollows(KW_under, SYM_eq)) {
            const vname = this.parseSingleAssignmentVarInfo();

            const okassign = this.env.assignVariable(vname);
            if(!okassign) {
                this.recordErrorGeneral(sinfo, `Cannot assign to variable ${vname}`);
            }

            this.ensureAndConsumeTokenIf(SYM_eq, "assignment statement");
            const exp = this.parseRHSExpression();

            return new VariableAssignmentStatement(sinfo, vname, exp);
        }
        else if (this.testFollows(TokenStrings.IdentifierName, SYM_coma) || this.testFollows(KW_under, SYM_coma)) {
            const vnames = this.parseMultiAssignmentVarInfo(true);

            this.ensureAndConsumeTokenIf(SYM_eq, "assignment statement");
            const exp = this.parseRHSExpression();

            if(this.testToken(SYM_semicolon)) {
                //could be elist type expression but we need to wait for type checking
                vnames.forEach((vv) => {
                    const okassign = this.env.assignVariable(vv);
                    if(!okassign) {
                        this.recordErrorGeneral(sinfo, `Cannot assign to variable ${vv}`);
                    }
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
                this.ensureToken(TokenStrings.ExString, "validate statement tag");
                diagnosticTag = this.consumeTokenAndGetValue();
                this.ensureAndConsumeTokenAlways(SYM_rbrack, "validate statement tag");
            }

            const exp = this.parseExpression();

            return new ValidateStatement(sinfo, exp, diagnosticTag);
        }
        else if (this.testToken(KW__debug)) {
            this.consumeToken();

            this.ensureAndConsumeTokenAlways(SYM_lparen, "_debug statement");
            const value = this.parseExpression();
            this.ensureAndConsumeTokenAlways(SYM_rparen, "_debug statement");
            
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
        const sinfo = this.peekToken().getSourceInfo();

        this.env.pushStandardBlockScope();

        const closeparen = this.scanMatchingParens(SYM_lbrace, SYM_rbrace);
        this.prepStateStackForNested("BlockStatement", closeparen);

        let stmts: Statement[] = [];
        this.ensureAndConsumeTokenAlways(SYM_lbrace, "block statement");
        while(!this.testToken(SYM_rbrace) && !this.testToken(TokenStrings.Recover) && !this.testToken(TokenStrings.EndOfStream)) {
            const stmt = this.parseStatement();
            stmts.push(stmt);
        }
        this.ensureAndConsumeTokenAlways(SYM_rbrace, "block statement");
        
        this.popStateIntoParentOk();
        this.env.popStandardBlockScope();

        if(stmts.length === 0) {
            this.recordErrorGeneral(sinfo, "Empty block statement -- should include a ';' to indicate intentionally empty block");
        }

        return new BlockStatement(sinfo, stmts);
    }

    private parseScopedBlockStatementWithBinderTracking(bindernames: string[]): {block: BlockStatement, used: {srcname: string, scopedname: string}[]} {
        const sinfo = this.peekToken().getSourceInfo();

        this.env.pushBinderExpressionScope(bindernames);

        const closeparen = this.scanMatchingParens(SYM_lbrace, SYM_rbrace);
        this.prepStateStackForNested("BlockStatement", closeparen);

        let stmts: Statement[] = [];
        this.ensureAndConsumeTokenAlways(SYM_lbrace, "block statement");
        while(!this.testToken(SYM_rbrace) && !this.testToken(TokenStrings.Recover) && !this.testToken(TokenStrings.EndOfStream)) {
            const stmt = this.parseStatement();
            stmts.push(stmt);
        }
        this.ensureAndConsumeTokenAlways(SYM_rbrace, "block statement");
        
        this.popStateIntoParentOk();
        const used = this.env.popBinderExpressionScope();

        if(stmts.length === 0) {
            this.recordErrorGeneral(sinfo, "Empty block statement -- should include a ';' to indicate intentionally empty block");
        }
        
        return {block: new BlockStatement(sinfo, stmts), used: used};
    }

    private parseIfElseStatement(): Statement {
        const sinfo = this.peekToken().getSourceInfo();

        this.ensureAndConsumeTokenAlways(KW_if, "if statement cond");
        const [iexp, binder, implicitdef, ispostflow, itest] = this.parseIfTest(false);

        const ifbody = this.parseScopedBlockStatementWithBinderTracking(binder === undefined ? [] : [binder]);
        let ifbind: BinderInfo | undefined = undefined;
        if(ifbody.used.length > 0) {
            ifbind = new BinderInfo(ifbody.used[0].srcname, ifbody.used[0].scopedname, implicitdef, ispostflow);
        }

        let conds: {cond: IfTest, block: BlockStatement}[] = [];
        while (this.testAndConsumeTokenIf(KW_elif)) {
            const [kiexp, kbinder, _k2, _k3, kitest] = this.parseIfTest(false);
            if(kbinder !== undefined) {
                this.recordErrorGeneral(sinfo, "Cannot have a binder in an if-elif-else statement");
            }
            const elifbody = this.parseScopedBlockStatement();
           
            conds.push({cond: new IfTest(kiexp, kitest), block: elifbody});
        }

        if(conds.length === 0) {
            if(!this.testAndConsumeTokenIf(KW_else)) {
                return new IfStatement(sinfo, new IfTest(iexp, itest), ifbody.block, ifbind);
            }
            else {
                const elsebody = this.parseScopedBlockStatementWithBinderTracking([]);
                let elsebind: BinderInfo | undefined = undefined;
                if(elsebody.used.length > 0) {
                    elsebind = new BinderInfo(elsebody.used[0].srcname, elsebody.used[0].scopedname, false, ispostflow);
                }

                return new IfElseStatement(sinfo, new IfTest(iexp, itest), ifbody.block, ifbind, elsebody.block, elsebind);
            }
        }
        else {
            if(binder !== undefined) {
                this.recordErrorGeneral(sinfo, "Cannot have a binder in an if-elif-else statement");
            }

            if(ifbody.used.length > 0) {
                this.recordErrorGeneral(sinfo, "Cannot have a binder in an if-elif-else statement");
            }

            const elssebody = this.parseScopedBlockStatement();
            return new IfElifElseStatement(sinfo, [{cond: new IfTest(iexp, itest), block: ifbody.block}, ...conds], elssebody);
        }
    }

    private parseSwitchStatement(): Statement {
        const sinfo = this.peekToken().getSourceInfo();
        
        this.ensureAndConsumeTokenAlways(KW_switch, "switch statement dispatch value");

        const [sexp, binder, implicitdef, ispostflow] = this.parseSwitchOrMatchTest(true);

        let entries: { lval: LiteralExpressionValue | undefined, value: BlockStatement, bindername: string | undefined }[] = [];
        this.ensureAndConsumeTokenAlways(SYM_lbrace, "switch statement options");
        
        const swlit = this.parseSwitchLiteralGuard();
        this.ensureAndConsumeTokenIf(SYM_bigarrow, "switch statement entry");
        const svalue = this.parseScopedBlockStatementWithBinderTracking(binder === undefined ? [] : [binder]);

        entries.push({ lval: swlit, value: svalue.block, bindername: svalue.used.length !== 0 ? svalue.used[0].srcname : undefined });
        while (this.testToken(SYM_bar)) {
            this.consumeToken();

            const swlitx = this.parseSwitchLiteralGuard();
            this.ensureAndConsumeTokenIf(SYM_bigarrow, "switch statement entry");
            const svaluex = this.parseScopedBlockStatementWithBinderTracking(binder === undefined ? [] : [binder]);

            entries.push({ lval: swlitx, value: svaluex.block, bindername: svaluex.used.length !== 0 ? svaluex.used[0].srcname : undefined });
        }
        this.ensureAndConsumeTokenAlways(SYM_rbrace, "switch statement options");

        let bindinfo: BinderInfo | undefined = undefined;
        if(binder !== undefined && entries.some((cc) => cc.bindername !== undefined)) {
            bindinfo = new BinderInfo(binder, this.env.getScope().getBinderVarName(binder), implicitdef, ispostflow);
        }

        return new SwitchStatement(sinfo, [sexp, bindinfo], entries);
    }

    private parseMatchStatement(): Statement {
        const sinfo = this.peekToken().getSourceInfo();
        
        this.ensureAndConsumeTokenAlways(KW_match, "match statement dispatch value");

        const [mexp, binder, implicitdef, ispostflow] = this.parseSwitchOrMatchTest(true);

        let entries: { mtype: TypeSignature | undefined, value: BlockStatement, bindername: string | undefined  }[] = [];
        this.ensureAndConsumeTokenAlways(SYM_lbrace, "match statement options");

        const mtype = this.parseMatchTypeGuard();
        this.ensureAndConsumeTokenIf(SYM_bigarrow, "match statement entry");
        const mvalue = this.parseScopedBlockStatementWithBinderTracking(binder === undefined ? [] : [binder]);

        entries.push({ mtype: mtype, value: mvalue.block, bindername: mvalue.used.length !== 0 ? mvalue.used[0].srcname : undefined});
        while (this.testToken(SYM_bar)) {
            this.consumeToken();
            
            const mtypex = this.parseMatchTypeGuard();
            this.ensureAndConsumeTokenIf(SYM_bigarrow, "match statement entry");
            const mvaluex = this.parseScopedBlockStatementWithBinderTracking(binder === undefined ? [] : [binder]);

            entries.push({ mtype: mtypex, value: mvaluex.block, bindername: mvaluex.used.length !== 0 ? mvaluex.used[0].srcname : undefined});
        }
        this.ensureAndConsumeTokenAlways(SYM_rbrace, "switch statment options");

        let bindinfo: BinderInfo | undefined = undefined;
        if(binder !== undefined && entries.some((cc) => cc.bindername !== undefined)) {
            bindinfo = new BinderInfo(binder, this.env.getScope().getBinderVarName(binder), implicitdef, ispostflow);
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
            this.prepStateStackForNested("line-statement", closesemi);

            const result = this.parseLineStatement();
            
            if(!this.testToken(SYM_semicolon)) {
                //we gotta recover
                this.recordExpectedError(this.peekToken(), SYM_semicolon, "line statement");
                this.currentState().moveToRecoverPosition();
            }

            if(this.testToken(SYM_semicolon)) {
                this.consumeToken();
            }

            this.popStateIntoParentOk();

            return result;
        }
    }

    private parseBody(attribs: DeclarationAttibute[], isPredicate: boolean, isLambda: boolean): BodyImplementation {
        const sinfo = this.peekToken().getSourceInfo();

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
            const iname = this.parseIdentifierAsStdVariable();
            this.ensureAndConsumeTokenIf(SYM_semicolon, "body");

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
        let tags: TemplateTermDeclExtraTag[] = [];
        if(this.testAndConsumeTokenIf(SYM_colon)) {
            while(this.testToken(TokenStrings.IdentifierName) && (this.peekTokenData() === "unique" || this.peekTokenData() === "atomic")) {
                const data = this.consumeTokenAndGetValue();
                let tag = data === "unique" ? TemplateTermDeclExtraTag.Unique : TemplateTermDeclExtraTag.Atomic;
                if(tags.some((t) => t === tag)) {
                    this.recordErrorGeneral(this.peekToken(), "Cannot have duplicate template tags");
                }
            }

            ttype = this.parseTypeSignature();
        }

        return new TypeTemplateTermDecl(tname, tags, ttype);
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
        this.currentState().skipToPosition(spoc);
    }

    private scanOverCodeParenSet(lp: string, rp: string) {
        const spoc = this.scanToSyncEatParens(lp, rp);
        this.currentState().skipToPosition(spoc);
    }

    private parseNamespaceUsing() {
        const sinfo = this.peekToken().getSourceInfo();

        this.ensureAndConsumeTokenAlways(KW_using, "namespce using");
        this.ensureToken(TokenStrings.IdentifierName, "namespce using");
            
        const chain: string[] = [];
        while(this.testToken(TokenStrings.IdentifierName)) {
            chain.push(this.parseIdentifierAsNamespaceOrTypeName());
            if(!this.testToken(SYM_coloncolon)) {
                break;
            }
            this.consumeToken();
        }

        if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterNames)) {
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
                    const asns = this.parseIdentifierAsNamespaceOrTypeName();

                    if(this.env.currentNamespace.istoplevel) {
                        this.env.currentNamespace.usings.push(new NamespaceUsing(this.env.currentFile, new FullyQualifiedNamespace(chain), asns));
                    }
                    else {
                        this.recordErrorGeneral(sinfo, `Cannot "use" a namespace in a non-toplevel namespace`);
                    }
                }
            }
        }
        else {
            if(isParsePhase_Enabled(this.currentPhase, ParsePhase_CompleteParsing)) {
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
            this.ensureAndConsumeTokenIf(SYM_semicolon, "namespace using");
        }
    }

    //scan (or recover) to the next declaration or end brace
    private namespaceParseScanCover(endtok: string) {
        const rpos = this.scanToSyncPos(endtok, ...NAMESPACE_DECL_FIRSTS);
        if(rpos === undefined) {
            this.currentState().moveToRecoverPosition();
        }
        else {
            this.currentState().skipToPosition(rpos);
        }
    }

    private parseNamespaceMembers(endtok: string) {
        const rpos = this.scanToRecover(endtok);
        this.prepStateStackForNested("namespace", rpos);

        while (!this.testToken(endtok) && !this.testToken(TokenStrings.EndOfStream) && !this.testToken(TokenStrings.Recover)) {
            let attributes: DeclarationAttibute[] = [];
            while(this.testToken(TokenStrings.Attribute) || this.testToken(TokenStrings.DocComment)) {
                const attr = this.parseAttribute();
                attributes.push(attr);
            }

            this.prepStateStackForNested("namespace-member", undefined);

            const sinfo = this.peekToken().getSourceInfo();
            if(this.testToken(KW_type)) {
                this.parseNamespaceTypedef(attributes);
            }
            else if (this.testToken(KW_const)) {
                this.parseNamespaceConstant(attributes);
            }
            else if(this.testFollows(KW_function) || this.testFollows(KW_recursive, KW_function) || this.testFollows(KW_recursive_q, KW_function)) {
                this.parseNamespaceFunction(attributes, endtok);
            }
            else if(this.testFollows(KW_predicate) || this.testFollows(KW_recursive, KW_predicate) || this.testFollows(KW_recursive_q, KW_predicate)) {
                this.parseNamespaceFunction(attributes, endtok);
            }
            else if(this.testFollows(KW_chktest) || this.testFollows(KW_errtest)) {
                this.parseNamespaceFunction(attributes, endtok);
            }
            else if(this.testFollows(KW_entity) || this.testFollows(KW_status, KW_entity) || this.testFollows(KW_event, KW_entity)) {
                this.parseEntity(attributes, endtok);
            }
            else if(this.testFollows(KW_concept) || this.testFollows(KW_status, KW_concept) || this.testFollows(KW_event, KW_concept)) {
                this.parseConcept(attributes, endtok);
            }
            else if(this.testFollows(KW_enum) || this.testFollows(KW_status, KW_enum) || this.testFollows(KW_event, KW_enum)) {
                this.parseEnum(attributes, endtok);
            }
            else if(this.testFollows(KW_validator) || this.testFollows(KW_status, KW_validator) || this.testFollows(KW_event, KW_validator)) {
                this.parseValidatorTypedecl(attributes, endtok);
            }
            else if(this.testFollows(KW_typedecl) || this.testFollows(KW_status, KW_typedecl) || this.testFollows(KW_event, KW_typedecl)) {
                this.parseTypeDecl(attributes, endtok);
            }
            else if(this.testFollows(KW_datatype) || this.testFollows(KW_status, KW_datatype) || this.testFollows(KW_event, KW_datatype)) {
                this.parseDataTypeDecl(attributes);
            }
            else if(this.testToken(KW_task)) {
                this.parseTask(attributes, endtok);
            }
            else if(this.testToken(KW_api)) {
                this.parseAPI(attributes);
            }
            else if(this.testToken(KW_namespace)) {
                this.parseSubNamespace();
            }
            else {
                this.recordErrorGeneral(sinfo, `Unknown member ${this.peekTokenData()}`);

                this.consumeToken();
                this.namespaceParseScanCover(endtok);
            }

            this.popStateIntoParentOk();
        }

        this.popStateIntoParentOk();
    }

    private parseSubNamespace() {
        this.ensureAndConsumeTokenAlways(KW_namespace, "nested namespace declaration");
        this.ensureToken(TokenStrings.IdentifierName, "nested namespace declaration");

        const nsname = this.parseIdentifierAsNamespaceOrTypeName();

        const sinfo = this.peekToken().getSourceInfo();
        if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterNames)) {
            if (this.env.currentNamespace.checkDeclNameClashNS(nsname)) {
                this.recordErrorGeneral(sinfo, `Collision between namespace and other names -- ${nsname}`);
            }

            const nsdecl = new NamespaceDeclaration(false, nsname, new FullyQualifiedNamespace([...this.env.currentNamespace.fullnamespace.ns, nsname]));

            this.env.currentNamespace.subns.push(nsdecl);
            this.env.currentNamespace.declaredSubNSNames.add(nsname);

            const ons = this.env.currentNamespace;

            this.env.currentNamespace = nsdecl;
            this.ensureAndConsumeTokenAlways(SYM_lbrace, "nested namespace declaration");
            this.parseNamespaceMembers(SYM_rbrace);
            this.ensureAndConsumeTokenAlways(SYM_rbrace, "nested namespace declaration");

            this.env.currentNamespace = ons;
        }
        else {
            const ons = this.env.currentNamespace;

            const nsdecl = this.env.currentNamespace.subns.find((ns) => ns.name === nsname) as NamespaceDeclaration;
            this.env.currentNamespace = nsdecl;
            this.ensureAndConsumeTokenAlways(SYM_lbrace, "nested namespace declaration");
            this.parseNamespaceMembers(SYM_rbrace);
            this.ensureAndConsumeTokenAlways(SYM_rbrace, "nested namespace declaration");

            this.env.currentNamespace = ons;
        }
    }

    private parseNamespaceTypedef(attributes: DeclarationAttibute[]) {
        const sinfo = this.peekToken().getSourceInfo();
        this.ensureAndConsumeTokenAlways(KW_type, "type alias");
        this.ensureToken(TokenStrings.IdentifierName, "type alias");
        const tyname = this.parseIdentifierAsNamespaceOrTypeName();

        if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterNames)) {
            if (this.env.currentNamespace.checkDeclNameClashType(tyname, this.testToken(SYM_langle))) {
                this.recordErrorGeneral(sinfo, `Collision between type alias and other names -- ${tyname}`);
            }

            this.env.currentNamespace.declaredNames.add(tyname);
            this.env.currentNamespace.declaredTypeNames.push({name: tyname, hasterms: this.testToken(SYM_langle)});
            
            this.scanOverCodeTo(SYM_semicolon);
            this.ensureAndConsumeTokenIf(SYM_semicolon, "type alias");
        }
        else {
            const terms = this.parseTypeTemplateTerms();
            this.ensureAndConsumeTokenIf(SYM_eq, "type alias");

            const btype = this.parseTypeSignature();

            const nndl = this.env.currentNamespace.typeDefs.find((td) => td.name === tyname);
            if(nndl !== undefined) {
                nndl.terms = terms;
                nndl.boundType = btype;
            }

            this.ensureAndConsumeTokenIf(SYM_semicolon, "type alias");
        }
    }

    private parseNamespaceConstant(attributes: DeclarationAttibute[]) {
        const sinfo = this.peekToken().getSourceInfo();
        this.ensureAndConsumeTokenAlways(KW_const, "const member");

        this.ensureToken(TokenStrings.IdentifierName, "const member");
        const sname = this.parseIdentifierAsStdVariable();

        if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterNames)) {
            if(this.env.currentNamespace.checkDeclNameClashMember(sname)) {
                this.recordErrorGeneral(sinfo, `Collision between const and other names -- ${sname}`);
            }

            this.env.currentNamespace.declaredNames.add(sname);
            this.env.currentNamespace.declaredMemberNames.add(sname);

            this.scanOverCodeTo(SYM_semicolon);
            this.ensureAndConsumeTokenIf(SYM_semicolon, "const member");
        }
        else {
            this.ensureAndConsumeTokenIf(SYM_colon, "const member");
            const stype = this.parseTypeSignature();

            this.ensureAndConsumeTokenIf(SYM_eq, "const member");
            const value = this.parseConstExpression(stype);
            if(value.captured.size !== 0) {
                this.recordErrorGeneral(sinfo, "Cannot have captured variables in const member");
            }

            this.env.currentNamespace.consts.push(new ConstMemberDecl(this.env.currentFile, sinfo, attributes, sname, stype, value));

            this.ensureAndConsumeTokenIf(SYM_semicolon, "const member");
        }
    }

    private parseNamespaceFunction(attributes: DeclarationAttibute[], endtok: string) {
        const sinfo = this.peekToken().getSourceInfo();

        if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterNames)) {
            this.consumeTokenIf(KW_recursive);
            this.consumeTokenIf(KW_recursive_q);
            this.consumeToken();

            const fname = this.consumeTokenAndGetValue();
            if(this.env.currentNamespace.checkDeclNameClashMember(fname)) {
                this.recordErrorGeneral(sinfo, `Collision between function and other names -- ${fname}`);
            }

            this.env.currentNamespace.declaredNames.add(fname);
            this.env.currentNamespace.declaredMemberNames.add(fname);

            this.namespaceParseScanCover(endtok);
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
        assert(isParsePhase_Enabled(this.currentPhase, ParsePhase_CompleteParsing));

        let provides: TypeSignature[] = [];
        if (this.testAndConsumeTokenIf(KW_provides)) {
            while (!endtoken.some((tok) => this.testToken(tok))) {
                this.consumeTokenIf(SYM_coma);
                provides.push(this.parseTypeSignature());
            }
        }
        
        if (this.env.currentNamespace.fullnamespace.ns[0] !== "Core") {
            const corens = this.env.assembly.getCoreNamespace();
            const otype = corens.typedecls.find((td) => td.name === "Object") as AbstractNominalTypeDecl;

            provides.push(new NominalTypeSignature(sinfo, ["Core"], [{tname: "Object", terms: []}], undefined, otype));
        }

        return provides;
    }

    private parseConstMember(constMembers: ConstMemberDecl[] | undefined, allMemberNames: Set<string>, attributes: DeclarationAttibute[]) {
        assert(isParsePhase_Enabled(this.currentPhase, ParsePhase_CompleteParsing));

        const sinfo = this.peekToken().getSourceInfo();
        this.ensureAndConsumeTokenAlways(KW_const, "const member");

        this.ensureToken(TokenStrings.IdentifierName, "const member");
        const sname = this.parseIdentifierAsStdVariable();

        this.ensureAndConsumeTokenIf(SYM_colon, "const member");
        const stype = this.parseTypeSignature();

        this.ensureAndConsumeTokenIf(SYM_eq, "const member");
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

        this.ensureAndConsumeTokenIf(SYM_semicolon, "const member");
    }

    private parseMemberFunction(memberFunctions: TypeFunctionDecl[] | undefined, allMemberNames: Set<string>, attributes: DeclarationAttibute[], typeTerms: Set<string>) {
        assert(isParsePhase_Enabled(this.currentPhase, ParsePhase_CompleteParsing));

        const sinfo = this.peekToken().getSourceInfo();
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
        assert(isParsePhase_Enabled(this.currentPhase, ParsePhase_CompleteParsing));

        const sinfo = this.peekToken().getSourceInfo();
        this.ensureAndConsumeTokenAlways(KW_field, "member field");

        this.ensureToken(TokenStrings.IdentifierName, "member field");
        const fname = this.parseIdentifierAsStdVariable();

        this.ensureAndConsumeTokenIf(SYM_colon, "member field");
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

        this.ensureAndConsumeTokenIf(SYM_semicolon, "member field");
    }

    private parseMemberMethod(memberMethods: MethodDecl[] | undefined, allMemberNames: Set<string>, attributes: DeclarationAttibute[], typeTerms: Set<string>) {
        assert(isParsePhase_Enabled(this.currentPhase, ParsePhase_CompleteParsing));

        const sinfo = this.peekToken().getSourceInfo();
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
        assert(isParsePhase_Enabled(this.currentPhase, ParsePhase_CompleteParsing));

        const sinfo = this.peekToken().getSourceInfo();
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

    private parseTaskMemberAction(taskMemberAction: TaskActionDecl[] | undefined, allMemberNames: Set<string>, attributes: DeclarationAttibute[], typeTerms: Set<string>, taskmain: string) {
        assert(isParsePhase_Enabled(this.currentPhase, ParsePhase_CompleteParsing));

        const sinfo = this.peekToken().getSourceInfo();
        const adecl = this.parseActionInvokeDecl(attributes, typeTerms, taskmain);

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
        assert(isParsePhase_Enabled(this.currentPhase, ParsePhase_CompleteParsing));
        const sinfo = this.peekToken().getSourceInfo();

        this.env.pushStandardFunctionScope([], typeTerms, this.wellknownTypes.get("Bool") as TypeSignature);
        while (this.testToken(KW_invariant) || this.testToken(KW_validate)) {
            const isvalidate = this.testToken(KW_validate);
            this.consumeToken();

            let tag: string | undefined = undefined;
            if(this.testAndConsumeTokenIf(SYM_lbrack)) {
                if(this.ensureToken(TokenStrings.ExString, "invariant/validate tag")) {
                    tag = this.consumeTokenAndGetValue();
                }
            
                this.ensureAndConsumeTokenAlways(SYM_rbrack, "invariant/validate tag");
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

            this.ensureAndConsumeTokenIf(SYM_semicolon, "invariant");
        }
        this.env.popStandardFunctionScope();
    }

    private parseOOPMembersCommonAll(istask: boolean, specialConcept: InternalConceptTypeDecl | undefined, typeTerms: Set<string>,
        invariants: InvariantDecl[] | undefined, validates: ValidateDecl[] | undefined,
        constMembers: ConstMemberDecl[] | undefined, functionMembers: TypeFunctionDecl[] | undefined, 
        memberFields: MemberFieldDecl[] | undefined, memberMethods: MethodDecl[] | undefined, 
        taskMemberMethods: TaskMethodDecl[] | undefined, taskMemberAction: TaskActionDecl[] | undefined, 
        taskmain: string | undefined) {
        let allMemberNames = new Set<string>();

        this.prepStateStackForNested("type", undefined);
        this.ensureAndConsumeTokenAlways(SYM_lbrace, "type members");

        while (!this.testToken(SYM_rbrace) && !this.testToken(TokenStrings.EndOfStream) && !this.testToken(TokenStrings.Recover)) {
            let attributes: DeclarationAttibute[] = [];
            while(this.testToken(TokenStrings.Attribute) || this.testToken(TokenStrings.DocComment)) {
                const attr = this.parseAttribute();
                attributes.push(attr);
            }

            this.prepStateStackForNested("type-member", undefined);

            const sinfo = this.peekToken().getSourceInfo();
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
            else if(this.testToken(KW_method) || this.testFollows(KW_recursive, KW_method) || this.testFollows(KW_recursive_q, KW_method)) {
                if(istask) {
                    this.parseTaskMemberMethod(taskMemberMethods, allMemberNames, attributes, typeTerms);
                }
                else {
                    this.parseMemberMethod(memberMethods, allMemberNames, attributes, typeTerms);
                }
            }
            else if(this.testToken(KW_action)) {
                this.parseTaskMemberAction(taskMemberAction, allMemberNames, attributes, typeTerms, taskmain as string);
            }
            else if(this.testToken(KW_entity)) {
                if(specialConcept === undefined) {
                    this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Cannot have nested entities on this type");

                    //scan to the next declaration or end brace
                    this.consumeToken();
                    const rpos = this.scanToSyncPos(SYM_rbrace, ...TYPE_DECL_FIRSTS);
                    if(rpos === undefined) {
                        this.currentState().moveToRecoverPosition();
                        return; 
                    }
                    else {
                        this.currentState().skipToPosition(rpos);
                    }
                }
                else {
                    this.parseNestedEntity(specialConcept, allMemberNames, attributes);
                }
            }
            else {
                this.recordErrorGeneral(sinfo, `Unknown member ${this.peekTokenData()}`);

                //scan to the next declaration or end brace
                this.consumeToken();
                const rpos = this.scanToSyncPos(SYM_rbrace, ...TYPE_DECL_FIRSTS);
                if(rpos === undefined) {
                    this.currentState().moveToRecoverPosition();
                    return; 
                }
                else {
                    this.currentState().skipToPosition(rpos);
                }
            }

            this.popStateIntoParentOk();
        }

        this.popStateIntoParentOk();
        this.ensureAndConsumeTokenIf(SYM_rbrace, "type members");
    }

    private parseNestedEntity(specialConcept: InternalConceptTypeDecl, allMemberNames: Set<string>, attributes: DeclarationAttibute[]) {
        //special Concept should be Result or APIResult and this should be one of the known subtypes

        //need to set the template terms here from parent as well!!!

        assert(false, "Not implemented");
    }

    private parseEntityRegisterType(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, etag: AdditionalTypeDeclTag) {
        let tdecl: AbstractNominalTypeDecl | undefined = undefined;

        if(PRIMITIVE_ENTITY_TYPE_NAMES.includes(name)) {
            tdecl = new PrimitiveEntityTypeDecl(this.env.currentFile, sinfo, attributes, name);
        }
        else if(name === "StringOf") {
            tdecl = new StringOfTypeDecl(this.env.currentFile, sinfo, attributes, "StringOf");
        }
        else if(name === "ExStringOf") {
            tdecl = new ExStringOfTypeDecl(this.env.currentFile, sinfo, attributes, "ExStringOf");
        }
        else if(name === "Something") {
            tdecl = new SomethingTypeDecl(this.env.currentFile, sinfo, attributes, "Something");
        }
        else if(name === "List") {
            tdecl = new ListTypeDecl(this.env.currentFile, sinfo, attributes, "List");
        }
        else if(name === "Stack") {
            tdecl = new StackTypeDecl(this.env.currentFile, sinfo, attributes, "Stack");
        }
        else if(name === "Queue") {
            tdecl = new QueueTypeDecl(this.env.currentFile, sinfo, attributes, "Queue");
        }
        else if(name === "Set") {
            tdecl = new SetTypeDecl(this.env.currentFile, sinfo, attributes, "Set");
        }
        else if(name === "MapEntry") {
            tdecl = new MapEntryTypeDecl(this.env.currentFile, sinfo, attributes, "MapEntry");
        }
        else if(name === "Map") {
            tdecl = new MapTypeDecl(this.env.currentFile, sinfo, attributes, "Map");
        }
        else if(name === "EventList") {
            tdecl = new EventListTypeDecl(this.env.currentFile, sinfo, attributes, "EventList");
        }
        else {
            assert(!attributes.some((attr) => attr.name === "__internal"), "Missing special case on primitive entity parse");

            tdecl = new EntityTypeDecl(this.env.currentFile, sinfo, attributes, name, etag);
        }

        assert(tdecl !== undefined, "Failed to register entity type");
        this.env.currentNamespace.typedecls.push(tdecl);
    }

    private parseEntityCompleteParse(sinfo: SourceInfo, name: string) {
        const tdecl = this.env.currentNamespace.typedecls.find((td) => td.name === name);
        assert(tdecl !== undefined, "Failed to find entity type");

        const terms = this.parseTypeTemplateTerms();
        if(terms.length !== 0) {
            tdecl.terms.push(...terms);
        }

        const provides = this.parseProvides(sinfo, [SYM_lbrace]);
        if(provides.length !== 0) {
            tdecl.provides.push(...provides);
        }

        if(tdecl instanceof PrimitiveEntityTypeDecl) {
            this.parseOOPMembersCommonAll(false, undefined, new Set<string>(), undefined, undefined, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined, undefined);
        }
        else if(tdecl instanceof StringOfTypeDecl) {
            this.parseOOPMembersCommonAll(false, undefined, new Set<string>("T"), undefined, undefined, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined, undefined);
        }
        else if(tdecl instanceof ExStringOfTypeDecl) {
            this.parseOOPMembersCommonAll(false, undefined, new Set<string>("T"), undefined, undefined, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined, undefined);
        }
        else if(tdecl instanceof ListTypeDecl || tdecl instanceof StackTypeDecl || tdecl instanceof QueueTypeDecl || tdecl instanceof SetTypeDecl) {
            this.parseOOPMembersCommonAll(false, undefined, new Set<string>("T"), undefined, undefined, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined, undefined);
        }
        else if(tdecl instanceof MapEntryTypeDecl) {
            this.parseTypeTemplateTerms();
            this.parseOOPMembersCommonAll(false, undefined, new Set<string>(["K", "V"]), undefined, undefined, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined, undefined);
        }
        else if(tdecl instanceof MapTypeDecl) {
            this.parseTypeTemplateTerms();
            this.parseOOPMembersCommonAll(false, undefined, new Set<string>(["K", "V"]), undefined, undefined, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined, undefined);
        }
        else if(tdecl instanceof EventListTypeDecl) {
            this.parseOOPMembersCommonAll(false, undefined, new Set<string>("T"), undefined, undefined, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined, undefined);
        }
        else {
            const edecl = tdecl as EntityTypeDecl;
            this.parseOOPMembersCommonAll(false, undefined, new Set<string>(edecl.terms.map((term) => term.name)), edecl.invariants, edecl.validates, edecl.consts, edecl.functions, edecl.fields, edecl.methods, undefined, undefined, undefined);
        }
    }

    private parseEntity(attributes: DeclarationAttibute[], endtok: string) {
        const sinfo = this.peekToken().getSourceInfo();

        const etag: AdditionalTypeDeclTag = this.parseAdditionalTypeDeclTag();
        this.ensureAndConsumeTokenAlways(KW_entity, "entity declaration");
        this.ensureToken(TokenStrings.IdentifierName, "entity declaration");
        const ename = this.parseIdentifierAsNamespaceOrTypeName();

        if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterNames)) {
            const hasterms = this.testToken(SYM_langle);

            if(this.env.currentNamespace.checkDeclNameClashType(ename, hasterms)) {
                this.recordErrorGeneral(sinfo, `Collision between type and other names -- ${ename}`);
            }

            this.parseEntityRegisterType(sinfo, attributes, ename, etag);

            this.env.currentNamespace.declaredNames.add(ename);
            this.env.currentNamespace.declaredTypeNames.push({name: ename, hasterms: hasterms});

            this.namespaceParseScanCover(endtok);
        }
        else {
            this.parseEntityCompleteParse(sinfo, ename);
        }
    }

    private parseConceptRegisterType(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, etag: AdditionalTypeDeclTag) {
        let tdecl: AbstractNominalTypeDecl | undefined = undefined;

        if(PRIMITIVE_CONCEPT_TYPE_NAMES.includes(name)) {
            tdecl = new PrimitiveConceptTypeDecl(this.env.currentFile, sinfo, attributes, name);
        }
        else if(name === "Option") {
            tdecl = new OptionTypeDecl(this.env.currentFile, sinfo, attributes, "Option");
        }
        else if(name === "Expandoable") {
            tdecl = new ExpandoableTypeDecl(this.env.currentFile, sinfo, attributes, "Expandoable");
        }
        else {
            assert(!attributes.some((attr) => attr.name === "__internal"), "Missing special case on primitive concept parse");

            tdecl = new ConceptTypeDecl(this.env.currentFile, sinfo, attributes, name, etag);
        }

        assert(tdecl !== undefined, "Failed to register entity type");
        this.env.currentNamespace.typedecls.push(tdecl);
    }

    private parseConceptCompleteParse(sinfo: SourceInfo, name: string) {
        const tdecl = this.env.currentNamespace.typedecls.find((td) => td.name === name);
        assert(tdecl !== undefined, "Failed to find entity type");

        const terms = this.parseTypeTemplateTerms();
        if(terms.length !== 0) {
            tdecl.terms.push(...terms);
        }

        const provides = this.parseProvides(sinfo, [SYM_lbrace]);
        if(provides.length !== 0) {
            tdecl.provides.push(...provides);
        }

        if(tdecl instanceof PrimitiveConceptTypeDecl) {
            this.parseOOPMembersCommonAll(false, undefined, new Set<string>(), undefined, undefined, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined, undefined);
        }
        else if(tdecl instanceof ExpandoableTypeDecl) {
            this.parseOOPMembersCommonAll(false, undefined, new Set<string>("T"), undefined, undefined, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined, undefined);
        }
        else {
            const cdecl = tdecl as ConceptTypeDecl;
            this.parseOOPMembersCommonAll(false, undefined, new Set<string>(cdecl.terms.map((term) => term.name)), cdecl.invariants, cdecl.validates, cdecl.consts, cdecl.functions, cdecl.fields, cdecl.methods, undefined, undefined, undefined);
        }
    }

    private parseConcept(attributes: DeclarationAttibute[], endtok: string) {
        const sinfo = this.peekToken().getSourceInfo();

        const etag: AdditionalTypeDeclTag = this.parseAdditionalTypeDeclTag();
        this.ensureAndConsumeTokenAlways(KW_concept, "concept declaration");
        this.ensureToken(TokenStrings.IdentifierName, "concept declaration");
        const ename = this.parseIdentifierAsNamespaceOrTypeName();

        if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterNames)) {
            const hasterms = this.testToken(SYM_langle);

            if(this.env.currentNamespace.checkDeclNameClashType(ename, hasterms)) {
                this.recordErrorGeneral(sinfo, `Collision between type and other names -- ${ename}`);
            }

            this.parseConceptRegisterType(sinfo, attributes, ename, etag);

            this.env.currentNamespace.declaredNames.add(ename);
            this.env.currentNamespace.declaredTypeNames.push({name: ename, hasterms: hasterms});

            this.namespaceParseScanCover(endtok);
        }
        else {
            this.parseConceptCompleteParse(sinfo, ename);
        }
    }
    
    private parseEnum(attributes: DeclarationAttibute[], endtok: string) {
        const sinfo = this.peekToken().getSourceInfo();

        const etag: AdditionalTypeDeclTag = this.parseAdditionalTypeDeclTag();
        this.ensureAndConsumeTokenAlways(KW_enum, "enum declaration");
        this.ensureToken(TokenStrings.IdentifierName, "enum declaration");
        const ename = this.parseIdentifierAsNamespaceOrTypeName();

        if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterNames)) {
            if(this.env.currentNamespace.checkDeclNameClashType(ename, false)) {
                this.recordErrorGeneral(sinfo, `Collision between enum and other names -- ${ename}`);
            }

            const members = this.parseListOf<string>(SYM_lbrace, SYM_rbrace, SYM_coma, "enum members", () => {
                this.ensureToken(TokenStrings.IdentifierName, "enum member");
                return this.parseIdentifierAsEnumMember();
            });

            const enumtype = new EnumTypeDecl(this.env.currentFile, sinfo, attributes, ename, members, etag);
            this.env.currentNamespace.typedecls.push(enumtype);

            this.env.currentNamespace.declaredNames.add(ename);
            this.env.currentNamespace.declaredTypeNames.push({name: ename, hasterms: false});
        }
        else {
            const tdecl = this.env.currentNamespace.typedecls.find((td) => td.name === ename);
            assert(tdecl !== undefined, "Failed to find entity type");

            tdecl.provides.push(this.wellknownTypes.get("Some") as TypeSignature);

            this.namespaceParseScanCover(endtok);
        }
    }

    private parseValidatorTypedecl(attributes: DeclarationAttibute[], endtok: string) {
        const sinfo = this.peekToken().getSourceInfo();

        this.ensureAndConsumeTokenAlways(KW_validator, "validator declaration");
        this.ensureToken(TokenStrings.IdentifierName, "validator declaration");
        const iname = this.parseIdentifierAsNamespaceOrTypeName();

        if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterNames)) {
            if(this.env.currentNamespace.checkDeclNameClashType(iname, false)) {
                this.recordErrorGeneral(sinfo, `Collision between validator decl and other names -- ${iname}`);
            }

            this.ensureAndConsumeTokenIf(SYM_eq, "validator declaration");
            if(this.testToken(TokenStrings.Regex)) {
                const vregex = this.consumeTokenAndGetValue();

                if(vregex.endsWith("/")) {
                    const vdecl = new RegexValidatorTypeDecl(this.env.currentFile, sinfo, attributes, iname, vregex);
                    this.env.currentNamespace.typedecls.push(vdecl);
                }
                else {
                    const vdecl = new ExRegexValidatorTypeDecl(this.env.currentFile, sinfo, attributes, iname, vregex);
                    this.env.currentNamespace.typedecls.push(vdecl);
                }

                assert(false, "TODO: we need to validate the regex parse too!!!");
            }
            else if(this.testToken(TokenStrings.PathItem)) {
                const pthglb = this.consumeTokenAndGetValue();

                if(!pthglb.startsWith("g")) {
                    this.recordErrorGeneral(sinfo, "Path glob must start with end with a 'g'");
                }

                const vdecl = new PathValidatorTypeDecl(this.env.currentFile, sinfo, attributes, iname, pthglb);
                this.env.currentNamespace.typedecls.push(vdecl);

                assert(false, "TODO: we need to validate the path glob parse too!!!");
            }
            else {
                this.recordErrorGeneral(sinfo, "Invalid validator declaration");
                this.namespaceParseScanCover(endtok);
            }

            this.env.currentNamespace.declaredNames.add(iname);
            this.env.currentNamespace.declaredTypeNames.push({name: iname, hasterms: false});

            this.ensureAndConsumeTokenIf(SYM_semicolon, "validator declaration");
        }
        else {
            const tdecl = this.env.currentNamespace.typedecls.find((td) => td.name === iname);
            assert(tdecl !== undefined, "Failed to find entity type");

            tdecl.provides.push(this.wellknownTypes.get("Some") as TypeSignature);

            this.namespaceParseScanCover(endtok);
        }
    }

    private parseTypeDecl(attributes: DeclarationAttibute[], endtok: string) {
        const sinfo = this.peekToken().getSourceInfo();

        const etag: AdditionalTypeDeclTag = this.parseAdditionalTypeDeclTag();
        this.ensureAndConsumeTokenAlways(KW_typedecl, "typedecl declaration");
        this.ensureToken(TokenStrings.IdentifierName, "typedecl declaration");
        const iname = this.parseIdentifierAsNamespaceOrTypeName();

        if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterNames)) {
            if(this.env.currentNamespace.checkDeclNameClashType(iname, false)) {
                this.recordErrorGeneral(sinfo, `Collision between type and other names -- ${iname}`);
            }

            const tdecl = new TypedeclTypeDecl(this.env.currentFile, sinfo, attributes, iname, etag, new ErrorTypeSignature(sinfo, undefined));
            this.env.currentNamespace.typedecls.push(tdecl);

            this.env.currentNamespace.declaredNames.add(iname);
            this.env.currentNamespace.declaredTypeNames.push({name: iname, hasterms: this.testToken(SYM_langle)});

            this.ensureAndConsumeTokenIf(SYM_semicolon, "typedecl declaration");
        }
        else {
            const tdecl = this.env.currentNamespace.typedecls.find((td) => td.name === iname);
            assert(tdecl !== undefined && !(tdecl instanceof TypedeclTypeDecl), "Failed to find typedecl type");

            const terms = this.parseTypeTemplateTerms();
            if(terms.length !== 0) {
                tdecl.terms.push(...terms);
            }

            this.ensureAndConsumeTokenIf(SYM_eq, "typedecl declaration");
            const ttype = this.parseTypeSignature();
            (tdecl as TypedeclTypeDecl).valuetype = ttype;

            if(this.testAndConsumeTokenIf(SYM_semicolon)) {
                tdecl.provides.push(this.wellknownTypes.get("Some") as TypeSignature);
            }
            else {
                this.ensureAndConsumeTokenIf(SYM_amp, "typedecl declaration");

               const provides = this.parseProvides(sinfo, [SYM_lbrace]);
                if(provides.length !== 0) {
                    tdecl.provides.push(...provides);
                }

                this.parseOOPMembersCommonAll(false, undefined, new Set<string>(terms.map((tt) => tt.name)), tdecl.invariants, tdecl.validates, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined, undefined);
            }
        }
    }

    private parseDatatypeMemberEntityTypeDecl(attributes: DeclarationAttibute[], parenttype: DatatypeTypeDecl, hasterms: boolean, etag: AdditionalTypeDeclTag) {
        const sinfo = this.peekToken().getSourceInfo();

        this.consumeTokenIf(SYM_bar);

        this.ensureToken(TokenStrings.IdentifierName, "datatype member entity declaration");
        const ename = this.parseIdentifierAsNamespaceOrTypeName();

        if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterNames)) {
            if(this.env.currentNamespace.checkDeclNameClashType(ename, false)) {
                this.recordErrorGeneral(sinfo, `Collision between type and other names -- ${ename}`);
            }

            const tdecl = new DatatypeMemberEntityTypeDecl(this.env.currentFile, sinfo, attributes, ename, etag, parenttype);
            
            parenttype.associatedMemberEntityDecls.push(tdecl);
            this.env.currentNamespace.typedecls.push(tdecl);

            this.env.currentNamespace.declaredNames.add(ename);
            this.env.currentNamespace.declaredTypeNames.push({name: ename, hasterms: hasterms});

            this.scanOverCodeParenSet(SYM_lbrace, SYM_rbrace);
        }
        else {
            const tdecl = this.env.currentNamespace.typedecls.find((td) => td.name === ename);
            assert(tdecl !== undefined && !(tdecl instanceof DatatypeMemberEntityTypeDecl), "Failed to find typedecl type");

            if(parenttype.terms.length !== 0) {
                tdecl.terms.push(...parenttype.terms);
            }

            if(this.testFollows(SYM_lbrace, TokenStrings.IdentifierName, SYM_colon)) {
                const fields = this.parseListOf<MemberFieldDecl>("datatype member entity", SYM_lbrace, SYM_rbrace, SYM_coma, () => {
                    const mfinfo = this.peekToken().getSourceInfo();

                    this.ensureToken(TokenStrings.IdentifierName, "datatype POD member field");
                    const name = this.parseIdentifierAsStdVariable();
                    this.ensureAndConsumeTokenIf(SYM_colon, "datatype POD member field");

                    const ttype = this.parseTypeSignature();
                    return new MemberFieldDecl(this.env.currentFile, mfinfo, [], name, ttype, undefined);
                });

                (tdecl as DatatypeMemberEntityTypeDecl).fields.push(...fields);
            }
            else {
                this.parseOOPMembersCommonAll(false, undefined, new Set<string>(parenttype.terms.map((term) => term.name)), tdecl.invariants, tdecl.validates, tdecl.consts, tdecl.functions, (tdecl as DatatypeMemberEntityTypeDecl).fields, tdecl.methods, undefined, undefined, undefined);
            }
        }
    }

    private parseDataTypeDecl(attributes: DeclarationAttibute[]) {
        const sinfo = this.peekToken().getSourceInfo();

        const etag: AdditionalTypeDeclTag = this.parseAdditionalTypeDeclTag();
        this.ensureAndConsumeTokenAlways(KW_datatype, "datatype declaration");
        this.ensureToken(TokenStrings.IdentifierName, "datatype declaration");
        const dname = this.parseIdentifierAsNamespaceOrTypeName();

        let tdecl: DatatypeTypeDecl;
        let hasTerms = this.testToken(SYM_langle);
        if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterNames)) {
            if(this.env.currentNamespace.checkDeclNameClashType(dname, false)) {
                this.recordErrorGeneral(sinfo, `Collision between type and other names -- ${dname}`);
            }

            tdecl = new DatatypeTypeDecl(this.env.currentFile, sinfo, attributes, dname, etag);
            this.env.currentNamespace.typedecls.push(tdecl);

            this.env.currentNamespace.declaredNames.add(dname);
            this.env.currentNamespace.declaredTypeNames.push({name: dname, hasterms: hasTerms});

            this.scanOverCodeTo(KW_of, SYM_amp, SYM_semicolon);
        }
        else {
            const ddecl = this.env.currentNamespace.typedecls.find((td) => td.name === dname);
            assert(ddecl !== undefined && !(ddecl instanceof DatatypeTypeDecl), "Failed to find typedecl type");

            tdecl = ddecl as DatatypeTypeDecl;

            const terms = this.parseTypeTemplateTerms();
            if(terms.length !== 0) {
                tdecl.terms.push(...terms);
            }

            const provides = this.parseProvides(sinfo, [SYM_lbrace]);
            if(provides.length !== 0) {
                tdecl.provides.push(...provides);
            }

            if(this.testAndConsumeTokenIf(KW_using)) {
                const cusing = this.parseListOf<MemberFieldDecl>("datatype", SYM_lbrace, SYM_rbrace, SYM_coma, () => {
                    const sinfo = this.peekToken().getSourceInfo();

                    this.ensureToken(TokenStrings.IdentifierName, "datatype field");
                    const name = this.parseIdentifierAsStdVariable();
                    this.ensureAndConsumeTokenIf(SYM_colon, "datatype field");

                    const ttype = this.parseTypeSignature();
                    return new MemberFieldDecl(this.env.currentFile, sinfo, [], name, ttype, undefined);
                });

                tdecl.fields.push(...cusing);
            }
        }

        this.ensureAndConsumeTokenIf(KW_of, "datatype");

        while (!this.testToken(SYM_semicolon) && !this.testToken(SYM_amp)) {
            this.parseDatatypeMemberEntityTypeDecl(attributes, tdecl, hasTerms, etag);
        }

        if(this.testAndConsumeTokenIf(SYM_amp)) {
            if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterNames)) {
                this.scanMatchingParens(SYM_lbrace, SYM_rbrace);
            }
            else {
                if(tdecl.fields.length !== 0) {
                    this.recordErrorGeneral(sinfo, "Cannot mix POD (using) declartion with full datatype (&) declaration");
                }
                this.parseOOPMembersCommonAll(false, undefined, new Set<string>(tdecl.terms.map((tt) => tt.name)), tdecl.invariants, tdecl.validates, tdecl.consts, tdecl.functions, tdecl.fields, tdecl.methods, undefined, undefined, undefined);
            }
        }

        this.testAndConsumeTokenIf(SYM_semicolon);
    }

    private parseTask(attributes: DeclarationAttibute[], endtok: string) {
        const sinfo = this.peekToken().getSourceInfo();

        this.ensureAndConsumeTokenAlways(KW_task, "task declaration");
        this.ensureToken(TokenStrings.IdentifierName, "task declaration");
        const tname = this.parseIdentifierAsNamespaceOrTypeName();

        if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterNames)) {
            const hasterms = this.testToken(SYM_langle);

            if(this.env.currentNamespace.checkDeclNameClashType(tname, hasterms)) {
                this.recordErrorGeneral(sinfo, `Collision between type and other names -- ${tname}`);
            }

            const tdecl = new TaskDecl(this.env.currentFile, sinfo, attributes, tname);
            this.env.currentNamespace.typedecls.push(tdecl);

            this.env.currentNamespace.declaredNames.add(tname);
            this.env.currentNamespace.declaredTypeNames.push({name: tname, hasterms: hasterms});

            this.namespaceParseScanCover(endtok);
        }
        else {
            const tdecl = this.env.currentNamespace.typedecls.find((td) => td.name === tname);
            assert(tdecl !== undefined && tdecl instanceof TaskDecl, "Failed to find task type");

            const terms = this.parseTypeTemplateTerms();
            if(terms.length !== 0) {
                tdecl.terms.push(...terms);
            }

            const provides = this.parseProvides(sinfo, [SYM_lbrace]);
            if(provides.length !== 0) {
                this.recordErrorGeneral(sinfo, "Cannot have provides on tasks");
            }

            let taskmain: string = "main";
            if(this.testAndConsumeTokenIf(KW_implements)) {
                const iiaccess = this.parseIdentifierAccessChain();
                if(iiaccess === undefined) {
                    this.recordErrorGeneral(sinfo, "Invalid expression -- could not resolve name");
                    
                    //something went very wrong
                    this.namespaceParseScanCover(endtok);
                    return;
                }

                if(iiaccess.typeTokens.length !== 0) {
                    this.recordErrorGeneral(sinfo, "Invalid API name");
                }
                else {
                    this.ensureAndConsumeTokenAlways(SYM_coloncolon, "task declaration provides");
                    const ok = this.ensureToken(TokenStrings.IdentifierName, "task declaration provides");

                    if(ok) {
                        const pn = this.parseIdentifierAsStdVariable();

                        taskmain = pn;
                        tdecl.implementsapi = [iiaccess.nsScope.fullnamespace, pn];
                    }
                }
            }

            while(this.testToken(KW_event) || this.testToken(KW_status) || this.testToken(KW_resource) || this.testToken(KW_env)) {
                if(this.testToken(KW_event)) {
                    if(tdecl.eventsInfo !== undefined) {
                        this.recordErrorGeneral(sinfo, "Cannot have multiple event sections");
                    }

                    this.consumeToken();
                    if(this.testFollows(SYM_lbrace, SYM_rbrace)) {
                        this.consumeToken();
                        this.consumeToken();
                        tdecl.eventsInfo = "{}";
                    }
                    else if(this.testFollows(SYM_lbrace, SYM_question, SYM_rbrace)) {
                        this.consumeToken();
                        tdecl.eventsInfo = this.consumeTokenAndGetValue() as "?";
                        this.consumeToken();
                    }
                    else {
                        tdecl.eventsInfo = this.parseListOf<TypeSignature>("task event section", SYM_lbrace, SYM_rbrace, SYM_coma, () => this.parseTypeSignature());
                    }
                }
                else if(this.testToken(KW_status)) {
                    if(tdecl.statusInfo !== undefined) {
                        this.recordErrorGeneral(sinfo, "Cannot have multiple status sections");
                    }

                    this.consumeToken();
                    if(this.testFollows(SYM_lbrace, SYM_question, SYM_rbrace)) {
                        this.consumeToken();
                        tdecl.statusInfo = this.consumeTokenAndGetValue() as "?";
                        this.consumeToken();
                    }
                    else {
                        const ttl = this.parseListOf<TypeSignature>("task status section", SYM_lbrack, SYM_rbrack, SYM_coma, () => this.parseTypeSignature());
                        if(ttl.length > 2) {
                            this.recordErrorGeneral(sinfo, "Invalid status section");
                        }

                        tdecl.statusInfo = new StatusInfoFilter(ttl[0], ttl[1]); //implicit undefined is fine here
                    }
                }
                else if(this.testToken(KW_resource)) {
                    if(tdecl.resourceImpactInfo !== undefined) {
                        this.recordErrorGeneral(sinfo, "Cannot have multiple resource sections");
                    }

                    this.consumeToken();
                    if(this.testFollows(SYM_lbrace, SYM_rbrace)) {
                        this.consumeToken();
                        this.consumeToken();
                        tdecl.resourceImpactInfo = "{}";
                    }
                    else if(this.testFollows(SYM_lbrace, SYM_wildcard, SYM_rbrace)) {
                        this.consumeToken();
                        tdecl.resourceImpactInfo = this.consumeTokenAndGetValue() as "**";
                        this.consumeToken();
                    }
                    else if(this.testFollows(SYM_lbrace, SYM_question, SYM_lbrace)) {
                        this.consumeToken();
                        tdecl.resourceImpactInfo = this.consumeTokenAndGetValue() as "?";
                        this.consumeToken();
                    }
                    else {
                        tdecl.resourceImpactInfo = this.parseListOf<ResourceInformation>("task resource section", SYM_lbrace, SYM_rbrace, SYM_coma, () => {
                            const pp = this.parseConstResourceExpression();
                            this.ensureAndConsumeTokenIf(SYM_at, "task resource section");

                            const mod = this.ensureToken(TokenStrings.ResourceUseMod, "task resource section") ? this.consumeTokenAndGetValue() : "[*]";
                            const oops = mod.includes("*") ? "*" : mod.slice(1, -1).split("");

                            return new ResourceInformation(pp, oops as ResourceAccessModes[]);
                        });
                    }
                }
                else {
                    if(tdecl.envVarRequirementInfo !== undefined) {
                        this.recordErrorGeneral(sinfo, "Cannot have multiple env sections");
                    }

                    this.consumeToken();
                    if(this.testFollows(SYM_lbrace, SYM_question, SYM_rbrace)) {
                        this.consumeToken();
                        tdecl.envVarRequirementInfo = this.consumeTokenAndGetValue() as "?";
                        this.consumeToken();
                    }
                    else {
                        tdecl.envVarRequirementInfo = this.parseListOf<EnvironmentVariableInformation>("task env section", SYM_lbrace, SYM_rbrace, SYM_coma, () => {
                            this.ensureToken(TokenStrings.ExString, "task env section");
                            const ename = this.consumeTokenAndGetValue();

                            this.ensureAndConsumeTokenIf(SYM_colon, "task env section");
                            const ttype = this.parseTypeSignature();
                        
                            let exp: ConstantExpressionValue | undefined = undefined;
                            if(this.testAndConsumeTokenIf(SYM_eq)) {
                                exp = this.parseConstExpression(ttype);
                            }

                            return new EnvironmentVariableInformation(ename, ttype, exp);
                        });
                    }
                }
            }

            if(tdecl.eventsInfo === undefined) {
                tdecl.eventsInfo = "{}";
            }
            if(tdecl.statusInfo === undefined) {
                tdecl.statusInfo = new StatusInfoFilter(undefined, undefined);
            }
            if(tdecl.envVarRequirementInfo === undefined) {
                tdecl.envVarRequirementInfo = [];
            }
            if(tdecl.resourceImpactInfo === undefined) {
                tdecl.resourceImpactInfo = "{}";
            }

            this.parseOOPMembersCommonAll(true, undefined, new Set<string>(tdecl.terms.map((term) => term.name)), tdecl.invariants, tdecl.validates, tdecl.consts, tdecl.functions, tdecl.fields, undefined, tdecl.selfmethods, tdecl.actions, taskmain);
        }
    }

    private parseAPI(attributes: DeclarationAttibute[]) {
        const sinfo = this.peekToken().getSourceInfo();

        this.ensureAndConsumeTokenAlways(KW_api, "api declaration");
        this.ensureToken(TokenStrings.IdentifierName, "api declaration");
        const apiname = this.parseIdentifierAsStdVariable();

        if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterNames)) {
            if(this.env.currentNamespace.checkDeclNameClashMember(apiname)) {
                this.recordErrorGeneral(sinfo, `Collision between API and other names -- ${apiname}`);
            }

            this.env.currentNamespace.declaredNames.add(apiname);
            this.env.currentNamespace.declaredMemberNames.add(apiname);

            this.namespaceParseScanCover(SYM_semicolon);
        }
        else {
            const okdecl = this.testToken(SYM_lparen);
            if(!okdecl) {
                this.recordErrorGeneral(sinfo, "API declaration missing parameter list");
                return;
            }

            const params: FunctionParameter[] = this.parseInvokeSignatureParameters(sinfo, false, false);
        
            let resultInfo = this.env.SpecialVoidSignature;
            if (this.testAndConsumeTokenIf(SYM_colon)) {
                resultInfo = this.parseTypeSignature();
            }

            const argNames = new Set<string>(params.map((param) => param.name));
            const cargs = params.map((param) => new LocalVariableDefinitionInfo(param.name, !param.isRefParam));
            const boundtemplates = new Set<string>();

            const [preconds, postconds] = this.parsePreAndPostConditions(sinfo, argNames, new Set<string>(), new Set<string>(), true, true);
            const samples = this.parseSamples(sinfo, boundtemplates);
    
            let statusinfo: StatusInfoFilter | undefined = undefined;
            let resouceinfo: ResourceInformation[] | "**" | "{}" | undefined = undefined;
            let envinfo: EnvironmentVariableInformation[] | undefined = undefined;
            while(this.testToken(KW_event) || this.testToken(KW_status) || this.testToken(KW_resource) || this.testToken(KW_env)) {
                if(this.testToken(KW_status)) {
                    if(statusinfo !== undefined) {
                        this.recordErrorGeneral(sinfo, "Cannot have multiple status sections");
                    }

                    this.consumeToken();
                    const ttl = this.parseListOf<TypeSignature>("task status section", SYM_lbrack, SYM_rbrack, SYM_coma, () => this.parseTypeSignature());
                    if(ttl.length > 2) {
                        this.recordErrorGeneral(sinfo, "Invalid status section");
                    }

                    statusinfo = new StatusInfoFilter(ttl[0], ttl[1]); //implicit undefined is fine here
                }
                else if(this.testToken(KW_resource)) {
                    if(resouceinfo !== undefined) {
                        this.recordErrorGeneral(sinfo, "Cannot have multiple resource sections");
                    }

                    this.consumeToken();
                    if(this.testFollows(SYM_lbrace, SYM_rbrace)) {
                        this.consumeToken();
                        this.consumeToken();
                        resouceinfo = "{}";
                    }
                    else if(this.testFollows(SYM_lbrace, SYM_wildcard, SYM_rbrace)) {
                        this.consumeToken();
                        resouceinfo = this.consumeTokenAndGetValue() as "**";
                        this.consumeToken();
                    }
                    else {
                        resouceinfo = this.parseListOf<ResourceInformation>("task resource section", SYM_lbrace, SYM_rbrace, SYM_coma, () => {
                            const pp = this.parseConstResourceExpression();
                            this.ensureAndConsumeTokenIf(SYM_at, "task resource section");

                            const mod = this.ensureToken(TokenStrings.ResourceUseMod, "task resource section") ? this.consumeTokenAndGetValue() : "[*]";
                            const oops = mod.includes("*") ? "*" : mod.slice(1, -1).split("");

                            return new ResourceInformation(pp, oops as ResourceAccessModes[]);
                        });
                    }
                }
                else {
                    if(envinfo !== undefined) {
                        this.recordErrorGeneral(sinfo, "Cannot have multiple env sections");
                    }

                    this.consumeToken();
                    envinfo = this.parseListOf<EnvironmentVariableInformation>("task env section", SYM_lbrace, SYM_rbrace, SYM_coma, () => {
                        this.ensureToken(TokenStrings.ExString, "task env section");
                        const ename = this.consumeTokenAndGetValue();

                        this.ensureAndConsumeTokenIf(SYM_colon, "task env section");
                        const ttype = this.parseTypeSignature();

                        let exp: ConstantExpressionValue | undefined = undefined;
                        if(this.testAndConsumeTokenIf(SYM_eq)) {
                            exp = this.parseConstExpression(ttype);
                        }

                        return new EnvironmentVariableInformation(ename, ttype, exp);
                    });
                }
            }

            if(statusinfo === undefined) {
                statusinfo = new StatusInfoFilter(undefined, undefined);
            }
            if(envinfo === undefined) {
                envinfo = [];
            }
            if(resouceinfo === undefined) {
                resouceinfo = "{}";
            }

            this.env.pushStandardFunctionScope(cargs, boundtemplates, resultInfo);
            const body = this.parseBody(attributes, false, false);
            this.env.popStandardFunctionScope();
            
            const api = new APIDecl(this.env.currentFile, sinfo, attributes, apiname, params, resultInfo, preconds, postconds, samples, statusinfo, envinfo, resouceinfo, body);
            this.env.currentNamespace.apis.push(api);
        }
    }

    private loadWellKnownType(name: string) {
        const ccore = this.env.assembly.getCoreNamespace();

        const tdecl = ccore.typedecls.find((td) => td.name === name);
        assert(tdecl !== undefined, "Failed to find well known type");

        this.wellknownTypes.set(name, new NominalTypeSignature(tdecl.sinfo, ["Core"], [{tname: name, terms: []}], undefined, tdecl));
    }

    private static _s_lcre = /^%%[^\n]*/y;
    private static _s_bcre = /^%\*[\s\S]*?\*%/y;
    private static _s_wsre = /^\s+/y;

    private static eatDeadTextAtFileStart(contents: string): string {
        while(true) {
            let ocontents = contents;
            let m = Parser._s_lcre.exec(contents);
            while(m !== null) {
                contents = contents.slice(m[0].length);
                m = Parser._s_lcre.exec(contents);
            }

            m = Parser._s_bcre.exec(contents);
            while(m !== null) {
                contents = contents.slice(m[0].length);
                m = Parser._s_bcre.exec(contents);
            }

            m = Parser._s_wsre.exec(contents);
            while(m !== null) {
                contents = contents.slice(m[0].length);
                m = Parser._s_wsre.exec(contents);
            }

            if(ocontents.length === contents.length) {
                return contents;
            }
        }
    }

    private static _s_nsre = /^(declare[ ]+)?namespace[ ]+[A-Z][_a-zA-Z0-9]*/;
    private static parseCompilationUnit(iscore: boolean, phase: ParsePhase, file: string, contents: string, macrodefs: string[], assembly: Assembly): {ns: string, isdecl: boolean, errors: ParserError[]} {
        const tcontents = Parser.eatDeadTextAtFileStart(contents);
        const nnsm = Parser._s_nsre.exec(tcontents);
        if(nnsm === null) {
            return {ns: "[error]", isdecl: false, errors: [new ParserError(file, SourceInfo.implicitSourceInfo(), "Failed to find namespace declaration")]};
        }
        let nnt = nnsm[0].trim();

        let isdeclared = false;
        if(nnt.startsWith("declare")) {
            isdeclared = true;
            nnt = nnt.slice(7).trim();
        }
        nnt = nnt.slice(9).trim();

        const ns = nnt;
        assembly.ensureToplevelNamespace(ns);

        const ll = new Lexer(iscore, file, tcontents, macrodefs);
        const toks = ll.lex();

        const pp = new Parser(file, ns, toks, assembly, phase);

        pp.testAndConsumeTokenIf(KW_declare);
        pp.ensureAndConsumeTokenAlways(KW_namespace, "namespace declaration");
        pp.ensureAndConsumeTokenAlways(TokenStrings.IdentifierName, "namespace declaration");

        if(pp.testToken(SYM_lbrace)) {
            pp.parseListOf<boolean>("namespace", SYM_lbrace, SYM_rbrace, SYM_coma, () => {
                pp.parseNamespaceUsing();
                return true;
            });
        }
        else {
            pp.ensureAndConsumeTokenIf(SYM_semicolon, "namespace declaration");
        }

        if(phase === ParsePhase_CompleteParsing) {
            pp.loadWellKnownType("None");
            pp.loadWellKnownType("Nothing");
            pp.loadWellKnownType("Bool");

            pp.loadWellKnownType("Any");
            pp.loadWellKnownType("Some");
        }

        pp.parseNamespaceMembers(TokenStrings.EndOfStream);

        return {ns: ns, isdecl: isdeclared, errors: [...ll.errors, ...pp.currentState().errors]};
    }

    ////
    //Public methods

    static parsefiles(iscore: boolean, code: CodeFileInfo[], macrodefs: string[], assembly: Assembly, registeredNamespaces: Set<string>): ParserError[] {
        let errors: ParserError[] = [];

        //load all the names and make sure every top-level namespace is declared
        for(let i = 0; i < code.length; ++i) {
            const cunit = Parser.parseCompilationUnit(iscore, ParsePhase_RegisterNames, code[i].srcpath, code[i].contents, macrodefs, assembly);
        
            if(cunit.isdecl) {
                if(registeredNamespaces.has(cunit.ns)) {
                    errors.push(new ParserError(code[i].srcpath, SourceInfo.implicitSourceInfo(), `Duplicate namespace declaration -- ${cunit.ns}`));
                }
                registeredNamespaces.add(cunit.ns);
            }
        }

        //parse the code
        for(let i = 0; i < code.length; ++i) {
            const cunit = Parser.parseCompilationUnit(iscore, ParsePhase_CompleteParsing, code[i].srcpath, code[i].contents, macrodefs, assembly);
            errors.push(...cunit.errors);
        }

        return errors;
    }

    static parse(core: CodeFileInfo[], code: CodeFileInfo[], macrodefs: string[]): Assembly | ParserError[] {
        let assembly = new Assembly();

        let registeredNamespaces = new Set<string>();
        const coreerrors = Parser.parsefiles(true, core, macrodefs, assembly, registeredNamespaces);
        const usererrors = Parser.parsefiles(false, code, macrodefs, assembly, registeredNamespaces);

        const nsdeclerrors: ParserError[] = [];
        if(assembly.toplevelNamespaces.length !== registeredNamespaces.size) {
            assembly.toplevelNamespaces.forEach((ns) => {
                if(!registeredNamespaces.has(ns.name)) {
                    nsdeclerrors.push(new ParserError("[implicit]", SourceInfo.implicitSourceInfo(), `Missing namespace declaration -- ${ns.fullnamespace.emit()}`));
                }
            });
        }

        if(nsdeclerrors.length === 0 && coreerrors.length === 0 && usererrors.length === 0) {
            return assembly;
        }
        else {
            return [...nsdeclerrors, ...coreerrors, ...usererrors];
        }
    }

    //Test methods
    static test_parseSFunction(core: CodeFileInfo[], macrodefs: string[], sff: string): string | ParserError[] {
        let assembly = new Assembly();

        let registeredNamespaces = new Set<string>();
        const coreerrors = Parser.parsefiles(true, core, macrodefs, assembly, registeredNamespaces);
        const ferrors = Parser.parsefiles(false, [{srcpath: "main.bsq", filename: "main.bsq", contents: `declare namespace Main; ${sff}`}], macrodefs, assembly, registeredNamespaces);
        
        if(coreerrors.length !== 0 || ferrors.length !== 0) {
            return [...coreerrors, ...ferrors];
        }

        const ns = assembly.getToplevelNamespace("Main") as NamespaceDeclaration;
        const sffdecl = ns.functions.find((f) => f.name === "main");

        return sffdecl !== undefined ? sffdecl.emit(new CodeFormatter()) : "**ERROR**";
    }
}

export { 
    Parser, ParserError
};
