
import assert from "node:assert";
import { Buffer } from "node:buffer";

import { LocalVariableDefinitionInfo, ParserEnvironment, StandardScopeInfo } from "./parser_env.js";
import { AutoTypeSignature, EListTypeSignature, ErrorTypeSignature, FullyQualifiedNamespace, LambdaParameterSignature, LambdaTypeSignature, NominalTypeSignature, TemplateTypeSignature, TypeSignature } from "./type.js";
import { AbortStatement, AbstractBodyImplementation, AccessEnumExpression, AccessNamespaceConstantExpression, AccessVariableExpression, ArgumentList, ArgumentValue, AssertStatement, BinAddExpression, BinDivExpression, BinKeyEqExpression, BinKeyNeqExpression, BinLogicAndExpression, BinLogicIFFExpression, BinLogicImpliesExpression, BinLogicOrExpression, BinMultExpression, BinSubExpression, BinderInfo, BlockStatement, BodyImplementation, BuiltinBodyImplementation, CallNamespaceFunctionExpression, ConstantExpressionValue, ConstructorEListExpression, ConstructorLambdaExpression, DebugStatement, EmptyStatement, ErrorExpression, ErrorStatement, Expression, ExpressionBodyImplementation, ExpressionTag, ITest, ITestFail, ITestNone, ITestOk, ITestSome, ITestType, IfElifElseStatement, IfElseStatement, IfExpression, IfStatement, IfTest, LetExpression, LiteralExpressionValue, LiteralRegexExpression, LiteralSimpleExpression, LiteralNoneExpression, LiteralTypeDeclValueExpression, MapEntryConstructorExpression, MatchStatement, NamedArgumentValue, NumericEqExpression, NumericGreaterEqExpression, NumericGreaterExpression, NumericLessEqExpression, NumericLessExpression, NumericNeqExpression, ParseAsTypeExpression, PositionalArgumentValue, PostfixAsConvert, PostfixIsTest, PostfixOp, PostfixOperation, PredicateUFBodyImplementation, PrefixNegateOrPlusOpExpression, PrefixNotOpExpression, RefArgumentValue, SpreadArgumentValue, StandardBodyImplementation, Statement, SwitchStatement, SynthesisBodyImplementation, ValidateStatement, VariableAssignmentStatement, VariableDeclarationStatement, VariableInitializationStatement, VariableMultiAssignmentStatement, VariableMultiDeclarationStatement, VariableMultiInitializationStatement, VariableRetypeStatement, SpecialConstructorExpression, ConstructorPrimaryExpression, PostfixAccessFromName, ReturnVoidStatement, ReturnSingleStatement, PostfixInvoke, KeyCompareEqExpression, KeyCompareLessExpression, ReturnMultiStatement, SafeConvertExpression } from "./body.js";
import { APIDecl, APIResultTypeDecl, AbstractNominalTypeDecl, AdditionalTypeDeclTag, Assembly, ConceptTypeDecl, ConstMemberDecl, DatatypeMemberEntityTypeDecl, DatatypeTypeDecl, DeclarationAttibute, EntityTypeDecl, EnumTypeDecl, EnvironmentVariableInformation, EventListTypeDecl, FunctionInvokeDecl, InternalConceptTypeDecl, InvariantDecl, InvokeExample, InvokeExampleDeclFile, InvokeExampleDeclInline, InvokeTemplateTermDecl, InvokeTemplateTypeRestriction, InvokeTemplateTypeRestrictionClause, LambdaDecl, ListTypeDecl, MapEntryTypeDecl, MapTypeDecl, MemberFieldDecl, MethodDecl, NamespaceConstDecl, NamespaceDeclaration, NamespaceFunctionDecl, NamespaceUsing, PostConditionDecl, PreConditionDecl, PrimitiveEntityTypeDecl, QueueTypeDecl, ResourceAccessModes, ResourceInformation, ResultTypeDecl, SetTypeDecl, StackTypeDecl, TaskActionDecl, TaskDecl, TaskMethodDecl, TypeFunctionDecl, TypeTemplateTermDecl, TypedeclTypeDecl, ValidateDecl, WELL_KNOWN_EVENTS_VAR_NAME, WELL_KNOWN_RETURN_VAR_NAME, WELL_KNOWN_SRC_VAR_NAME, SomeTypeDecl, OptionTypeDecl, TemplateTermDeclExtraTag, InvokeParameterDecl, InvokeExampleKind, OkTypeDecl, FailTypeDecl, APIRejectedTypeDecl, APIFailedTypeDecl, APIErrorTypeDecl, APISuccessTypeDecl, InternalEntityTypeDecl, AbstractCollectionTypeDecl, InvokeExampleDeclBSQON, InvokeExampleDeclInlineRepr, InvokeExampleDeclLiteral } from "./assembly.js";
import { BuildLevel, CodeFileInfo, CodeFormatter, SourceInfo } from "./build_decls.js";
import { AllAttributes, CoreOnlyAttributes, KW__debug, KW_abort, KW_action, KW_api, KW_as, KW_assert, KW_chktest, KW_concept, KW_const, KW_datatype, KW_debug, KW_declare, KW_elif, KW_else, KW_ensures, KW_entity, KW_enum, KW_env, KW_fail, KW_errtest, KW_event, KW_example, KW_false, KW_field, KW_fn, KW_function, KW_if, KW_implements, KW_in, KW_invariant, KW_let, KW_match, KW_method, KW_namespace, KW_none, KW_of, KW_ok, KW_pred, KW_predicate, KW_provides, KW_recursive, KW_recursive_q, KW_ref, KW_release, KW_requires, KW_resource, KW_return, KW_safety, KW_self, KW_softcheck, KW_some, KW_spec, KW_status, KW_switch, KW_task, KW_test, KW_then, KW_this, KW_true, KW_type, KW_under, KW_using, KW_validate, KW_var, KW_when, KeywordStrings, LeftScanParens, ParenSymbols, RightScanParens, SYM_HOLE, SYM_amp, SYM_ampamp, SYM_arrow, SYM_at, SYM_atat, SYM_bang, SYM_bangeq, SYM_bangeqeq, SYM_bar, SYM_barbar, SYM_bigarrow, SYM_colon, SYM_coloncolon, SYM_coma, SYM_div, SYM_dot, SYM_dotdotdot, SYM_eq, SYM_eqeq, SYM_eqeqeq, SYM_gt, SYM_gteq, SYM_hash, SYM_iff, SYM_implies, SYM_langle, SYM_lbrace, SYM_lbrack, SYM_lbrackbar, SYM_lparen, SYM_lparenbar, SYM_lt, SYM_lteq, SYM_minus, SYM_negate, SYM_plus, SYM_positive, SYM_question, SYM_rangle, SYM_rbrace, SYM_rbrack, SYM_rparen, SYM_rparenbar, SYM_semicolon, SYM_times, SYM_wildcard, SpaceFrontSymbols, SpaceRequiredSymbols, StandardSymbols, TermRestrictions } from "./parser_kw.js";

import { initializeLexer, lexFront } from "@bosque/jsbrex";

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
    CString: "[LITERAL_EX_STRING]",
    TemplateString: "[LITERAL_TEMPLATE_STRING]",
    TemplateCString: "[LITERAL_TEMPLATE_EX_STRING]",

    BSQONLiteralImplicitType: "[LITERAL_BSQON_IMPLICIT_TYPE]",

    Regex: "[LITERAL_REGEX]",
    PathItem: "[LITERAL_PATH_ITEM]",
    PathTemplateItem: "[LITERAL_TEMPLATE_PATH_ITEM]",

    TZDateTime: "[LITERAL_TZTIME]",
    TAITime: "[LITERAL_TAI_TIME]",
    PlainDate: "[LITERAL_PLAIN_DATE]",
    PlainTime: "[LITERAL_PLAIN_TIME]",
    LogicalTime: "[LITERAL_LOGICAL_TIME]",
    Timestamp: "[LITERAL_TIMESTAMP]",

    DeltaDateTime: "[LITERAL_DELTA_DATETIME]",
    DeltaSeconds: "[LITERAL_DELTA_SECONDS]",
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
    KW_enum, KW_entity, KW_concept, KW_type, KW_datatype, KW_task,
    KW_event, KW_status,
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
    "None", "Bool", 
    "Nat", "Int", "BigInt", "BigNat", "Rational", "Float", "Decimal", "DecimalDegree", "LatLongCoordinate", "Complex",
    "ByteBuffer", "UUIDv4", "UUIDv7", "SHAContentHash", 
    "TZDateTime", "TAITime", "PlainDate", "PlainTime", "LogicalTime", "ISOTimestamp",
    "DeltaDateTime", "DeltaSeconds", "DeltaLogicalTime", "DeltaISOTimestamp",
    "String", "CString", 
    "Regex", "CRegex", "PathRegex",
    "Path", "PathItem", "Glob"
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

    private jsStrPos: number;
    private utf8StrPos: number;

    private jsStrEnd: number;

    cline: number;
    linestart: number;
    
    tokens: Token[];
    errors: ParserError[];

    private advancePositionInfo(epos: number): [number, number] {
        const u16count = epos - this.jsStrPos;
        const u8count = Buffer.from(this.input.substring(this.jsStrPos, epos), "utf8").length;

        return [u16count, u8count];
    }

    private advancePosition(epos: number) {
        const [u16count, u8count] = this.advancePositionInfo(epos);
        this.jsStrPos += u16count;
        this.utf8StrPos += u8count;
    }

    constructor(iscore: boolean, srcfile: string, input: string, macrodefs: string[]) {
        this.iscore = iscore;
        this.srcfile = srcfile;
        this.macrodefs = macrodefs;
        this.scanmode = [LexerStateScanMode.Enabled];

        this.input = input;
        initializeLexer(this.input);

        this.jsStrPos = 0;
        this.utf8StrPos = 0;

        const [u16count] = this.advancePositionInfo(this.input.length);
        this.jsStrEnd = u16count;

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

    private recordLexToken(jsepos: number, kind: string) {
        this.pushToken(new Token(this.cline, this.jsStrPos - this.linestart, this.jsStrPos, jsepos - this.jsStrPos, kind, kind)); //set data to kind string
        this.advancePosition(jsepos);
    }

    private recordLexTokenWData(jsepos: number, kind: string, data: string) {
        this.pushToken(new Token(this.cline, this.jsStrPos - this.linestart, this.jsStrPos, jsepos - this.jsStrPos, kind, data));
        this.advancePosition(jsepos);
    }

    private updatePositionInfo(jspos: number, jepos: number) {
        for (let i = jspos; i < jepos; ++i) {
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
        const arop = lexFront(Lexer._s_spaceSensitiveOpsRe, this.utf8StrPos);
        if (arop !== null) {
            return false;
        }

        const frop = lexFront(Lexer._s_spaceSensitiveFrontOpsRe, this.utf8StrPos);
        if (frop !== null) {
            return false;
        }

        const m = lexFront(Lexer._s_whitespaceRe, this.utf8StrPos);
        if (m === null) {
            return false;
        }

        this.updatePositionInfo(this.jsStrPos, this.jsStrPos + m.length);
        this.advancePosition(this.jsStrPos + m.length);

        return true;
    }

    private tryLexLineComment(): boolean {
        const m = this.input.startsWith("%%", this.jsStrPos);
        if (!m) {
            return false;
        }

        let jepos = this.input.indexOf("\n", this.jsStrPos);

        if (jepos === -1) {
            this.updatePositionInfo(this.jsStrPos, jepos);
            this.advancePosition(this.jsStrEnd);
        }
        else {
            jepos++;

            this.updatePositionInfo(this.jsStrPos, jepos);
            this.advancePosition(jepos);
        }

        return true;
    }

    private tryLexDocComment(): boolean {
        const m = this.input.startsWith("%** ", this.jsStrPos);
        if (!m) {
            return false;
        }

        let jepos = this.input.indexOf(" **%", this.jsStrPos + 4);
        if (jepos !== -1) {
            jepos += 4;

            this.updatePositionInfo(this.jsStrPos, jepos);
            this.recordLexTokenWData(jepos, TokenStrings.DocComment, this.input.substring(this.jsStrPos, jepos));
            return true;
        }

        return false;
    }

    private tryLexSpanComment(): boolean {
        const m = this.input.startsWith("%*", this.jsStrPos);
        if (!m) {
            return false;
        }

        let jepos = this.input.indexOf("*%", this.jsStrPos + 2);
        if (jepos === -1) {
            this.pushError(new SourceInfo(this.cline, this.linestart, this.jsStrPos, this.jsStrEnd - this.jsStrPos), "Unterminated span comment");
            
            this.updatePositionInfo(this.jsStrPos, jepos);
            this.advancePosition(this.jsStrEnd);
        }
        else {
            jepos += 2;

            this.updatePositionInfo(this.jsStrPos, jepos);
            this.advancePosition(jepos);
        }

        return true;
    }

    private static readonly _s_templateNameRe = /^[A-Z]$/;
    private static isTemplateName(str: string): boolean {
        return Lexer._s_templateNameRe.test(str);
    }

    private static readonly _s_literalTDOnlyTagRE = `"<"`;

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
    
    private static readonly _s_logicaltimeRe = `/(${Lexer._s_intValueRE})"l"(${Lexer._s_literalTDOnlyTagRE})?/`;

    private static readonly _s_deltasecondsRE = `/[+-](${Lexer._s_floatValueNoSignRE})"ds"(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static readonly _s_deltalogicaltimeRE = `/[+-](${Lexer._s_intValueNoSignRE})"dl"(${Lexer._s_literalTDOnlyTagRE})?/`;

    private static readonly _s_zerodenomRationalTaggedNumberinoRe = `/(${Lexer._s_intValueRE})"%slash;""0"${Lexer._s_literalTDOnlyTagRE}/`;
    private static readonly _s_zerodenomRationalRe = `/(${Lexer._s_intValueRE})("%slash;""0")?"R"(${Lexer._s_literalTDOnlyTagRE})?/`;

    private static readonly _s_redundantSignRE = /[+-]{2,}/y;
    private checkRedundantSigns() {
        if(this.jsStrPos !== this.jsStrEnd && (this.input[this.jsStrPos] === "+" || this.input[this.jsStrPos] === "-")) {
            Lexer._s_redundantSignRE.lastIndex = this.jsStrPos;
            const mm = Lexer._s_redundantSignRE.exec(this.input);
            if(mm !== null) {
                this.errors.push(new ParserError(this.srcfile, new SourceInfo(this.cline, this.linestart, this.jsStrPos, mm.length), "Redundant sign"));
                this.advancePosition(Math.min(this.jsStrEnd, this.jsStrPos + mm.length - 1));
            }
        }
    }

    private tryLexFloatCompositeLikeToken(): boolean {
        const mcomplex = lexFront(Lexer._s_complexRe, this.utf8StrPos);
        if(mcomplex !== null) {
            this.recordLexTokenWData(this.jsStrPos + mcomplex.length, TokenStrings.Complex, mcomplex);
            return true;
        }

        const mlatlong = lexFront(Lexer._s_latlongRe, this.utf8StrPos);
        if(mlatlong !== null) {
            this.recordLexTokenWData(this.jsStrPos + mlatlong.length, TokenStrings.LatLong, mlatlong);
            return true;
        }

        return false;
    }

    private tryLexFloatLikeToken(): boolean {
        const mdecimaldegree = lexFront(Lexer._s_decimalDegreeRe, this.utf8StrPos);
        if(mdecimaldegree !== null) {
            this.recordLexTokenWData(this.jsStrPos + mdecimaldegree.length, TokenStrings.DecimalDegree, mdecimaldegree);
            return true;
        }

        const mdeltaseconds = lexFront(Lexer._s_deltasecondsRE, this.utf8StrPos);
        if(mdeltaseconds !== null) {
            this.recordLexTokenWData(this.jsStrPos + mdeltaseconds.length, TokenStrings.DeltaSeconds, mdeltaseconds);
            return true;
        }

        const mdecimal = lexFront(Lexer._s_decimalRe, this.utf8StrPos);
        if(mdecimal !== null) {
            this.recordLexTokenWData(this.jsStrPos + mdecimal.length, TokenStrings.Decimal, mdecimal);
            return true;
        }

        const mfloat = lexFront(Lexer._s_floatRe, this.utf8StrPos);
        if(mfloat !== null) {
            this.recordLexTokenWData(this.jsStrPos + mfloat.length, TokenStrings.Float, mfloat);
            return true;
        }

        const mnumberino = lexFront(Lexer._s_floatTaggedNumberinoRe, this.utf8StrPos);
        if(mnumberino !== null) {
            this.recordLexTokenWData(this.jsStrPos + mnumberino.length, TokenStrings.TaggedNumberinoFloat, mnumberino);
            return true;
        }

        const unumberino = lexFront(Lexer._s_floatNumberinoRe, this.utf8StrPos);
        if(unumberino !== null) {
            this.recordLexTokenWData(this.jsStrPos + unumberino.length, TokenStrings.NumberinoFloat, unumberino);
            return true;
        }

        return false;
    }

    private tryLexIntegralCompositeLikeToken(): boolean {
        const mrational = lexFront(Lexer._s_rationalRe, this.utf8StrPos);
        if(mrational !== null) {
            this.recordLexTokenWData(this.jsStrPos + mrational.length, TokenStrings.Rational, mrational);
            return true;
        }

        const mnumberino = lexFront(Lexer._s_rationalTaggedNumberinoRe, this.utf8StrPos);
        if(mnumberino !== null) {
            this.recordLexTokenWData(this.jsStrPos + mnumberino.length, TokenStrings.TaggedNumberinoRational, mnumberino);
            return true;
        }

        const mzerodenom = lexFront(Lexer._s_zerodenomRationalRe, this.utf8StrPos);
        if(mzerodenom !== null) {
            this.pushError(new SourceInfo(this.cline, this.linestart, this.jsStrPos, mzerodenom.length), "Zero denominator in rational number");
            this.recordLexTokenWData(this.jsStrPos + mzerodenom.length, TokenStrings.Rational, mzerodenom);
            return true;
        }

        const mzerodenomtagged = lexFront(Lexer._s_zerodenomRationalTaggedNumberinoRe, this.utf8StrPos);
        if(mzerodenomtagged !== null) {
            this.pushError(new SourceInfo(this.cline, this.linestart, this.jsStrPos, mzerodenomtagged.length), "Zero denominator in rational number");
            this.recordLexTokenWData(this.jsStrPos + mzerodenomtagged.length, TokenStrings.TaggedNumberinoRational, mzerodenomtagged);
            return true;
        }

        return false;
    }

    private tryLexIntegralLikeToken(): boolean {
        const mlogical = lexFront(Lexer._s_logicaltimeRe, this.utf8StrPos);
        if(mlogical !== null) {
            this.recordLexTokenWData(this.jsStrPos + mlogical.length, TokenStrings.LogicalTime, mlogical);
            return true;
        }

        const m_deltalogical = lexFront(Lexer._s_deltalogicaltimeRE, this.utf8StrPos);
        if(m_deltalogical !== null) {
            this.recordLexTokenWData(this.jsStrPos + m_deltalogical.length, TokenStrings.DeltaLogicalTime, m_deltalogical);
            return true;
        }
        
        const mint = lexFront(Lexer._s_intRe, this.utf8StrPos);
        if(mint !== null) {
            this.recordLexTokenWData(this.jsStrPos + mint.length, TokenStrings.Int, mint);
            return true;
        }

        const mnat = lexFront(Lexer._s_natRe, this.utf8StrPos);
        if(mnat !== null) {
            this.recordLexTokenWData(this.jsStrPos + mnat.length, TokenStrings.Nat, mnat);
            return true;
        }

        const mbigint = lexFront(Lexer._s_bigintRe, this.utf8StrPos);
        if(mbigint !== null) {
            this.recordLexTokenWData(this.jsStrPos + mbigint.length, TokenStrings.BigInt, mbigint);
            return true;
        }

        const mbignat = lexFront(Lexer._s_bignatRe, this.utf8StrPos);
        if(mbignat !== null) {
            this.recordLexTokenWData(this.jsStrPos + mbignat.length, TokenStrings.BigNat, mbignat);
            return true;
        }

        const mtnumberino = lexFront(Lexer._s_intTaggedNumberinoRe, this.utf8StrPos);
        if(mtnumberino !== null) {
            this.recordLexTokenWData(this.jsStrPos + mtnumberino.length, TokenStrings.TaggedNumberinoInt, mtnumberino);
            return true;
        }

        const mnumberino = lexFront(Lexer._s_intNumberinoRe, this.utf8StrPos);
        if(mnumberino !== null) {
            this.recordLexTokenWData(this.jsStrPos + mnumberino.length, TokenStrings.NumberinoInt, mnumberino);
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
        const m = lexFront(Lexer._s_bytebufferRe, this.utf8StrPos);
        if(m !== null) {
            this.recordLexTokenWData(this.jsStrPos + m.length, TokenStrings.ByteBuffer, m);
            return true;
        }

        return false;
    }

    private static _s_uuidRe = `/"uuid"[47]"{"[a-fA-F0-9]{8}"-"[a-fA-F0-9]{4}"-"[a-fA-F0-9]{4}"-"[a-fA-F0-9]{4}"-"[a-fA-F0-9]{12}"}"(${Lexer._s_literalTDOnlyTagRE})?/`;
    private tryLexUUID(): boolean {
        const m = lexFront(Lexer._s_uuidRe, this.utf8StrPos);
        if(m !== null) {
            this.recordLexTokenWData(this.jsStrPos + m.length, TokenStrings.UUIDValue, m);
            return true;
        }

        return false;
    }

    private static _s_shaRe = `/"sha3{"[a-fA-F0-9]{64}"}"(${Lexer._s_literalTDOnlyTagRE})?/`;
    private tryLexHashCode(): boolean {
        const m = lexFront(Lexer._s_shaRe, this.utf8StrPos);
        if(m !== null) {
            this.recordLexTokenWData(this.jsStrPos + m.length, TokenStrings.ShaHashcode, m);
            return true;
        }

        return false;
    }

    private static readonly _s_literalGeneralTagRE = /[<]/y;
    private tryLexUnicodeString(): boolean {
        let ncpos = this.jsStrPos;
        let istemplate = false;
        if(this.input.startsWith('$"', this.jsStrPos)) {
            ncpos += 2;
            istemplate = true;
        }
        else if(this.input.startsWith('"', this.jsStrPos)) {
            ncpos += 1;
        }
        else {
            return false;
        }


        let jepos = this.input.indexOf('"', ncpos);
        if(jepos === -1) {
            this.pushError(new SourceInfo(this.cline, this.linestart, this.jsStrPos, this.jsStrEnd - this.jsStrPos), "Unterminated string literal");
            this.recordLexToken(this.jsStrEnd, TokenStrings.Error);

            return true;
        }
        else {
            jepos++;
            let strval = this.input.substring(this.jsStrPos, jepos);

            Lexer._s_literalGeneralTagRE.lastIndex = jepos;
            const mtag = Lexer._s_literalGeneralTagRE.exec(this.input);
            if(mtag !== null) {
                if(istemplate) {
                    this.pushError(new SourceInfo(this.cline, this.linestart, this.jsStrPos, jepos - this.jsStrPos), "Template strings cannot have type tags");
                }
                else {
                    strval += "[T]";
                }   
            }

            this.updatePositionInfo(this.jsStrPos, jepos);
            this.recordLexTokenWData(jepos, istemplate ? TokenStrings.TemplateString : TokenStrings.String, strval);
            return true;
        }
    }

    static _s_validCStringChars = /^[ -~\t\n]*$/;
    private tryLexCString(): boolean {
        let ncpos = this.jsStrPos;
        let istemplate = false;
        if(this.input.startsWith("$'", this.jsStrPos)) {
            ncpos += 2;
            istemplate = true;
        }
        else if(this.input.startsWith("'", this.jsStrPos)) {
            ncpos += 1;
        }
        else {
            return false;
        }

        let jepos = this.input.indexOf("'", ncpos);
        if(jepos === -1) {
            this.pushError(new SourceInfo(this.cline, this.linestart, this.jsStrPos, this.jsStrEnd - this.jsStrPos), "Unterminated CString literal");
            this.recordLexToken(this.jsStrEnd, TokenStrings.Error);

            return true;
        }
        else {
            const mstr = this.input.slice(ncpos, jepos);
            if(!Lexer._s_validCStringChars.test(mstr)) {
                this.pushError(new SourceInfo(this.cline, this.linestart, this.jsStrPos, jepos - this.jsStrPos), "Invalid chacaters in CString literal");
                this.recordLexToken(jepos, TokenStrings.Error);

                return true;
            }

            jepos++;
            let strval = this.input.substring(this.jsStrPos, jepos);

            Lexer._s_literalGeneralTagRE.lastIndex = jepos;
            const mtag = Lexer._s_literalGeneralTagRE.exec(this.input);
            if(mtag !== null) {
                if(istemplate) {
                    this.pushError(new SourceInfo(this.cline, this.linestart, this.jsStrPos, jepos - this.jsStrPos), "Template strings cannot have type tags");
                }
                else {
                    strval += "[T]";
                }   
            }

            this.updatePositionInfo(this.jsStrPos, jepos);
            this.recordLexTokenWData(jepos, istemplate ? TokenStrings.TemplateCString : TokenStrings.CString, strval);
            return true;
        }
    }

    private tryLexBSQONLiteral(): boolean {
        let ncpos = this.jsStrPos;
        if(this.input.startsWith("bsqon`", this.jsStrPos)) {
            ncpos += 6;
        }
        else {
            return false;
        }

        let jepos = this.input.indexOf("`", ncpos); //TODO: this is a bit of a hack for closed parens -- might be ok, just require internal escaping or maybe we rework a bit
        if(jepos === -1) {
            this.pushError(new SourceInfo(this.cline, this.linestart, this.jsStrPos, this.jsStrEnd - this.jsStrPos), "Unterminated bsqon literal");
            this.recordLexToken(this.jsStrEnd, TokenStrings.Error);

            return true;
        }
        else {            
            jepos += 2;
            let strval = this.input.substring(this.jsStrPos, jepos);

            //TODO we should validate that the string is valid BSQON here

            this.updatePositionInfo(this.jsStrPos, jepos);
            this.recordLexTokenWData(jepos, TokenStrings.BSQONLiteralImplicitType, strval);

            return true;
        }
    }

    private tryLexStringLike() {
        const us = this.tryLexUnicodeString();
        if(us) {
            return true;
        }

        const as = this.tryLexCString();
        if(as) {
            return true;
        }

        const bsqon = this.tryLexBSQONLiteral();
        if(bsqon) {
            return true;
        }

        return false;
    }

    private static _s_regexRe = '/"%slash;"[!-.0-~ %t;%n;]+"%slash;"[cp]?/';
    private tryLexRegex() {
        const rem = lexFront(Lexer._s_regexRe, this.utf8StrPos);
        if(rem === null) {
            return false;
        }

        this.recordLexTokenWData(this.jsStrPos + rem.length, TokenStrings.Regex, rem);
        return true;
    }

    
    private static _s_pathRe = /[$]?[gf]?\\[ !-Z^-~\[\]]\\/y;
    private static readonly _s_literalPathTagRE = /[<]/y;
    private tryLexPath() {
        Lexer._s_pathRe.lastIndex = this.jsStrPos;
        const mpth = Lexer._s_pathRe.exec(this.input);
        if(mpth !== null) {
            let jepos = this.jsStrPos + mpth[0].length;
            let pthval = mpth[0];

            const istemplate = pthval.startsWith("$");
            if(istemplate) {
                pthval = pthval.substring(1);
            }

            Lexer._s_literalPathTagRE.lastIndex = jepos;
            const mtag = Lexer._s_literalPathTagRE.exec(this.input);
            if(mtag !== null) {
                pthval += "[T]";
            }

            this.updatePositionInfo(this.jsStrPos, jepos);
            this.recordLexTokenWData(jepos, istemplate ? TokenStrings.PathTemplateItem : TokenStrings.PathItem, pthval);
            return true;
        }

        return false;
    }

    private static _s_datevalueRE = '([0-9]{4})"-"([0-9]{2})"-"([0-9]{2})';
    private static _s_timevalueRE = '([0-9]{2})":"([0-9]{2})":"([0-9]{2})';
    private static _s_tzvalueRE = '(("%lbrace;"[a-zA-Z0-9/, _-]+"%rbrace;")|[A-Z]+)';

    private static _s_datatimeRE = `/${Lexer._s_datevalueRE}"T"${Lexer._s_timevalueRE}"@"${Lexer._s_tzvalueRE}(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static _s_taitimeRE = `/${Lexer._s_datevalueRE}"T"${Lexer._s_timevalueRE}?(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static _s_plaindateRE = `/${Lexer._s_datevalueRE}(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static _s_plaintimeRE = `/${Lexer._s_timevalueRE}(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static _s_timestampRE = `/${Lexer._s_datevalueRE}"T"${Lexer._s_timevalueRE}"."([0-9]{3})"Z"(${Lexer._s_literalTDOnlyTagRE})?/`;

    private tryLexDateTime() {
        const mdt = lexFront(Lexer._s_datatimeRE, this.utf8StrPos);
        if(mdt !== null) {
            this.recordLexTokenWData(this.jsStrPos + mdt.length, TokenStrings.TZDateTime, mdt);
            return true;
        }

        const mutcdt = lexFront(Lexer._s_taitimeRE, this.utf8StrPos);
        if(mutcdt !== null) {
            this.recordLexTokenWData(this.jsStrPos + mutcdt.length, TokenStrings.TAITime, mutcdt);
            return true;
        }

        const mts = lexFront(Lexer._s_timestampRE, this.utf8StrPos);
        if(mts !== null) {
            this.recordLexTokenWData(this.jsStrPos + mts.length, TokenStrings.Timestamp, mts);
            return true;
        }

        const mpd = lexFront(Lexer._s_plaindateRE, this.utf8StrPos);
        if(mpd !== null) {
            this.recordLexTokenWData(this.jsStrPos + mpd.length, TokenStrings.PlainDate, mpd);
            return true;
        }

        const mpt = lexFront(Lexer._s_plaintimeRE, this.utf8StrPos);
        if(mpt !== null) {
            this.recordLexTokenWData(this.jsStrPos + mpt.length, TokenStrings.PlainTime, mpt);
            return true;
        }

        return false;
    }

    private static _s_deltadatevalueRE = '([0-9]{1,4})"-"([0-9]{1,2})"-"([0-9]{1,2})';
    private static _s_deltatimevalueRE = '([0-9]{1,2})":"([0-9]{1,2})":"([0-9]{1,2})';

    private static _s_datetimeDeltaRE = `/[+-]${Lexer._s_deltadatevalueRE}"T"${Lexer._s_deltatimevalueRE}?(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static _s_plaindateDeltaRE = `/[+-]${Lexer._s_deltadatevalueRE}(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static _s_plaintimeDeltaRE = `/[+-]${Lexer._s_deltatimevalueRE}(${Lexer._s_literalTDOnlyTagRE})?/`;
    private static _s_timestampDeltaRE = `/[+-]${Lexer._s_deltadatevalueRE}"T"${Lexer._s_deltatimevalueRE}"."([0-9]{3})"Z"(${Lexer._s_literalTDOnlyTagRE})?/`;

    private tryLexDateTimeDelta() {
        const mdt = lexFront(Lexer._s_datetimeDeltaRE, this.utf8StrPos);
        if(mdt !== null) {
            this.recordLexTokenWData(this.jsStrPos + mdt.length, TokenStrings.DeltaDateTime, mdt);
            return true;
        }

        const mts = lexFront(Lexer._s_timestampDeltaRE, this.utf8StrPos);
        if(mts !== null) {
            this.recordLexTokenWData(this.jsStrPos + mts.length, TokenStrings.DeltaTimestamp, mts);
            return true;
        }

        const mpd = lexFront(Lexer._s_plaindateDeltaRE, this.utf8StrPos);
        if(mpd !== null) {
            this.recordLexTokenWData(this.jsStrPos + mpd.length, TokenStrings.DeltaDateTime, mpd + "T00:00:00");
            return true;
        }

        const mpt = lexFront(Lexer._s_plaintimeDeltaRE, this.utf8StrPos);
        if(mpt !== null) {
            this.recordLexTokenWData(this.jsStrPos + mpt.length, TokenStrings.DeltaDateTime, "0000-00-00T" + mpt);
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
        const usemodop = lexFront(Lexer._s_resourceUseModRe, this.utf8StrPos);
        const spaceop = lexFront(Lexer._s_spaceSensitiveOpsRe, this.utf8StrPos);
        const frontop = lexFront(Lexer._s_spaceSensitiveFrontOpsRe, this.utf8StrPos);
        if(usemodop !== null) {
            this.recordLexTokenWData(this.jsStrPos + usemodop.length, TokenStrings.ResourceUseMod, usemodop);
            return true;
        }
        else if(spaceop !== null) {
            const realstr = " " + spaceop.trim() + " ";

            this.recordLexToken(this.jsStrPos + spaceop.length, realstr);
            return true; 
        }
        else if(frontop !== null) {
            const realstr = " " + frontop.trim();

            this.recordLexToken(this.jsStrPos + frontop.length, realstr);
            return true; 
        }
        else {
            const mm = StandardSymbols.find((value) => this.input.startsWith(value, this.jsStrPos)) || ParenSymbols.find((value) => this.input.startsWith(value, this.jsStrPos));
            if(mm !== undefined) {
                this.recordLexToken(this.jsStrPos + mm.length, mm);
                return true;
            }

        
            return false;
        }
    }

    private tryLexAttribute() {
        const mm = AllAttributes.find((value) => this.input.startsWith(value, this.jsStrPos));
        if(mm !== undefined) {
            let jepos = this.jsStrPos + mm.length;
            if(this.input.startsWith("[", jepos)) {
                jepos = this.input.indexOf("]", jepos);
                if(jepos === -1) {
                    this.pushError(new SourceInfo(this.cline, this.linestart, this.jsStrPos, this.jsStrEnd - this.jsStrPos), "Unterminated attribute");
                    this.recordLexToken(this.jsStrEnd, TokenStrings.Error);
                    return true;
                }
                jepos++;
            }

            this.recordLexTokenWData(jepos, TokenStrings.Attribute, this.input.substring(this.jsStrPos, jepos));
            return true;
        }

        if(this.iscore) {
            const cmm = CoreOnlyAttributes.find((value) => this.input.startsWith(value, this.jsStrPos));
        
            if(cmm !== undefined) {
                this.recordLexTokenWData(this.jsStrPos + cmm.length, TokenStrings.Attribute, cmm);
                return true;
            }
        }

        return false;
    }

    private processIdentifierOptions(idm: string): boolean {
        if(Lexer.isTemplateName(idm)) {
            this.recordLexTokenWData(this.jsStrPos + idm.length, TokenStrings.Template, idm);
            return true;
        }
        else {        
            this.recordLexTokenWData(this.jsStrPos + idm.length, TokenStrings.IdentifierName, idm);
            return true;
        }
    }

    private static readonly _s_taggedBooleanRE = `/"true<"|"false<"/`;
    private static readonly _s_identiferName = '/"$"?[_a-zA-Z][_a-zA-Z0-9]*/';
    private tryLexName(): boolean {
        const mtb = lexFront(Lexer._s_taggedBooleanRE, this.utf8StrPos);
        if (mtb !== null) {
            this.recordLexTokenWData(this.jsStrPos + mtb.length, TokenStrings.TaggedBoolean, mtb);
            return true;
        }

        const identifiermatch = lexFront(Lexer._s_identiferName, this.utf8StrPos);
        const kwmatch = KeywordStrings.find((value) => this.input.startsWith(value, this.jsStrPos));

        if(identifiermatch === null && kwmatch === undefined) {
            return false;
        }

        if (identifiermatch !== null && kwmatch === undefined) {
            return this.processIdentifierOptions(identifiermatch);
        }
        else if(identifiermatch === null && kwmatch !== undefined) {
            this.recordLexToken(this.jsStrPos + kwmatch.length, kwmatch);
            return true;
        }
        else {
            const nnid = identifiermatch as string;
            const nnkw = kwmatch as string;

            if (nnid.length > nnkw.length) {
                return this.processIdentifierOptions(nnid);
            }
            else {
                this.recordLexToken(this.jsStrPos + nnkw.length, nnkw);
                return true;
            }
        }
    }

    private static readonly _s_macroRe = '/("#if"" "+([A-Z][_A-Z0-9]*)|"#else"|"#endif")/';
    tryLexMacroOp(): [string, string | undefined] | undefined {
        const m = lexFront(Lexer._s_macroRe, this.utf8StrPos);
        if (m === null) {
            return undefined;
        }

        this.advancePosition(this.jsStrPos + m.length);

        if(m.slice(0, "#if".length) === "#if") {
            return ["#if", m.slice("#if".length).trim()];
        }
        else {
            return [m, undefined]
        }
    }

    lex(): Token[] {
        while (this.jsStrPos < this.jsStrEnd) {
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
                    this.errors.push(new ParserError(this.srcfile, new SourceInfo(this.cline, this.linestart, this.jsStrPos, 1), "Unrecognized token"));
                    this.recordLexToken(this.jsStrPos + 1, TokenStrings.Error);
                }
            }
        }

        if(this.jsStrPos === this.jsStrEnd) {
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

    ////////
    //
    // Namespace resolution:
    // 1) Core namespace is always in scope and implicit
    // 2) The current TOP-LEVEL namespace is always in scope and implicit
    // 3) All other namespaces must be explicitly scoped -- so if I am in a sub-namespace I can either fully scope a name or drop the top-level name ONLY
    //
    ////////

    private identifierResolvesAsScopedConstOrFunction(name: string): [NamespaceDeclaration, NamespaceFunctionDecl | NamespaceConstDecl] | undefined {
        const coredecl = this.env.assembly.getCoreNamespace();
        const cdm = coredecl.functions.find((f) => f.name === name) || coredecl.consts.find((c) => c.name === name);
        if(cdm !== undefined) {
            return [coredecl, cdm];
        }

        //acording to rules I will only allow implicit refs to toplevel namespace, even if I am in a sub-namespace
        const nsdecl = this.env.assembly.getToplevelNamespace(this.env.currentNamespace.topnamespace) as NamespaceDeclaration;

        const ndm = nsdecl.functions.find((f) => f.name === name) || nsdecl.consts.find((c) => c.name === name);
        if(ndm !== undefined) {
            return [this.env.currentNamespace, ndm];
        }

        return undefined;
    }

    private parseIdentifierAccessChainHelperTypeTail(leadingscoper: boolean, currentns: NamespaceDeclaration, scopeTokens: string[]): {nsScope: NamespaceDeclaration, scopeTokens: string[], typeTokens: {tname: string, tterms: TypeSignature[]}[]} {
        if(leadingscoper) {
            this.consumeToken();
        }
        const tsroot = this.peekTokenData();

        if(currentns.topnamespace === "Core" && (tsroot === "Result" || tsroot === "APIResult")) {
            this.consumeToken();
            const terms = this.parseTermList();

            if(!this.testToken(SYM_coloncolon)) {
                return {nsScope: currentns, scopeTokens: scopeTokens, typeTokens: [{tname: tsroot, tterms: terms}]};
            }
            else {
                this.consumeToken();
                this.ensureToken(TokenStrings.IdentifierName, "type tail");
                const ttname = (this.testToken(TokenStrings.IdentifierName) ? this.consumeTokenAndGetValue() : "[error]");

                if(tsroot === "Result" && (ttname === "Ok" || ttname === "Fail")) {
                    return {nsScope: currentns, scopeTokens: scopeTokens, typeTokens: [{tname: "Result", tterms: terms}, {tname: ttname, tterms: []}]};
                }
                else if(tsroot === "APIResult" && (ttname === "Rejected" || ttname === "Error" || ttname === "Failed" || ttname === "Success")) {
                    return {nsScope: currentns, scopeTokens: scopeTokens, typeTokens: [{tname: "APIResult", tterms: terms}, {tname: ttname, tterms: []}]};
                }
                else {
                    return {nsScope: currentns, scopeTokens: scopeTokens, typeTokens: [{tname: "error", tterms: terms}]};
                }
            }
        }
        else {
            this.consumeToken();
            const terms = this.parseTermList();

            return {nsScope: currentns, scopeTokens: scopeTokens, typeTokens: [{tname: tsroot, tterms: terms}]};
        }
    }

    private parseIdentifierAccessChainHelper(leadingscoper: boolean, currentns: NamespaceDeclaration, scopeTokens: string[]): {nsScope: NamespaceDeclaration, scopeTokens: string[], typeTokens: {tname: string, tterms: TypeSignature[]}[]} | undefined {
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

    private parseIdentifierAccessChain(): {altScope: string[] | undefined, nsScope: NamespaceDeclaration, typeTokens: {tname: string, tterms: TypeSignature[]}[]} | undefined {
        assert(isParsePhase_Enabled(this.currentPhase, ParsePhase_CompleteParsing));

        const nsroot = this.peekTokenData();
        if(!/^[A-Z][_a-zA-Z0-9]+/.test(nsroot)) {
            return undefined; //not a valid namespace or type name
        }

        const coredecl = this.env.assembly.getCoreNamespace();
        if (nsroot === "Core") {
            this.consumeToken();
            
            const ach = this.parseIdentifierAccessChainHelper(this.testToken(SYM_coloncolon), coredecl, ["Core"]);
            return ach !== undefined ? {altScope: undefined, nsScope: ach.nsScope, typeTokens: ach.typeTokens} : undefined;
        }
        else if(coredecl.declaredNames.has(nsroot)) {
            const ach = this.parseIdentifierAccessChainHelper(false, coredecl, ["Core"]);
            return ach !== undefined ? {altScope: undefined, nsScope: ach.nsScope, typeTokens: ach.typeTokens} : undefined;
        }
        else if(this.env.currentNamespace.topnamespace === nsroot) {
            this.consumeToken();
            
            const ach = this.parseIdentifierAccessChainHelper(this.testToken(SYM_coloncolon), this.env.currentNamespace, [nsroot]);
            return ach !== undefined ? {altScope: undefined, nsScope: ach.nsScope, typeTokens: ach.typeTokens} : undefined;
        }
        else if(this.env.currentNamespace.usings.find((nsuse) => nsuse.asns === nsroot) !== undefined) {
            const uns = (this.env.currentNamespace.usings.find((nsuse) => nsuse.asns === nsroot) as NamespaceUsing).fromns;
            this.consumeToken();

            const rrns = this.env.assembly.getToplevelNamespace(uns);
            if(rrns === undefined) {
                return undefined;
            }
                
            const ach = this.parseIdentifierAccessChainHelper(this.testToken(SYM_coloncolon), rrns, [nsroot]);
            return ach !== undefined ? {altScope: ach.scopeTokens, nsScope: ach.nsScope, typeTokens: ach.typeTokens} : undefined;
        }
        else if(this.env.currentNamespace.usings.find((nsuse) => nsuse.fromns === nsroot) !== undefined) {
            this.consumeToken();

            const tlns = this.env.assembly.getToplevelNamespace(nsroot);
            if(tlns === undefined) {
                return undefined;
            }
                
            const ach = this.parseIdentifierAccessChainHelper(this.testToken(SYM_coloncolon), tlns, [nsroot]);
            return ach !== undefined ? {altScope: undefined, nsScope: ach.nsScope, typeTokens: ach.typeTokens} : undefined;
        }
        else if(this.env.currentNamespace.declaredNames.has(nsroot)) {
            const ach = this.parseIdentifierAccessChainHelper(false, this.env.currentNamespace, []);
            return ach !== undefined ? {altScope: ach.scopeTokens, nsScope: ach.nsScope, typeTokens: ach.typeTokens} : undefined;
        }
        else {
            this.consumeToken();

            //hmm missing import -- see if it exists but not imported or just not there at all
            const tlns = this.env.assembly.getToplevelNamespace(nsroot);
            if(tlns === undefined) {
                this.recordErrorGeneral(this.peekToken().getSourceInfo(), `Unknown namespace ${nsroot}`);
            }
            else {
                this.recordErrorGeneral(this.peekToken().getSourceInfo(), `Missing import for namespace ${nsroot}`);
            }

            return undefined;
        }
    }

    private tryNormalizeCoreType(corens: NamespaceDeclaration, typeTokens: {tname: string, tterms: TypeSignature[]}[]): AbstractNominalTypeDecl | undefined {
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

    private normalizeTypeNameChain(sinfo: SourceInfo, ns: NamespaceDeclaration, typeTokens: {tname: string, tterms: TypeSignature[]}[]): AbstractNominalTypeDecl | undefined {
        const taskdef = ns.tasks.find((t) => t.name === typeTokens[0].tname);
        if(taskdef !== undefined) {
            return taskdef;
        }

        //handle special Core types first
        if(ns.name === "Core") {
            const ndecl = this.tryNormalizeCoreType(ns, typeTokens);
            if(ndecl !== undefined) {
                return ndecl;
            }
        }

        const nnt = ns.typedecls.find((t) => t.name === typeTokens[0].tname);
        if(nnt !== undefined) {
            return nnt;
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
                    const etype = this.parseNominalType();
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

    private parseIdentifierAsBinderVariable(): string {
        const vv = this.consumeTokenAndGetValue();
        if(vv === "_") {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Cannot use _ as an identifier name -- it is special ignored variable");
        }

        if(!/^[$][_a-z][_a-zA-Z0-9]*/.test(vv)) {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Invalid binder name -- must start with $ followed by a valid identifier name");
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
        
        const trl = this.parseListOf<InvokeTemplateTypeRestrictionClause>("template term restiction list", SYM_lbrace, SYM_rbrace, SYM_coma, () => {
            const ts = this.parseTemplateTypeReference();
            this.ensureAndConsumeTokenIf(SYM_colon, "template term restiction");

            let tags: TemplateTermDeclExtraTag[] = [];
            while(this.testToken(TokenStrings.IdentifierName) && TermRestrictions.includes(this.peekTokenData())) {
                const rr = this.consumeTokenAndGetValue();
                if(tags.find((t) => t === rr) !== undefined) {
                    this.recordErrorGeneral(this.peekToken(), "Cannot have duplicate template tags");
                }

                tags.push(rr as TemplateTermDeclExtraTag);
            }

            let subtype: TypeSignature | undefined = undefined;
            if(!this.testToken(SYM_coma) && !this.testToken(SYM_rbrace)) {
                subtype = this.parseStdTypeSignature();
            }

            return new InvokeTemplateTypeRestrictionClause(ts as TemplateTypeSignature, subtype, tags);
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

        this.env.scope = new StandardScopeInfo([...argnames].map((v) => new LocalVariableDefinitionInfo(true, v)), boundtemplates, this.wellknownTypes.get("Bool") as TypeSignature);
        while (this.testToken(KW_requires)) {
            this.consumeToken();
            
            let tag: string | undefined = undefined;
            if(this.testAndConsumeTokenIf(SYM_lbrack)) {
                if(this.ensureToken(TokenStrings.CString, "requires tag")) {
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

        const refnames = [...refParams].map((v) => new LocalVariableDefinitionInfo(true, "$" + v));

        const postvardecls = [...[...argnames].map((v) => new LocalVariableDefinitionInfo(true, v)), ...refnames, new LocalVariableDefinitionInfo(true, WELL_KNOWN_RETURN_VAR_NAME)];
        if(taskcond || apicond) {
            postvardecls.push(new LocalVariableDefinitionInfo(true, WELL_KNOWN_EVENTS_VAR_NAME));
        }

        this.env.scope = new StandardScopeInfo(postvardecls, boundtemplates, this.wellknownTypes.get("Bool") as TypeSignature);
        
        while (this.testToken(KW_ensures)) {
            this.consumeToken();

            let tag: string | undefined = undefined;
            if(this.testAndConsumeTokenIf(SYM_lbrack)) {
                if(this.ensureToken(TokenStrings.CString, "requires tag")) {
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
        while (this.testToken(KW_spec) || this.testToken(KW_test) || this.testToken(KW_example)) {
            let ekind: InvokeExampleKind = InvokeExampleKind.Test;
            while(this.testToken(KW_spec) || this.testToken(KW_test) || this.testToken(KW_example)) {
                if(ekind !== undefined) {
                    this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Cannot have multiple example kinds in the same example block");
                }

                if(this.testToken(KW_spec)) {
                    ekind = InvokeExampleKind.Spec;
                }
                else if(this.testToken(KW_test)) {
                    ekind = InvokeExampleKind.Test;
                }
                else {
                    ekind = InvokeExampleKind.Synth;
                }
                this.consumeToken();
            }

            const terms = this.parseInvokeTemplateArguments();

            if(this.testToken(TokenStrings.PathItem)) {
                const fp = this.consumeTokenAndGetValue();

                if(ekind === InvokeExampleKind.Spec) {
                    this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Cannot have a spec example in a file -- too big for documentation");
                }
                samples.push(new InvokeExampleDeclFile(this.env.currentFile, sinfo, ekind, terms, fp));
            }
            else {
                this.ensureToken(SYM_lbrace, "example");
                const examples = this.parseListOf<InvokeExampleDeclInlineRepr>("examples", SYM_lbrace, SYM_rbrace, SYM_semicolon, () => {
                    if(this.testToken(TokenStrings.BSQONLiteralImplicitType)) {
                        const bsqon = this.consumeTokenAndGetValue();
                        return new InvokeExampleDeclLiteral(bsqon);
                    }
                    else {
                        this.env.scope = new StandardScopeInfo([], boundtemplates, undefined);
                        const args = this.parseListOf<Expression>("example args", SYM_lbrack, SYM_rbrack, SYM_coma, () => this.parseExpression());
                        this.env.scope = undefined;

                        this.ensureAndConsumeTokenAlways(SYM_arrow, "example");

                        this.env.scope = new StandardScopeInfo([new LocalVariableDefinitionInfo(true, WELL_KNOWN_SRC_VAR_NAME)], boundtemplates, undefined);
                        const result = this.parseExpression();
                        this.env.scope = undefined;

                        return new InvokeExampleDeclBSQON(args, result);
                    }
                });
                
                samples.push(new InvokeExampleDeclInline(this.env.currentFile, sinfo, ekind, terms, examples));
            }

            this.ensureAndConsumeTokenIf(SYM_semicolon, "example");
        }

        return samples;
    }

    private parseLambdaSignatureParameter(): LambdaParameterSignature {
        const cinfo = this.peekToken().getSourceInfo();

        const isref = this.testAndConsumeTokenIf(KW_ref);
        const isrest = this.testAndConsumeTokenIf(SYM_dotdotdot);

        if(isref && isrest) {
            this.recordErrorGeneral(cinfo, "Cannot have a parameter that is both a reference and a rest");
        }

        const ptype = this.parseParameterTypeSignature();

        if(this.testToken(SYM_eq)) {
            this.recordErrorGeneral(this.peekToken(), "Cannot have default values for lambda parameters");
            this.consumeToken();
            this.parseExpression(); //try to eat the expression to recover nicely
        }

        return new LambdaParameterSignature(ptype, isref, isrest);
    }

    private parseLambdaSignatureParameters(cinfo: SourceInfo): LambdaParameterSignature[] {
        const params = this.parseListOf<LambdaParameterSignature>("function parameter list", SYM_lparen, SYM_rparen, SYM_coma, () => {
            return this.parseLambdaSignatureParameter()
        });
        
        if(params.length !== 0) {
            if(params.slice(0, -1).some((param) => param.isRestParam)) {
                this.recordErrorGeneral(cinfo, "Spread parameter must be the last parameter");
            }
        }

        return params;
    }

    private parseInvokeDeclParameter(boundtemplates: Set<string>): InvokeParameterDecl {
        const cinfo = this.peekToken().getSourceInfo();

        const isref = this.testAndConsumeTokenIf(KW_ref);
        const isrest = this.testAndConsumeTokenIf(SYM_dotdotdot);

        if(isref && isrest) {
            this.recordErrorGeneral(cinfo, "Cannot have a parameter that is both a reference and a rest");
        }

        const idok = this.ensureToken(TokenStrings.IdentifierName, "function parameter");
        const pname = idok ? this.parseIdentifierAsStdVariable() : "[error]";

        let ptype = this.env.SpecialAutoSignature;
        if(this.testAndConsumeTokenIf(SYM_colon)) {
            ptype = this.parseParameterTypeSignature();
        }
        else {
            this.recordErrorGeneral(cinfo, "Missing : type specifier -- auto typing is only supported for lambda parameter declarations");

            //maybe do a try parse type here in case someone just forgot the colon
            if(!this.testToken(SYM_coma) && !this.testToken(SYM_rparen) && !this.testToken(SYM_eq)) {
                ptype = this.parseParameterTypeSignature();
            }
        }

        let optDefaultExp: ConstantExpressionValue | undefined = undefined;
        if(this.testAndConsumeTokenIf(SYM_eq)) {
            optDefaultExp = this.parseConstExpression(ptype, boundtemplates);
        }

        if(isrest && optDefaultExp !== undefined) {
            this.recordErrorGeneral(cinfo, "Cannot have a default value for rest parameters");
        }

        if(isref && optDefaultExp !== undefined) {
            this.recordErrorGeneral(cinfo, "Cannot have a default value for reference parameters");
        }

        return new InvokeParameterDecl(pname, ptype, optDefaultExp, isref, isrest);
    }

    private parseInvokeDeclParameters(cinfo: SourceInfo, implicitRefAllowed: boolean, boundtemplates: Set<string>): InvokeParameterDecl[] {
        const params = this.parseListOf<InvokeParameterDecl>("function parameter list", SYM_lparen, SYM_rparen, SYM_coma, () => {
            return this.parseInvokeDeclParameter(boundtemplates)
        });
        
        if(params.length !== 0) {
            if(params.slice(0, -1).some((param) => param.isRestParam)) {
                this.recordErrorGeneral(cinfo, "Rest parameter must be the last parameter");
            }

            if(!implicitRefAllowed && params.some((param) => param.isRefParam)) {
                this.recordErrorGeneral(cinfo, "Cannot have more than one reference parameter");
            }

            if(params[params.length - 1].isRestParam && params.some((param) => param.optDefaultValue !== undefined)) {
                this.recordErrorGeneral(cinfo, "Cannot have default values and a rest parameter");
            }
        }

        return params;
    }

    private parseInvokeTemplateTermDecl(): InvokeTemplateTermDecl {
        this.ensureToken(TokenStrings.Template, "template term");
        const tname = this.consumeTokenAndGetValue();

        let ttype: TypeSignature | undefined = undefined;
        let tags: TemplateTermDeclExtraTag[] = [];
        if(this.testAndConsumeTokenIf(SYM_colon)) {
            while(this.testToken(TokenStrings.IdentifierName) && TermRestrictions.includes(this.peekTokenData())) {
                const rr = this.consumeTokenAndGetValue();
                if(tags.find((t) => t === rr) !== undefined) {
                    this.recordErrorGeneral(this.peekToken(), "Cannot have duplicate template tags");
                }

                tags.push(rr as TemplateTermDeclExtraTag);
            }

            if(!this.testToken(SYM_coma) && !this.testToken(SYM_rangle)) {
                ttype = this.parseStdTypeSignature();
            }
        }

        return new InvokeTemplateTermDecl(tname, tags, ttype);
    }

    private parseInvokeTemplateTerms(): InvokeTemplateTermDecl[] { 
        let terms: InvokeTemplateTermDecl[] = [];
        if(this.testToken(SYM_langle)) {
            const ttok = this.peekToken();

            terms = this.parseListOf<InvokeTemplateTermDecl>("template terms", SYM_langle, SYM_rangle, SYM_coma, () => {
                return this.parseInvokeTemplateTermDecl();
            });

            if(terms.length === 0) {
                this.recordErrorGeneral(ttok.getSourceInfo(), "Template term list cannot be empty");
            }
        }

        return terms;
    }

    private parseLambdaDeclParameter(): InvokeParameterDecl {
        const cinfo = this.peekToken().getSourceInfo();

        const isref = this.testAndConsumeTokenIf(KW_ref);
        const isrest = this.testAndConsumeTokenIf(SYM_dotdotdot);

        if(isref && isrest) {
            this.recordErrorGeneral(cinfo, "Cannot have a parameter that is both a reference and a rest");
        }

        const idok = this.ensureToken(TokenStrings.IdentifierName, "function parameter");
        const pname = idok ? this.parseIdentifierAsStdVariable() : "[error]";

        let ptype = this.env.SpecialAutoSignature;
        if(this.testAndConsumeTokenIf(SYM_colon)) {
            ptype = this.parseParameterTypeSignature();
        }

        if(this.testToken(SYM_eq)) {
            this.recordErrorGeneral(this.peekToken(), "Cannot have default values for lambda parameters");
            this.consumeToken();
            this.parseExpression(); //try to eat the expression to recover nicely
        }

        return new InvokeParameterDecl(pname, ptype, undefined, isref, isrest);
    }

    private parseLambdaDeclParameters(cinfo: SourceInfo): InvokeParameterDecl[] {
        const params = this.parseListOf<InvokeParameterDecl>("lambda parameter list", SYM_lparen, SYM_rparen, SYM_coma, () => {
            return this.parseLambdaDeclParameter()
        });
        
        if(params.length !== 0) {
            if(params.slice(0, -1).some((param) => param.isRestParam)) {
                this.recordErrorGeneral(cinfo, "Rest parameter must be the last parameter");
            }
        }

        return params;
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

        const params: InvokeParameterDecl[] = this.parseLambdaDeclParameters(cinfo);

        const allTypedParams = params.every((param) => !(param.type instanceof AutoTypeSignature));
        const someTypedParams = params.some((param) => !(param.type instanceof AutoTypeSignature));

        if(!allTypedParams && someTypedParams) {
            this.recordErrorGeneral(cinfo, "Cannot have a mix of typed parameter with untyped parameters");
        }

        let resultInfo = this.env.SpecialAutoSignature;
        if (this.testAndConsumeTokenIf(SYM_colon)) {
            resultInfo = this.parseReturnTypeSignature();
        }

        if(!this.testToken(SYM_bigarrow)) {
            this.recordExpectedError(this.peekToken(), SYM_bigarrow, "lambda declaration");
        }
        else {
            this.consumeToken();
        }
        
        const lambdaargs = params.map((param) => new LocalVariableDefinitionInfo(!param.isRefParam, param.name));
        this.env.pushLambdaScope(lambdaargs, (resultInfo instanceof AutoTypeSignature) ? undefined : resultInfo);
        const body = this.parseBody([], false, true);
        this.env.popLambdaScope();

        return new LambdaDecl(this.env.currentFile, cinfo, [], ispred ? "pred" : "fn", isrecursive, params, resultInfo, body, !someTypedParams);
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
        const boundtemplates = new Set<string>(...typeTerms, ...terms.map((term) => term.name));

        const okdecl = this.testToken(SYM_lparen);
        if(!okdecl) {
            this.recordErrorGeneral(cinfo, "Function declaration missing parameter list");
            return undefined;
        }

        const params: InvokeParameterDecl[] = this.parseInvokeDeclParameters(cinfo, true, boundtemplates);
        
        let resultInfo = this.env.SpecialVoidSignature;
        if (this.testAndConsumeTokenIf(SYM_colon)) {
            resultInfo = this.parseReturnTypeSignature();
        }

        const argNames = new Set<string>(params.map((param) => param.name));
        const cargs = params.map((param) => new LocalVariableDefinitionInfo(!param.isRefParam, param.name));
        const refparams = new Set<string>(params.filter((param) => param.isRefParam).map((param) => param.name));

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
        const boundtemplates = new Set<string>(...typeTerms, ...terms.map((term) => term.name));

        const okdecl = this.testToken(SYM_lparen);
        if(!okdecl) {
            this.recordErrorGeneral(cinfo, "Method declaration missing parameter list");
            return undefined;
        }

        const params: InvokeParameterDecl[] = this.parseInvokeDeclParameters(cinfo, !isref, boundtemplates);
        
        let resultInfo = this.env.SpecialVoidSignature;
        if (this.testAndConsumeTokenIf(SYM_colon)) {
            resultInfo = this.parseReturnTypeSignature();
        }

        const argNames = new Set<string>(params.map((param) => param.name));
        let cargs = params.map((param) => new LocalVariableDefinitionInfo(!param.isRefParam, param.name));
        const refparams = new Set<string>(params.filter((param) => param.isRefParam).map((param) => param.name));

        if(taskscope) {
            argNames.add("self");
            cargs = [new LocalVariableDefinitionInfo(!isref, "self"), ...cargs];
            if(isref) {
                refparams.add("self");
            }
        }
        else {
            argNames.add("this");
            cargs = [new LocalVariableDefinitionInfo(!isref, "this"), ...cargs];
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
        const boundtemplates = new Set<string>(...typeTerms, ...terms.map((term) => term.name));

        const okdecl = this.testToken(SYM_lparen);
        if(!okdecl) {
            this.recordErrorGeneral(cinfo, "Action declaration missing parameter list");
            return undefined;
        }

        const params: InvokeParameterDecl[] = this.parseInvokeDeclParameters(cinfo, false, boundtemplates);
        
        let resultInfo = this.env.SpecialVoidSignature;
        if (this.testAndConsumeTokenIf(SYM_colon)) {
            resultInfo = this.parseReturnTypeSignature();
        }

        const argNames = new Set<string>(params.map((param) => param.name));
        let cargs = params.map((param) => new LocalVariableDefinitionInfo(!param.isRefParam, param.name));
        const refparams = new Set<string>(params.filter((param) => param.isRefParam).map((param) => param.name));

        argNames.add("self");
        cargs = [new LocalVariableDefinitionInfo(true, "self"), ...cargs];
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

    //parse just types that are legal as return types
    private parseReturnTypeSignature(): TypeSignature {
        switch (this.peekTokenKind()) {
            case TokenStrings.Template: {
                return this.parseTemplateTypeReference();
            }
            case TokenStrings.IdentifierName: {
                return this.parseNominalType();
            }
            case SYM_lbrack: {
                return this.parseElistType();
            }
            default: {
                return new ErrorTypeSignature(this.peekToken().getSourceInfo(), undefined);
            }
        }
    }

    //parse just types that are legal as parameter types
    private parseParameterTypeSignature(): TypeSignature {
        switch (this.peekTokenKind()) {
            case TokenStrings.Template: {
                return this.parseTemplateTypeReference();
            }
            case TokenStrings.IdentifierName: {
                return this.parseNominalType();
            }
            case SYM_lbrack: {
                return this.parseElistType();
            }
            case KW_fn:
            case KW_pred:
            case KW_recursive_q:
            case KW_recursive: {
                return this.parseLambdaType();
            }
            default: {
                return new ErrorTypeSignature(this.peekToken().getSourceInfo(), undefined);
            }
        }
    }

    //parse just types that are legal as provides types
    private parseProvidesTypeSignature(): TypeSignature {
        switch (this.peekTokenKind()) {
            case TokenStrings.IdentifierName: {
                return this.parseNominalType();
            }
            default: {
                return new ErrorTypeSignature(this.peekToken().getSourceInfo(), undefined);
            }
        }
    }

    //parse just types that are legal as tags (typedecl literal, stringof, etc)
    private parseTypeTagSignature(): TypeSignature {
        switch (this.peekTokenKind()) {
            case TokenStrings.Template: {
                return this.parseTemplateTypeReference();
            }
            case TokenStrings.IdentifierName: {
                return this.parseNominalType();
            }
            default: {
                return new ErrorTypeSignature(this.peekToken().getSourceInfo(), undefined);
            }
        }
    }

    //parse just types that are legal as the RHS of a typedecl
    private parseTypedeclRHSSignature(): TypeSignature {
        switch (this.peekTokenKind()) {
            case TokenStrings.IdentifierName: {
                return this.parseNominalType();
            }
            default: {
                return new ErrorTypeSignature(this.peekToken().getSourceInfo(), undefined);
            }
        }
    }

    //parse just types that are legal as variables, fields, consts, etc
    private parseStdTypeSignature(): TypeSignature {
        switch (this.peekTokenKind()) {
            case TokenStrings.Template: {
                return this.parseTemplateTypeReference();
            }
            case TokenStrings.IdentifierName: {
                return this.parseNominalType();
            }
            case SYM_lbrack: {
                return this.parseElistType();
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
            const ttok = this.peekToken();

            terms = this.parseListOf<TypeSignature>("template term list", SYM_langle, SYM_rangle, SYM_coma, () => {
                return this.parseStdTypeSignature();
            });

            if(terms.length === 0) {
                this.recordErrorGeneral(ttok, "Template term list cannot be empty");
            }
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
            return new ErrorTypeSignature(sinfo, nsr.nsScope.fullnamespace);
        }
        else {
            const resolved = this.normalizeTypeNameChain(sinfo, nsr.nsScope, nsr.typeTokens);
            if(resolved === undefined) {
                return new ErrorTypeSignature(sinfo, nsr.nsScope.fullnamespace);
            }
            else {
                const altns = nsr.altScope !== undefined ? new FullyQualifiedNamespace(nsr.altScope) : undefined;
                return new NominalTypeSignature(sinfo, altns, resolved, nsr.typeTokens.flatMap((te) => te.tterms));
            }
        }
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

        const params = this.parseLambdaSignatureParameters(sinfo);

        this.ensureAndConsumeTokenAlways(SYM_arrow, "lambda type reference");
        const resultInfo = this.parseReturnTypeSignature();

        return new LambdaTypeSignature(sinfo, isrecursive, name, params, resultInfo);
    }

    private parseElistType(): TypeSignature {
        const sinfo = this.peekToken().getSourceInfo();

        const elargs = this.parseListOf<TypeSignature>("paren-type", SYM_lparenbar, SYM_rparenbar, SYM_coma, () => {
            return this.parseStdTypeSignature();
        });

        return new EListTypeSignature(sinfo, elargs);
    }

    ////
    //Expression parsing
    private parseBinderInfo(): string | undefined {
        if(!this.testToken(TokenStrings.IdentifierName)) {
            return undefined;
        }
        else {
            return this.parseIdentifierAsBinderVariable();
        }
    }

    private parseMatchTypeGuard(): TypeSignature | undefined {
        if (this.testToken(KW_under)) {
            return undefined;
        }
        else {
            return this.parseStdTypeSignature();
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
        else {
            if(this.testToken(KW_none)) {
                this.consumeToken();
                return new ITestNone(isnot);
            }
            else if(this.testToken(KW_some)) {
                this.consumeToken();
                return new ITestSome(isnot);
            }
            else if(this.testToken(KW_ok)) {
                this.consumeToken();
                return new ITestOk(isnot);
            }
            else if(this.testToken(KW_fail)) {
                this.consumeToken();
                return new ITestFail(isnot);
            }
            else {
                this.recordErrorGeneral(this.peekToken(), "Expected ITest");
                return undefined;
            }
        }
    }

    private parseITypeTest(isnot: boolean): ITest {
        this.consumeToken();
        const ttype = this.parseStdTypeSignature();
        this.ensureAndConsumeTokenAlways(SYM_rangle, "ITest");

        return new ITestType(isnot, ttype);
    }

    private parseInvokeTemplateArguments() {
        let args: TypeSignature[] = [];
        if (this.testToken(SYM_langle)) {
            const ttok = this.peekToken();

            args = this.parseListOf<TypeSignature>("template arguments", SYM_langle, SYM_rangle, SYM_coma, () => {
                return this.parseStdTypeSignature();
            });

            if(args.length === 0) {
                this.recordErrorGeneral(ttok, "Template argument list cannot be empty");
            }
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

    private parseArguments(lparen: string, rparen: string, sep: string, refok: boolean, spreadok: boolean, anyspreadok: boolean, mapargs: boolean, lambdaok: boolean): ArgumentList {
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

        if(!anyspreadok) {
            const spreadidx = args.findIndex((arg, index) => arg instanceof SpreadArgumentValue && index !== args.length - 1);
            const badspread = spreadidx !== -1 && args.slice(spreadidx).some((arg) => !(arg instanceof NamedArgumentValue));
            if(badspread) {
                this.recordErrorGeneral(this.peekToken(), "Spread argument must be the last argument");
            }
        }

        return new ArgumentList(args);
    }
    
    private parseLambdaTerm(): Expression {
        const sinfo = this.peekToken().getSourceInfo();

        const ldecl = this.parseLambdaDecl();
        if(ldecl === undefined) {
            return new ErrorExpression(sinfo, undefined, undefined);
        }

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

    private parseConstExpression(etype: TypeSignature | undefined, boundtemplates: Set<string>): ConstantExpressionValue {
        this.env.pushStandardFunctionScope([], boundtemplates, etype);
        this.env.pushBlockScope();
        const exp = this.parseExpression();
        this.env.popBlockScope();
        this.env.popStandardFunctionScope();

        return new ConstantExpressionValue(exp);
    }

    private static isTaggedLiteral(val: string): boolean {
        return val.endsWith("<");
    }

    private processTaggedLiteral(val: string): [string, TypeSignature] {
        const vval = val.slice(0, val.length - 1);

        const ttype = this.parseTypeTagSignature();
        this.ensureAndConsumeTokenIf(SYM_rangle, "tagged literal");
        
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

    private trySpecialNamespaceCall(sinfo: SourceInfo, ns: NamespaceDeclaration, name: string, targs: TypeSignature[], args: ArgumentList): Expression | undefined {
        if(ns.fullnamespace.ns[0] !== "Core") {
            return undefined;
        }

        if(ns.name === "XCore") {
            if(name === "s_safeas") {
                if(targs.length !== 2) {
                    this.recordErrorGeneral(sinfo, "SafeAs expects exactly two template arguments");
                }
    
                if(args.args.length !== 1 || args.args.every((arg) => arg instanceof PositionalArgumentValue)) {
                    this.recordErrorGeneral(sinfo, "SafeAs expects exactly one positional arguments");
                }

                return new SafeConvertExpression(sinfo, (args.args[0] as PositionalArgumentValue).exp, targs[0], targs[1]);
            }
        }

        if(ns.name === "KeyComparator") {
            if(targs.length !== 1) {
                this.recordErrorGeneral(sinfo, "KeyComparator expects exactly one (keytype) template argument");
            }

            if(args.args.length !== 2 || args.args.every((arg) => arg instanceof PositionalArgumentValue)) {
                this.recordErrorGeneral(sinfo, "KeyComparator expects exactly two positional arguments");
            }

            if(name === "equal") {
                return new KeyCompareEqExpression(sinfo, targs[0], (args.args[0] as PositionalArgumentValue).exp, (args.args[1] as PositionalArgumentValue).exp);
            }
            else {
                assert(name === "less");

                return new KeyCompareLessExpression(sinfo, targs[0], (args.args[0] as PositionalArgumentValue).exp, (args.args[1] as PositionalArgumentValue).exp);
            }
        }

        return undefined;
    }

    private parseImplicitNamespaceScopedConstOrFunc(ns: NamespaceDeclaration, decl: NamespaceFunctionDecl | NamespaceConstDecl): Expression {
        const sinfo = this.peekToken().getSourceInfo();

        const idname = this.parseIdentifierAsStdVariable();

        if(decl instanceof NamespaceConstDecl) {
            return new AccessNamespaceConstantExpression(sinfo, true, ns.fullnamespace, idname);
        }
        else {
            const targs = this.parseInvokeTemplateArguments();
            const rec = this.parseInvokeRecursiveArgs();
            const args = this.parseArguments(SYM_lparen, SYM_rparen, SYM_coma, true, true, false, false, true);

            const specialop = this.trySpecialNamespaceCall(sinfo, ns, idname, targs, args);
            if(specialop !== undefined) {
                return specialop;
            }
            else {
                return new CallNamespaceFunctionExpression(sinfo, true, ns.fullnamespace, idname, targs, rec, args);
            }
        }
    }

    private parseNamespaceScopedFirstExpression(nspace: NamespaceDeclaration): Expression {
        const sinfo = this.peekToken().getSourceInfo();

        this.ensureAndConsumeTokenAlways(SYM_coloncolon, "namespace scoped expression");
        this.ensureToken(TokenStrings.IdentifierName, "namespace scoped expression");

        const idname = this.parseIdentifierAsStdVariable();

        const constOpt = nspace.consts.find((c) => c.name === idname);
        const funOpt = nspace.functions.find((f) => f.name === idname);
        if(constOpt !== undefined) {
            return new AccessNamespaceConstantExpression(sinfo, false, nspace.fullnamespace, idname);
        }
        else if(funOpt !== undefined) {
            const targs = this.parseInvokeTemplateArguments();
            const rec = this.parseInvokeRecursiveArgs();
            const args = this.parseArguments(SYM_lparen, SYM_rparen, SYM_coma, true, true, false, false, true);

            const specialop = this.trySpecialNamespaceCall(sinfo, nspace, idname, targs, args);
            if(specialop !== undefined) {
                return specialop;
            }
            else {
                return new CallNamespaceFunctionExpression(sinfo, false, nspace.fullnamespace, idname, targs, rec, args);
            }
        }
        else {
            this.recordErrorGeneral(sinfo, `Name '${nspace.fullnamespace.emit()}::${idname}' is not defined in this context`);
            return new ErrorExpression(sinfo, {ns: nspace, typeopt: undefined}, undefined);
        }
    }

    private parseTypeScopedFirstExpression(access: {altScope: string[] | undefined, nsScope: NamespaceDeclaration, typeTokens: {tname: string, tterms: TypeSignature[]}[]}): Expression {
        const sinfo = this.peekToken().getSourceInfo();

        const altns = access.altScope !== undefined ? new FullyQualifiedNamespace(access.altScope) : undefined;
        const resolved = this.normalizeTypeNameChain(sinfo, access.nsScope, access.typeTokens);
        const tsig = (resolved === undefined)  ? new ErrorTypeSignature(sinfo, access.nsScope.fullnamespace) : new NominalTypeSignature(sinfo, altns, resolved, access.typeTokens.flatMap((te) => te.tterms));

        if(this.testToken(SYM_hash)) {
            this.consumeToken();
            
            const ename = this.parseIdentifierAsEnumMember();
            return new AccessEnumExpression(sinfo, tsig, ename);
        }
        else if(this.testToken(SYM_lbrace)) {
            const isContainer = tsig instanceof NominalTypeSignature && tsig.decl instanceof AbstractCollectionTypeDecl;
            const isMap = isContainer && (tsig instanceof NominalTypeSignature) && (tsig.decl instanceof MapTypeDecl);
            const args = this.parseArguments(SYM_lbrace, SYM_rbrace, SYM_coma, false, isContainer, isContainer, isMap, false);

            return new ConstructorPrimaryExpression(sinfo, tsig, args);
        }
        else {
            this.recordErrorGeneral(sinfo, "Unknown type scoped expression");
            return new ErrorExpression(sinfo, {ns: access.nsScope, typeopt: tsig}, undefined);
        }
    }

    private parseIdentifierFirstExpression(): Expression {
        const sinfo = this.peekToken().getSourceInfo();
        if (this.peekTokenData().startsWith("$")) {
            const idname = this.parseIdentifierAsBinderVariable();
            return new AccessVariableExpression(sinfo, idname);
        }
        else if (this.env.identifierResolvesAsVariable(this.peekTokenData())) {
            const idname = this.parseIdentifierAsStdVariable();
            return new AccessVariableExpression(sinfo, idname);
        }
        else {
            const peekname = this.peekTokenData();

            const isScopedConstOrFunc = this.identifierResolvesAsScopedConstOrFunction(this.peekTokenData());
            if(isScopedConstOrFunc !== undefined) {
                return this.parseImplicitNamespaceScopedConstOrFunc(isScopedConstOrFunc[0], isScopedConstOrFunc[1]);
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

    private parseSpecialConstructorExpression(): Expression {
        const sinfo = this.peekToken().getSourceInfo();
        const cons = this.consumeTokenAndGetValue() as "fail" | "ok" | "some";

        this.ensureAndConsumeTokenAlways(SYM_lparen, "special constructor expression");
        const exp = this.parseExpression();
        this.ensureAndConsumeTokenAlways(SYM_rparen, "special constructor expression");

        return new SpecialConstructorExpression(sinfo, cons, exp);
    }

    private parseEListConstructorExpression(): Expression {
        let exps = this.parseListOf<Expression>("elist constructor expression", SYM_lparenbar, SYM_rparenbar, SYM_coma, () => {
            return this.parseExpression();
        });

        if(exps.length === 0) {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Empty elist constructor");
        }
        if(exps.length === 1) {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Singleton elist constructor");
        }

        const argl = new ArgumentList(exps.map((arg) => new PositionalArgumentValue(arg)));
        return new ConstructorEListExpression(this.peekToken().getSourceInfo(), argl);
    }

    private parseParseAsTypeExpression(): Expression {
        const sinfo = this.peekToken().getSourceInfo();

        this.ensureAndConsumeTokenAlways(SYM_langle, "parse as type expression");
        const tsig = this.parseStdTypeSignature();
        this.ensureAndConsumeTokenAlways(SYM_rangle, "parse as type expression");

        this.ensureAndConsumeTokenAlways(SYM_lparen, "parse as type expression");
        const exp = this.parseExpression();
        this.ensureAndConsumeTokenAlways(SYM_rparen, "parse as type expression");

        return new ParseAsTypeExpression(sinfo, exp, tsig);
    }

    private parseLetExpression(): Expression {
        const sinfo = this.peekToken().getSourceInfo();

        const decls = this.parseListOf<{vname: string, vtype: TypeSignature | undefined, value: Expression}>("let expression", KW_let, KW_in, SYM_coma, () => {
            this.ensureToken(TokenStrings.IdentifierName, "let expression variable name");
            const vname = this.parseIdentifierAsIgnoreableVariable();

            let vtype: TypeSignature | undefined = undefined;
            if(this.testAndConsumeTokenIf(SYM_colon)) {
                vtype = this.parseStdTypeSignature();
            }

            this.ensureAndConsumeTokenIf(SYM_eq, "let expression");

            const value = this.parseExpression();

            return {vname: vname, vtype: vtype, value: value};
        });

        const body = this.parseExpression();

        return new LetExpression(sinfo, decls, body);
    }

    private parsePrimaryExpression(): Expression {
        const sinfo = this.peekToken().getSourceInfo();

        const tk = this.peekTokenKind();
        if (tk === KW_none) {
            this.consumeToken();
            return new LiteralNoneExpression(ExpressionTag.LiteralNoneExpression, sinfo);
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
        else if(tk === TokenStrings.TZDateTime) {
            const dstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralTZDateTimeExpression, dstr);
        }
        else if(tk === TokenStrings.TAITime) {
            const dstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralTAITimeExpression, dstr);
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
        else if(tk === TokenStrings.Timestamp) {
            const dstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralISOTimeStampExpression, dstr);
        }
        else if(tk === TokenStrings.DeltaDateTime) {
            const dstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralDeltaDateTimeExpression, dstr);
        }
        else if(tk === TokenStrings.DeltaTimestamp) {
            const dstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralDeltaISOTimeStampExpression, dstr);
        }
        else if(tk === TokenStrings.DeltaSeconds) {
            const dstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralDeltaSecondsExpression, dstr);
        }
        else if(tk === TokenStrings.DeltaLogicalTime) {
            const dstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralDeltaLogicalExpression, dstr);
        }
        else if(tk === TokenStrings.Regex) {
            const rstr = this.consumeTokenAndGetValue();
            return new LiteralRegexExpression(rstr.endsWith("/") ? ExpressionTag.LiteralUnicodeRegexExpression : ExpressionTag.LiteralCRegexExpression, sinfo, rstr);
        }
        else if(tk === TokenStrings.String) {
            const sstr = this.consumeTokenAndGetValue();
            if(sstr.endsWith("[T]")) {
                const vval = sstr.slice(0, sstr.length - "[T]".length);

                this.ensureAndConsumeTokenIf(SYM_langle, "string type tag");
                const ttype = this.parseTypeTagSignature();
                this.ensureAndConsumeTokenIf(SYM_rangle, "string type tag");
                
                return new LiteralTypeDeclValueExpression(sinfo, new LiteralSimpleExpression(ExpressionTag.LiteralStringExpression, sinfo, vval), ttype);
            }
            else {
                return new LiteralSimpleExpression(ExpressionTag.LiteralStringExpression, sinfo, sstr);
            }
        }
        else if(tk === TokenStrings.CString) {
            const sstr = this.consumeTokenAndGetValue();
            if(sstr.endsWith("[T]")) {
                const vval = sstr.slice(0, sstr.length - "[T]".length);
                
                this.ensureAndConsumeTokenIf(SYM_langle, "string type tag");
                const ttype = this.parseTypeTagSignature();
                this.ensureAndConsumeTokenIf(SYM_rangle, "string type tag");

                return new LiteralTypeDeclValueExpression(sinfo, new LiteralSimpleExpression(ExpressionTag.LiteralCStringExpression, sinfo, vval), ttype);
            }
            else {
                return new LiteralSimpleExpression(ExpressionTag.LiteralCStringExpression, sinfo, sstr);
            }
        }
        else if(tk === TokenStrings.PathItem) {
            const sstr = this.consumeTokenAndGetValue();

            let ptag = ExpressionTag.LiteralPathExpression;
            if(!sstr.startsWith("\\")) {
                ptag = sstr.startsWith("g") ? ExpressionTag.LiteralGlobExpression : ExpressionTag.LiteralPathItemExpression;
            }

            if(sstr.endsWith("[T]")) {
                const vval = sstr.slice(0, sstr.length - "[T]".length);
                
                this.ensureAndConsumeTokenIf(SYM_langle, "string type tag");
                const ttype = this.parseTypeTagSignature();
                this.ensureAndConsumeTokenIf(SYM_rangle, "string type tag");

                return new LiteralTypeDeclValueExpression(sinfo, new LiteralSimpleExpression(ptag, sinfo, vval), ttype);
            }
            else {
                return new LiteralSimpleExpression(ptag, sinfo, sstr);
            }
        }
        else if (tk === KW_this) {
            this.consumeToken();
            return new AccessVariableExpression(sinfo, "this");
        }
        else if (tk === KW_self) {
            assert(false, "Need to handle any self cases");
        }
        else if(tk === KW_some || tk === KW_ok || tk === KW_fail) {
            return this.parseSpecialConstructorExpression();
        }
        else if(tk === SYM_rbrack) {
            return this.parseEListConstructorExpression();
        }
        else if(tk === SYM_langle) {
            return this.parseParseAsTypeExpression();
        }
        else if(tk === SYM_lparen) {
            const closeparen = this.scanMatchingParens(SYM_lbrack, SYM_rbrack);
            this.prepStateStackForNested("paren-type", closeparen);

            this.consumeToken();
            let exp: Expression;
            if (this.testToken(KW_let)) {
                exp = this.parseLetExpression();
            }
            else {
                exp = this.parseExpression();
            }
            
            if(this.testToken(SYM_rparen)) {
                this.consumeToken();
            }
            else {
                if(closeparen !== undefined) {
                    this.currentState().moveToRecoverPosition();
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

    private parsePostfixExpression(): Expression {
        let rootexp = this.parsePrimaryExpression();

        let ops: PostfixOperation[] = [];
        while (this.testToken(SYM_dot) || this.testToken(SYM_question) || this.testToken(SYM_at) || this.testToken(SYM_lbrack)) {
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
            else if(this.testToken(SYM_lbrack)) {
                assert(false, "Not implemented yet -- literal key access");
            }
            else if(this.testToken(SYM_lbrackbar)) {
                assert(false, "Not implemented yet -- update fields");
            }
            else {
                this.ensureAndConsumeTokenAlways(SYM_dot, "postfix access/update/invoke");

                if(this.testToken(SYM_lparenbar)) {
                    assert(false, "Not implemented yet -- project fields");
                }
                   
                else if(this.testToken(TokenStrings.NumberinoInt)) {
                    assert(false, "Not implemented yet -- elist access");
                }
                else {
                    this.ensureToken(TokenStrings.IdentifierName, "postfix access/invoke");
                    
                    let resolvedScope: TypeSignature | undefined = undefined;
                    if(this.peekTokenKind(1) === SYM_coloncolon) { //it is either T::f or N::T...::f
                        resolvedScope = this.parseNominalType();
                        this.ensureToken(SYM_coloncolon, "postfix access");
                    }

                    const name = this.parseIdentifierAsStdVariable();
                    if(!this.testToken(SYM_langle) && !this.testToken(SYM_lbrack) && !this.testToken(SYM_lparen)) {
                        if(resolvedScope !== undefined) {
                            this.recordErrorGeneral(sinfo, "Encountered named access but given type resolver (only valid on method calls)");
                        }

                        ops.push(new PostfixAccessFromName(sinfo, name));
                    }
                    else {
                        const targs = this.parseInvokeTemplateArguments();
                        const rec = this.parseInvokeRecursiveArgs();
                        const args = this.parseArguments(SYM_lparen, SYM_rparen, SYM_coma, false, true, false, false, true);

                        ops.push(new PostfixInvoke(sinfo, resolvedScope, name, targs, rec, args));
                    }
                }
            }
        }

        if (ops.length === 0) {
            return rootexp;
        }
        else {
            return new PostfixOp(ops[0].sinfo, rootexp, ops);
        }
    }

    private prefixStackApplicationHandler(exp: Expression, sinfo: SourceInfo, ops: [string, TypeSignature | undefined][]): Expression {
        for (let i = 0; i < ops.length; ++i) {
            const op = ops[i];

            if(op[0] === SYM_bang) {
                exp = new PrefixNotOpExpression(sinfo, exp);
            }
            else if(op[0] === SYM_negate) {
                exp = new PrefixNegateOrPlusOpExpression(sinfo, exp, "-");
            }
            else if(op[0] === SYM_positive) {
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
        while(this.testToken(SYM_bang) || this.testToken(SYM_positive) || this.testToken(SYM_negate)) {
            ops.push([this.consumeTokenAndGetValue(), undefined]);
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

        return [exp, bindername, implicitdef, ispostflow, itest];
    }

    private parseMatchTest(isexp: boolean): [Expression, string | undefined, boolean] {
        let exp: Expression;
        let bindername: string | undefined = undefined;
        let implicitdef: boolean = true;
        let dobind: boolean;

        this.ensureAndConsumeTokenIf(SYM_lparen, "swtich/match test");
        if(this.testFollows(TokenStrings.IdentifierName, SYM_eq)) {
            bindername = this.parseBinderInfo();
            implicitdef = false;
            this.ensureAndConsumeTokenAlways(SYM_eq, "if test");
        }
        
        exp = this.parseExpression();
        this.ensureAndConsumeTokenIf(SYM_rparen, "swtich/match test");

        dobind = this.testAndConsumeTokenIf(SYM_at);

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

        return [exp, bindername, implicitdef];
    }

    private parseIfExpression(): Expression {
        const sinfo = this.peekToken().getSourceInfo();

        this.consumeToken();
        const [iexp, bindername, implicitdef, _, itest] = this.parseIfTest(true);

        this.ensureAndConsumeTokenIf(KW_then, "if-expression")

        const ifvalueinfo = this.parseExpression();
        let binder: BinderInfo | undefined = undefined;
        if(bindername !== undefined) {
            binder = new BinderInfo(bindername, implicitdef, false);
        }

        this.ensureAndConsumeTokenIf(KW_else, "if-expression");
        const elsevalueinfo = this.parseExpression();

        return new IfExpression(sinfo, new IfTest(iexp, itest), binder, ifvalueinfo, elsevalueinfo);
    }

    private parseExpression(): Expression {
        return this.parseImpliesExpression();
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
        if(isref && this.testFollows(TokenStrings.IdentifierName, SYM_at)) {
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
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Unknown statment expression starting with -- " + this.peekToken().kind);
            return new ErrorStatement(this.peekToken().getSourceInfo());
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
            itype = this.parseStdTypeSignature();
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
                return new ReturnVoidStatement(sinfo);
            }
            else {
                const rexp = this.parseRHSExpression();
                if(this.testToken(SYM_semicolon)) {
                    return new ReturnSingleStatement(sinfo, rexp);
                }
                else {
                    let rexps = [rexp];
                    while(this.testToken(SYM_coma)) {
                        this.consumeToken();
                        rexps.push(this.parseRHSExpression());
                    }

                    return new ReturnMultiStatement(sinfo, rexps);
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
                this.ensureToken(TokenStrings.CString, "validate statement tag");
                diagnosticTag = this.consumeTokenAndGetValue();
                this.ensureAndConsumeTokenAlways(SYM_rbrack, "validate statement tag");
            }

            const exp = this.parseExpression();

            return new ValidateStatement(sinfo, exp, diagnosticTag);
        }
        else if (this.testToken(KW__debug)) {
            this.consumeToken();

            const value = this.parseExpression();
            
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

    /*
    TODO: use this with env-scoped and other scopeable statements

    private parseUnScopedBlockStatement(): BlockStatement {
        const sinfo = this.peekToken().getSourceInfo();

        this.env.pushBlockScope();

        const closeparen = this.scanMatchingParens(SYM_lbracebar, SYM_rbracebar);
        this.prepStateStackForNested("BlockStatement", closeparen);

        let stmts: Statement[] = [];
        this.ensureAndConsumeTokenAlways(SYM_lbracebar, "block statement");
        while(!this.testToken(SYM_rbracebar) && !this.testToken(TokenStrings.Recover) && !this.testToken(TokenStrings.EndOfStream)) {
            const stmt = this.parseStatement();
            stmts.push(stmt);
        }
        this.ensureAndConsumeTokenAlways(SYM_rbracebar, "block statement");
        
        this.popStateIntoParentOk();
        this.env.popBlockScope();

        if(stmts.length === 0) {
            this.recordErrorGeneral(sinfo, "Empty block statement -- should include a ';' to indicate intentionally empty block");
        }

        return new BlockStatement(sinfo, stmts, false);
    }
    */

    private parseScopedBlockStatement(): BlockStatement {
        const sinfo = this.peekToken().getSourceInfo();

        this.env.pushBlockScope();

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
        this.env.popBlockScope();

        if(stmts.length === 0) {
            this.recordErrorGeneral(sinfo, "Empty block statement -- should include a ';' to indicate intentionally empty block");
        }

        return new BlockStatement(sinfo, stmts, true);
    }

    private parseIfElseStatement(): Statement {
        const sinfo = this.peekToken().getSourceInfo();

        this.ensureAndConsumeTokenAlways(KW_if, "if statement cond");
        const [iexp, bindername, implicitdef, ispostflow, itest] = this.parseIfTest(false);

        const ifbody = this.parseScopedBlockStatement();
        let binder: BinderInfo | undefined = undefined;
        if(bindername !== undefined) {
            binder = new BinderInfo(bindername, implicitdef, ispostflow);
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
                return new IfStatement(sinfo, new IfTest(iexp, itest), binder, ifbody);
            }
            else {
                const elsebody = this.parseScopedBlockStatement();
                return new IfElseStatement(sinfo, new IfTest(iexp, itest), binder, ifbody, elsebody);
            }
        }
        else {
            if(binder !== undefined) {
                this.recordErrorGeneral(sinfo, "Cannot have a binder in an if-elif-else statement");
            }

            const elssebody = this.parseScopedBlockStatement();
            return new IfElifElseStatement(sinfo, [{cond: iexp, block: ifbody}, ...conds.map((cc) => { return {cond: cc.cond.exp, block: cc.block}; })], elssebody);
        }
    }

    private parseSwitchStatement(): Statement {
        const sinfo = this.peekToken().getSourceInfo();
        
        this.ensureAndConsumeTokenAlways(KW_switch, "switch statement dispatch value");

        this.ensureAndConsumeTokenAlways(SYM_lparen, "switch statement dispatch value");
        const sexp = this.parseExpression();
        this.ensureAndConsumeTokenAlways(SYM_rparen, "switch statement dispatch value");

        let entries: { lval: LiteralExpressionValue | undefined, value: BlockStatement }[] = [];
        this.ensureAndConsumeTokenAlways(SYM_lbrace, "switch statement options");
        
        const swlit = this.parseSwitchLiteralGuard();
        this.ensureAndConsumeTokenIf(SYM_bigarrow, "switch statement entry");
        const svalue = this.parseScopedBlockStatement();

        entries.push({ lval: swlit, value: svalue });
        while (this.testToken(SYM_bar)) {
            this.consumeToken();

            const swlitx = this.parseSwitchLiteralGuard();
            this.ensureAndConsumeTokenIf(SYM_bigarrow, "switch statement entry");
            const svaluex = this.parseScopedBlockStatement();

            entries.push({ lval: swlitx, value: svaluex });
        }
        this.ensureAndConsumeTokenAlways(SYM_rbrace, "switch statement options");

        return new SwitchStatement(sinfo, sexp, entries);
    }

    private parseMatchStatement(): Statement {
        const sinfo = this.peekToken().getSourceInfo();
        
        this.ensureAndConsumeTokenAlways(KW_match, "match statement dispatch value");

        const [mexp, binder, implicitdef] = this.parseMatchTest(true);

        let entries: { mtype: TypeSignature | undefined, value: BlockStatement }[] = [];
        this.ensureAndConsumeTokenAlways(SYM_lbrace, "match statement options");

        const mtype = this.parseMatchTypeGuard();
        this.ensureAndConsumeTokenIf(SYM_bigarrow, "match statement entry");
        const mvalue = this.parseScopedBlockStatement();

        entries.push({ mtype: mtype, value: mvalue });
        while (this.testToken(SYM_bar)) {
            this.consumeToken();
            
            const mtypex = this.parseMatchTypeGuard();
            this.ensureAndConsumeTokenIf(SYM_bigarrow, "match statement entry");
            const mvaluex = this.parseScopedBlockStatement();

            entries.push({ mtype: mtypex, value: mvaluex });
        }
        this.ensureAndConsumeTokenAlways(SYM_rbrace, "switch statment options");

        let bindinfo: BinderInfo | undefined = undefined;
        if(binder !== undefined) {
            bindinfo = new BinderInfo(binder, implicitdef, false);
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

        let ttype: TypeSignature | undefined = undefined;
        let tags: TemplateTermDeclExtraTag[] = [];
        if(this.testAndConsumeTokenIf(SYM_colon)) {
            while(this.testToken(TokenStrings.IdentifierName) && TermRestrictions.includes(this.peekTokenData())) {
                const rr = this.consumeTokenAndGetValue();
                if(tags.find((t) => t === rr) !== undefined) {
                    this.recordErrorGeneral(this.peekToken(), "Cannot have duplicate template tags");
                }

                tags.push(rr as TemplateTermDeclExtraTag);
            }

            if(!this.testToken(SYM_coma) && !this.testToken(SYM_rangle)) {
                ttype = this.parseStdTypeSignature();
            }
        }

        return new TypeTemplateTermDecl(tname, tags, ttype);
    }

    private parseTypeTemplateTerms(): TypeTemplateTermDecl[] { 
        let terms: TypeTemplateTermDecl[] = [];
        if(this.testToken(SYM_langle)) {
            const ttok = this.peekToken();

            terms = this.parseListOf<TypeTemplateTermDecl>("template terms", SYM_langle, SYM_rangle, SYM_coma, () => {
                return this.parseTypeTemplateTermDecl();
            });

            if(terms.length === 0) {
                this.recordErrorGeneral(ttok.getSourceInfo(), "Expected at least one template term");
            }
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

        //TODO: support package name scope here
        if(chain.length !== 1) {
            this.recordErrorGeneral(sinfo, "Expected a single namespace identifier -- TODO support package name scope");
        }

        if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterNames)) {
            if(chain.length === 0) {
                this.recordErrorGeneral(sinfo, "Expected a namespace identifier");

                this.scanOverCodeTo(SYM_semicolon);
            }
            else {
                if(!this.testToken(KW_as)) {
                    if(this.env.currentNamespace.isTopNamespace()) {
                        this.env.currentNamespace.usings.push(new NamespaceUsing(this.env.currentFile, chain[0], undefined));
                    }
                    else {
                        this.recordErrorGeneral(sinfo, `Cannot "use" a namespace in a non-toplevel namespace`);
                    }
                }
                else {
                    this.consumeToken();
                    this.ensureToken(TokenStrings.IdentifierName, "namespace import");
                    const asns = this.parseIdentifierAsNamespaceOrTypeName();

                    if(this.env.currentNamespace.isTopNamespace()) {
                        this.env.currentNamespace.usings.push(new NamespaceUsing(this.env.currentFile, chain[0], asns));
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
            if (this.testToken(KW_const)) {
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
            else if(this.testFollows(KW_type) || this.testFollows(KW_status, KW_type) || this.testFollows(KW_event, KW_type)) {
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

            const nsdecl = new NamespaceDeclaration(nsname, this.env.currentNamespace.topnamespace, new FullyQualifiedNamespace([...this.env.currentNamespace.fullnamespace.ns, nsname]));

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
            nsdecl.usings = ons.usings;

            this.env.currentNamespace = nsdecl;
            this.ensureAndConsumeTokenAlways(SYM_lbrace, "nested namespace declaration");
            this.parseNamespaceMembers(SYM_rbrace);
            this.ensureAndConsumeTokenAlways(SYM_rbrace, "nested namespace declaration");

            this.env.currentNamespace = ons;
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
            const stype = this.parseStdTypeSignature();

            this.ensureAndConsumeTokenIf(SYM_eq, "const member");
            const value = this.parseConstExpression(stype, new Set<string>());
        
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

    private parseProvides(): TypeSignature[] {
        assert(isParsePhase_Enabled(this.currentPhase, ParsePhase_CompleteParsing));

        let first = true;
        let provides: TypeSignature[] = [];
        if (this.testAndConsumeTokenIf(KW_provides)) {
            while(this.testToken(TokenStrings.IdentifierName) || this.testToken(SYM_coma)) {
                if(first) {
                    first = false;
                }
                else {
                    if(this.testToken(SYM_coma)) {
                        this.consumeToken();
                    }
                    else {
                        this.recordErrorGeneral(this.peekToken(), "Expected a comma between provided interfaces");
                    }
                }

                provides.push(this.parseProvidesTypeSignature());
            }
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
        const stype = this.parseStdTypeSignature();

        this.ensureAndConsumeTokenIf(SYM_eq, "const member");
        const value = this.parseConstExpression(stype, this.env.getScope().boundtemplates);

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

    private parseMemberField(memberFields: MemberFieldDecl[] | undefined, allMemberNames: Set<string>, attributes: DeclarationAttibute[], typeTerms: Set<string>) {
        assert(isParsePhase_Enabled(this.currentPhase, ParsePhase_CompleteParsing));

        const sinfo = this.peekToken().getSourceInfo();
        this.ensureAndConsumeTokenAlways(KW_field, "member field");

        this.ensureToken(TokenStrings.IdentifierName, "member field");
        const fname = this.parseIdentifierAsStdVariable();

        this.ensureAndConsumeTokenIf(SYM_colon, "member field");
        const ftype = this.parseStdTypeSignature();

        let ivalue: ConstantExpressionValue | undefined = undefined;
        if (this.testAndConsumeTokenIf(SYM_eq)) {
            ivalue = this.parseConstExpression(ftype, typeTerms);
        }

        if(memberFields === undefined) {
            this.recordErrorGeneral(sinfo, "Cannot have a const member on this type");
        }
        if(allMemberNames.has(fname)) {
            this.recordErrorGeneral(sinfo, `Duplicate const member ${fname}`);
        }
        allMemberNames.add(fname);

        if(memberFields !== undefined && !memberFields.some((cm) => cm.name === fname)) {
            memberFields.push(new MemberFieldDecl(this.env.currentFile, sinfo, attributes, fname, ftype, ivalue, false));
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

        while (this.testToken(KW_invariant) || this.testToken(KW_validate)) {
            const isvalidate = this.testToken(KW_validate);
            this.consumeToken();

            let tag: string | undefined = undefined;
            if(this.testAndConsumeTokenIf(SYM_lbrack)) {
                if(this.ensureToken(TokenStrings.CString, "invariant/validate tag")) {
                    tag = this.consumeTokenAndGetValue();
                }
            
                this.ensureAndConsumeTokenAlways(SYM_rbrack, "invariant/validate tag");
            }

            if(isvalidate) {
                const exp = this.parseConstExpression(this.wellknownTypes.get("Bool") as TypeSignature, typeTerms);

                if(vdates === undefined) {
                    this.recordErrorGeneral(sinfo, "Cannot have a validate on this type");
                }
                else {
                    vdates.push(new ValidateDecl(this.env.currentFile, sinfo, tag, exp));
                }
            }
            else {
                const level = this.parseBuildInfo(KW_release);
                const exp = this.parseConstExpression(this.wellknownTypes.get("Bool") as TypeSignature, typeTerms);

                if(invs === undefined) {
                    this.recordErrorGeneral(sinfo, "Cannot have an invariant on this type");
                }
                else {
                    invs.push(new InvariantDecl(this.env.currentFile, sinfo, tag, level, exp));
                }
            }

            this.ensureAndConsumeTokenIf(SYM_semicolon, "invariant");
        }
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
                this.parseMemberField(memberFields, allMemberNames, attributes, typeTerms);
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
                    this.parseNestedEntity(specialConcept, attributes, typeTerms);
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

    private parseNestedEntity(specialConcept: InternalConceptTypeDecl, attributes: DeclarationAttibute[], typeTerms: Set<string>) {
        this.ensureAndConsumeTokenAlways(KW_entity, "entity declaration");
        this.ensureToken(TokenStrings.IdentifierName, "entity declaration");
        const ename = this.parseIdentifierAsNamespaceOrTypeName();

        if(ename === "Ok" || ename === "Fail") {
            const tdecl = (specialConcept as ResultTypeDecl).nestedEntityDecls.find((ned) => ned.name === ename) as InternalEntityTypeDecl;

            const provides = this.parseProvides();
            if(provides.length !== 0) {
                tdecl.provides.push(...provides);
            }

            this.parseOOPMembersCommonAll(false, undefined, typeTerms, undefined, undefined, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined, undefined);
        }
        else {
            const tdecl = (specialConcept as APIResultTypeDecl).nestedEntityDecls.find((ned) => ned.name === ename) as InternalEntityTypeDecl;

            const provides = this.parseProvides();
            if(provides.length !== 0) {
                tdecl.provides.push(...provides);
            }

            this.parseOOPMembersCommonAll(false, undefined, typeTerms, undefined, undefined, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined, undefined);
        }
    }

    private parseEntityRegisterType(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, etag: AdditionalTypeDeclTag) {
        let tdecl: AbstractNominalTypeDecl | undefined = undefined;

        if(this.env.currentNamespace.fullnamespace.ns[0] === "Core") {
            if(PRIMITIVE_ENTITY_TYPE_NAMES.includes(name)) {
                tdecl = new PrimitiveEntityTypeDecl(this.env.currentFile, sinfo, attributes, name);
            }
            else if(name === "Some") {
                tdecl = new SomeTypeDecl(this.env.currentFile, sinfo, attributes, "Some");
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
                assert(!attributes.some((attr) => attr.name === "__internal"), "Missing special case on primitive entity parse -- " + name);

                tdecl = new EntityTypeDecl(this.env.currentFile, sinfo, attributes, this.env.currentNamespace.fullnamespace, name, etag);
            }
        }
        else {
            assert(!attributes.some((attr) => attr.name === "__internal"), "Missing special case on primitive entity parse");

            tdecl = new EntityTypeDecl(this.env.currentFile, sinfo, attributes, this.env.currentNamespace.fullnamespace, name, etag);
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

        const provides = this.parseProvides();
        if(provides.length !== 0) {
            tdecl.provides.push(...provides);
        }

        if(tdecl instanceof PrimitiveEntityTypeDecl) {
            this.parseOOPMembersCommonAll(false, undefined, new Set<string>(), undefined, undefined, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined, undefined);
        }
        else if(tdecl instanceof SomeTypeDecl) {
            this.parseOOPMembersCommonAll(false, undefined, new Set<string>("T"), undefined, undefined, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined, undefined);
        }
        else if(tdecl instanceof ListTypeDecl || tdecl instanceof StackTypeDecl || tdecl instanceof QueueTypeDecl || tdecl instanceof SetTypeDecl) {
            this.parseOOPMembersCommonAll(false, undefined, new Set<string>("T"), undefined, undefined, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined, undefined);
        }
        else if(tdecl instanceof MapEntryTypeDecl) {
            this.parseOOPMembersCommonAll(false, undefined, new Set<string>(["K", "V"]), undefined, undefined, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined, undefined);
        }
        else if(tdecl instanceof MapTypeDecl) {
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

    private parseNestedEntityRegisterType(pdecl: InternalConceptTypeDecl) {
        let attributes: DeclarationAttibute[] = [];
        while(this.testToken(TokenStrings.Attribute) || this.testToken(TokenStrings.DocComment)) {
            const attr = this.parseAttribute();
            attributes.push(attr);
        }

        const sinfo = this.peekToken().getSourceInfo();

        this.ensureAndConsumeTokenAlways(KW_entity, "entity declaration");
        this.ensureToken(TokenStrings.IdentifierName, "entity declaration");
        const ename = this.parseIdentifierAsNamespaceOrTypeName();

        if(ename === "Ok" || ename === "Fail") {
            const rdecl = pdecl as ResultTypeDecl;
            if(ename === "Ok") {
                rdecl.nestedEntityDecls.push(new OkTypeDecl(this.env.currentFile, sinfo, attributes, ename));
            }
            else {
                rdecl.nestedEntityDecls.push(new FailTypeDecl(this.env.currentFile, sinfo, attributes, ename));
            }
        }
        else {
            const rdecl = pdecl as APIResultTypeDecl;
            if(ename === "APIRejectedTypeDecl") {
                rdecl.nestedEntityDecls.push(new APIRejectedTypeDecl(this.env.currentFile, sinfo, attributes, ename));
            }
            else if(ename === "APIFailedTypeDecl") {
                rdecl.nestedEntityDecls.push(new APIFailedTypeDecl(this.env.currentFile, sinfo, attributes, ename));
            }
            else if(ename === "APIErrorTypeDecl") {
                rdecl.nestedEntityDecls.push(new APIErrorTypeDecl(this.env.currentFile, sinfo, attributes, ename));
            }
            else {
                rdecl.nestedEntityDecls.push(new APISuccessTypeDecl(this.env.currentFile, sinfo, attributes, ename));
            }   
        }

        this.scanOverCodeTo(SYM_lbrace);
        this.scanOverCodeParenSet(SYM_lbrace, SYM_rbrace);
    }

    private parseConceptRegisterType(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, etag: AdditionalTypeDeclTag) {
        let tdecl: AbstractNominalTypeDecl | undefined = undefined;

        if(this.env.currentNamespace.fullnamespace.ns[0] === "Core") {
            if(name === "Option") {
                tdecl = new OptionTypeDecl(this.env.currentFile, sinfo, attributes, "Option");
            }
            else if(name === "Result") {
                tdecl = new ResultTypeDecl(this.env.currentFile, sinfo, attributes, "Result");

                this.scanOverCodeTo(SYM_lbrace);
                this.consumeToken();
                this.parseNestedEntityRegisterType(tdecl);
                this.parseNestedEntityRegisterType(tdecl);

                this.scanOverCodeTo(SYM_rbrace);
                this.consumeToken();
            }
            else if(name === "APIResult") {
                tdecl = new APIResultTypeDecl(this.env.currentFile, sinfo, attributes, "APIResult");

                this.scanOverCodeTo(SYM_lbrace);
                this.consumeToken();
                this.parseNestedEntityRegisterType(tdecl);
                this.parseNestedEntityRegisterType(tdecl);
                this.parseNestedEntityRegisterType(tdecl);
                this.parseNestedEntityRegisterType(tdecl);

                this.scanOverCodeTo(SYM_rbrace);
                this.consumeToken();
            }
            else {
                assert(false, "Unknown special concept type -- " + name);
            }
        }
        else {
            assert(!attributes.some((attr) => attr.name === "__internal"), "Missing special case on primitive concept parse");

            tdecl = new ConceptTypeDecl(this.env.currentFile, sinfo, attributes, this.env.currentNamespace.fullnamespace, name, etag);
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

        const provides = this.parseProvides();
        if(provides.length !== 0) {
            tdecl.provides.push(...provides);
        }

        if(tdecl instanceof OptionTypeDecl) {
            this.parseOOPMembersCommonAll(false, undefined, new Set<string>("T"), undefined, undefined, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined, undefined);
        }
        else if(tdecl instanceof ResultTypeDecl) {
            this.parseOOPMembersCommonAll(false, tdecl, new Set<string>(["T", "E"]), undefined, undefined, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined, undefined);
        }
        else if(tdecl instanceof APIResultTypeDecl) {
            this.parseOOPMembersCommonAll(false, tdecl, new Set<string>(["T"]), undefined, undefined, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined, undefined);
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

            const enumtype = new EnumTypeDecl(this.env.currentFile, sinfo, [...attributes, new DeclarationAttibute("__keycomparable", [], undefined), new DeclarationAttibute("__typedeclable", [], undefined)], this.env.currentNamespace.fullnamespace, ename, members, etag);
            this.env.currentNamespace.typedecls.push(enumtype);

            this.env.currentNamespace.declaredNames.add(ename);
            this.env.currentNamespace.declaredTypeNames.push({name: ename, hasterms: false});
        }
        else {
            const tdecl = this.env.currentNamespace.typedecls.find((td) => td.name === ename);
            assert(tdecl !== undefined, "Failed to find entity type");

            this.namespaceParseScanCover(endtok);
        }
    }

    private parseTypeDecl(attributes: DeclarationAttibute[], endtok: string) {
        const sinfo = this.peekToken().getSourceInfo();

        const etag: AdditionalTypeDeclTag = this.parseAdditionalTypeDeclTag();
        this.ensureAndConsumeTokenAlways(KW_type, "type alias declaration");
        this.ensureToken(TokenStrings.IdentifierName, "type alias declaration");
        const iname = this.parseIdentifierAsNamespaceOrTypeName();

        if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterNames)) {
            if(this.env.currentNamespace.checkDeclNameClashType(iname, false)) {
                this.recordErrorGeneral(sinfo, `Collision between type and other names -- ${iname}`);
            }

            const tdecl = new TypedeclTypeDecl(this.env.currentFile, sinfo, attributes, this.env.currentNamespace.fullnamespace, iname, etag, new ErrorTypeSignature(sinfo, undefined));
            this.env.currentNamespace.typedecls.push(tdecl);

            this.env.currentNamespace.declaredNames.add(iname);
            this.env.currentNamespace.declaredTypeNames.push({name: iname, hasterms: this.testToken(SYM_langle)});

            this.scanOverCodeTo(SYM_lbrace, SYM_semicolon);
            if(!this.testToken(SYM_semicolon)) {
                this.scanOverCodeParenSet(SYM_lbrace, SYM_rbrace);
            }
        }
        else {
            const tdecl = this.env.currentNamespace.typedecls.find((td) => td.name === iname);
            assert(tdecl !== undefined && (tdecl instanceof TypedeclTypeDecl), "Failed to find type type");

            this.ensureAndConsumeTokenIf(SYM_eq, "type declaration");
            const ttype = this.parseTypedeclRHSSignature();
            (tdecl as TypedeclTypeDecl).valuetype = ttype;

            if(this.testAndConsumeTokenIf(KW_of)) {
                const ofexp = this.parseConstExpression(undefined, new Set<string>());
                (tdecl as TypedeclTypeDecl).optofexp = ofexp;
            }

            if(!this.testAndConsumeTokenIf(SYM_semicolon)) {
                this.ensureAndConsumeTokenIf(SYM_amp, "type declaration");

               const provides = this.parseProvides();
                if(provides.length !== 0) {
                    tdecl.provides.push(...provides);
                }

                this.parseOOPMembersCommonAll(false, undefined, new Set<string>(), tdecl.invariants, tdecl.validates, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined, undefined);
            }
        }
    }

    private parseDatatypeMemberEntityTypeDecl(attributes: DeclarationAttibute[], parenttype: DatatypeTypeDecl, hasterms: boolean, etag: AdditionalTypeDeclTag) {
        const sinfo = this.peekToken().getSourceInfo();

        this.ensureToken(TokenStrings.IdentifierName, "datatype member entity declaration");
        const ename = this.parseIdentifierAsNamespaceOrTypeName();

        if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterNames)) {
            if(this.env.currentNamespace.checkDeclNameClashType(ename, false)) {
                this.recordErrorGeneral(sinfo, `Collision between type and other names -- ${ename}`);
            }

            const tdecl = new DatatypeMemberEntityTypeDecl(this.env.currentFile, sinfo, attributes, this.env.currentNamespace.fullnamespace, ename, etag, parenttype);
            
            parenttype.associatedMemberEntityDecls.push(tdecl);
            this.env.currentNamespace.typedecls.push(tdecl);

            this.env.currentNamespace.declaredNames.add(ename);
            this.env.currentNamespace.declaredTypeNames.push({name: ename, hasterms: hasterms});

            this.scanOverCodeParenSet(SYM_lbrace, SYM_rbrace);
        }
        else {
            const tdecl = this.env.currentNamespace.typedecls.find((td) => td.name === ename);
            assert(tdecl !== undefined && (tdecl instanceof DatatypeMemberEntityTypeDecl), "Failed to find datatype entry type");

            if(parenttype.terms.length !== 0) {
                tdecl.terms.push(...parenttype.terms);
            }

            tdecl.provides.push(new NominalTypeSignature(parenttype.sinfo, undefined, parenttype, parenttype.terms.map((term) => new TemplateTypeSignature(SourceInfo.implicitSourceInfo(), term.name))));

            if(this.testFollows(SYM_lbrace, TokenStrings.IdentifierName, SYM_colon)) {
                const fields = this.parseListOf<MemberFieldDecl>("datatype member entity", SYM_lbrace, SYM_rbrace, SYM_coma, () => {
                    const mfinfo = this.peekToken().getSourceInfo();

                    this.ensureToken(TokenStrings.IdentifierName, "datatype POD member field");
                    const name = this.parseIdentifierAsStdVariable();
                    this.ensureAndConsumeTokenIf(SYM_colon, "datatype POD member field");

                    const ttype = this.parseStdTypeSignature();
                    return new MemberFieldDecl(this.env.currentFile, mfinfo, [], name, ttype, undefined, false);
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

            tdecl = new DatatypeTypeDecl(this.env.currentFile, sinfo, attributes, this.env.currentNamespace.fullnamespace, dname, etag);
            this.env.currentNamespace.typedecls.push(tdecl);

            this.env.currentNamespace.declaredNames.add(dname);
            this.env.currentNamespace.declaredTypeNames.push({name: dname, hasterms: hasTerms});

            this.scanOverCodeTo(KW_of, SYM_amp, SYM_semicolon);
        }
        else {
            const ddecl = this.env.currentNamespace.typedecls.find((td) => td.name === dname);
            assert(ddecl !== undefined && (ddecl instanceof DatatypeTypeDecl), "Failed to find datatype type");

            tdecl = ddecl as DatatypeTypeDecl;

            const terms = this.parseTypeTemplateTerms();
            if(terms.length !== 0) {
                tdecl.terms.push(...terms);
            }

            const provides = this.parseProvides();
            if(provides.length !== 0) {
                tdecl.provides.push(...provides);
            }

            if(this.testAndConsumeTokenIf(KW_using)) {
                if(this.testFollows(SYM_lbrace, TokenStrings.IdentifierName, SYM_colon)) {
                    const fields = this.parseListOf<MemberFieldDecl>("datatype member", SYM_lbrace, SYM_rbrace, SYM_coma, () => {
                        const mfinfo = this.peekToken().getSourceInfo();
    
                        this.ensureToken(TokenStrings.IdentifierName, "datatype POD member field");
                        const name = this.parseIdentifierAsStdVariable();
                        this.ensureAndConsumeTokenIf(SYM_colon, "datatype POD member field");
    
                        const ttype = this.parseStdTypeSignature();
                        return new MemberFieldDecl(this.env.currentFile, mfinfo, [], name, ttype, undefined, false);
                    });
    
                    tdecl.fields.push(...fields);
                }
                else {
                    this.parseOOPMembersCommonAll(false, undefined, new Set<string>(tdecl.terms.map((term) => term.name)), tdecl.invariants, tdecl.validates, tdecl.consts, tdecl.functions, tdecl.fields, tdecl.methods, undefined, undefined, undefined);
                    if(tdecl.functions.length !== 0 || tdecl.methods.length !== 0) {
                        this.recordErrorGeneral(sinfo, "Using component cannot include functions or methods");
                    }
                }
            }
        }

        if(this.testToken(KW_of) || this.testToken(SYM_amp) || this.testToken(SYM_semicolon)) {
            this.ensureAndConsumeTokenIf(KW_of, "datatype");
        }
        else {
            //missing something so skip to known position
            this.recordErrorGeneral(sinfo, "Missing clause in datatype declaration");
            this.scanOverCodeTo(SYM_amp, SYM_semicolon);
        }
        

        let firstMember = true;
        while (!this.testToken(SYM_semicolon) && !this.testToken(SYM_amp) && !this.testToken(TokenStrings.EndOfStream) && !this.testToken(TokenStrings.Recover)) {
            if(!firstMember) {
                this.ensureAndConsumeTokenAlways(SYM_bar, "datatype member");
            }
            firstMember = false;

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

            const tdecl = new TaskDecl(this.env.currentFile, sinfo, attributes, this.env.currentNamespace.fullnamespace, tname);
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

            const provides = this.parseProvides();
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

            while(this.testToken(KW_status) || this.testToken(KW_resource) || this.testToken(KW_env) || this.testToken(KW_event)) {
                if(this.testToken(KW_event)) {
                    if(tdecl.eventsInfo !== undefined) {
                        this.recordErrorGeneral(sinfo, "Cannot have multiple event sections");
                    }
    
                    this.consumeToken();
                    tdecl.eventsInfo = this.parseNominalType();
                }
                else if(this.testToken(KW_status)) {
                    if(tdecl.statusInfo !== undefined) {
                        this.recordErrorGeneral(sinfo, "Cannot have multiple status sections");
                    }

                    this.consumeToken();
                    tdecl.statusInfo = this.parseListOf<TypeSignature>("task status section", SYM_lbrack, SYM_rbrack, SYM_coma, () => this.parseNominalType());
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
                            const pp = this.parseConstExpression(undefined, new Set<string>());
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
                    tdecl.envVarRequirementInfo = this.parseListOf<EnvironmentVariableInformation>("task env section", SYM_lbrace, SYM_rbrace, SYM_coma, () => {
                        this.ensureToken(TokenStrings.CString, "task env section");
                        const ename = this.consumeTokenAndGetValue();

                        this.ensureAndConsumeTokenIf(SYM_colon, "task env section");
                        const ttype = this.parseStdTypeSignature();
                        
                        let exp: ConstantExpressionValue | undefined = undefined;
                        if(this.testAndConsumeTokenIf(SYM_eq)) {
                            exp = this.parseConstExpression(ttype, new Set<string>());
                        }

                        return new EnvironmentVariableInformation(ename, ttype, exp);
                    });
                }
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

            const boundtemplates = new Set<string>();
            const params: InvokeParameterDecl[] = this.parseInvokeDeclParameters(sinfo, false, boundtemplates);
        
            this.ensureAndConsumeTokenIf(SYM_colon, "api declaration");
            const resultInfo = this.parseReturnTypeSignature();

            const argNames = new Set<string>(params.map((param) => param.name));
            const cargs = params.map((param) => new LocalVariableDefinitionInfo(!param.isRefParam, param.name));

            const [preconds, postconds] = this.parsePreAndPostConditions(sinfo, argNames, new Set<string>(), new Set<string>(), true, true);
            const samples = this.parseSamples(sinfo, boundtemplates);
    
            let statusinfo: TypeSignature[] = [];
            let resouceinfo: ResourceInformation[] | "**" | "{}" | undefined = undefined;
            let envinfo: EnvironmentVariableInformation[] | undefined = undefined;
            while(this.testToken(KW_event) || this.testToken(KW_status) || this.testToken(KW_resource) || this.testToken(KW_env)) {
                if(this.testToken(KW_status)) {
                    if(statusinfo !== undefined) {
                        this.recordErrorGeneral(sinfo, "Cannot have multiple status sections");
                    }

                    this.consumeToken();
                    statusinfo = this.parseListOf<TypeSignature>("task status section", SYM_lbrack, SYM_rbrack, SYM_coma, () => this.parseNominalType());
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
                            const pp = this.parseConstExpression(undefined, new Set<string>());
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
                        this.ensureToken(TokenStrings.CString, "task env section");
                        const ename = this.consumeTokenAndGetValue();

                        this.ensureAndConsumeTokenIf(SYM_colon, "task env section");
                        const ttype = this.parseStdTypeSignature();

                        let exp: ConstantExpressionValue | undefined = undefined;
                        if(this.testAndConsumeTokenIf(SYM_eq)) {
                            exp = this.parseConstExpression(ttype, new Set<string>());
                        }

                        return new EnvironmentVariableInformation(ename, ttype, exp);
                    });
                }
            }

            if(statusinfo === undefined) {
                statusinfo = [];
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

        this.wellknownTypes.set(name, new NominalTypeSignature(tdecl.sinfo, undefined, tdecl, []));
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
            pp.loadWellKnownType("Bool");
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

    static test_parseSFunctionInFile(core: CodeFileInfo[], macrodefs: string[], code: string, fname: string): string | ParserError[] {
        let assembly = new Assembly();

        let registeredNamespaces = new Set<string>();
        const coreerrors = Parser.parsefiles(true, core, macrodefs, assembly, registeredNamespaces);
        const ferrors = Parser.parsefiles(false, [{srcpath: "main.bsq", filename: "main.bsq", contents: `declare namespace Main; ${code}`}], macrodefs, assembly, registeredNamespaces);
        
        if(coreerrors.length !== 0 || ferrors.length !== 0) {
            return [...coreerrors, ...ferrors];
        }

        const ns = assembly.getToplevelNamespace("Main") as NamespaceDeclaration;
        const sffdecl = ns.functions.find((f) => f.name === fname);

        return sffdecl !== undefined ? sffdecl.emit(new CodeFormatter()) : "**ERROR**";
    }

    static test_parseSFunctionInFilePlus(core: CodeFileInfo[], macrodefs: string[], ctxfiles: CodeFileInfo[], code: string, fname: string): string | ParserError[] {
        let assembly = new Assembly();

        let registeredNamespaces = new Set<string>();
        const coreerrors = Parser.parsefiles(true, core, macrodefs, assembly, registeredNamespaces);
        const ferrors = Parser.parsefiles(false, [...ctxfiles, {srcpath: "main.bsq", filename: "main.bsq", contents: code}], macrodefs, assembly, registeredNamespaces);
        
        if(coreerrors.length !== 0 || ferrors.length !== 0) {
            return [...coreerrors, ...ferrors];
        }

        const ns = assembly.getToplevelNamespace("Main") as NamespaceDeclaration;
        const sffdecl = ns.functions.find((f) => f.name === fname);

        return sffdecl !== undefined ? sffdecl.emit(new CodeFormatter()) : "**ERROR**";
    }
}

export { 
    Parser, ParserError
};
