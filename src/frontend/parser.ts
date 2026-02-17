
import assert from "node:assert";

import { VariableDefinitionInfo, ParserEnvironment, StandardScopeInfo } from "./parser_env.js";
import { AutoTypeSignature, DashResultTypeSignature, EListTypeSignature, ErrorTypeSignature, FormatPathTypeSignature, FormatStringTypeSignature, FullyQualifiedNamespace, LambdaParameterSignature, LambdaTypeSignature, NominalTypeSignature, TemplateTypeSignature, TypeSignature } from "./type.js";
import { AbortStatement, AbstractBodyImplementation, AccessEnumExpression, AccessNamespaceConstantExpression, AccessVariableExpression, ArgumentList, AbstractArgumentValue, AssertStatement, BinAddExpression, BinDivExpression, BinKeyEqExpression, BinKeyNeqExpression, BinMultExpression, BinSubExpression, BinderInfo, BlockStatement, BodyImplementation, BuiltinBodyImplementation, CallNamespaceFunctionExpression, ConstructorEListExpression, ConstructorLambdaExpression, DebugStatement, EmptyStatement, ErrorExpression, ErrorStatement, Expression, ExpressionBodyImplementation, ExpressionTag, ITest, ITestFail, ITestNone, ITestOk, ITestSome, ITestType, IfElifElseStatement, IfElseStatement, IfStatement, LiteralRegexExpression, LiteralSimpleExpression, LiteralNoneExpression, LiteralTypeDeclValueExpression, MapEntryConstructorExpression, MatchStatement, NamedArgumentValue, NumericEqExpression, NumericGreaterEqExpression, NumericGreaterExpression, NumericLessEqExpression, NumericLessExpression, NumericNeqExpression, ParseAsTypeExpression, PositionalArgumentValue, PostfixAsConvert, PostfixIsTest, PostfixOp, PostfixOperation, PredicateUFBodyImplementation, PrefixNegateOrPlusOpExpression, PrefixNotOpExpression, SpreadArgumentValue, StandardBodyImplementation, Statement, SwitchStatement, ValidateStatement, VariableAssignmentStatement, VariableDeclarationStatement, VariableInitializationStatement, VariableMultiAssignmentStatement, VariableMultiDeclarationStatement, VariableMultiInitializationStatement, SpecialConstructorExpression, ConstructorPrimaryExpression, PostfixAccessFromName, ReturnVoidStatement, ReturnSingleStatement, PostfixInvoke, KeyCompareEqExpression, KeyCompareLessExpression, ReturnMultiStatement, PostfixAccessFromIndex, AccessStaticFieldExpression, CallTypeFunctionExpression, LambdaInvokeExpression, ThisUpdateStatement, VarUpdateStatement, CallRefThisExpression, VoidRefCallStatement, CallRefSelfExpression, CallRefVariableExpression, CallRefInvokeExpression, PostfixAssignFields, ChkLogicExpression, RValueExpression, ITestGuard, ITestGuardSet, ITestBinderGuard, ITestSimpleGuard, ITestTypeGuard, PassingArgumentValue, LiteralStringExpression, LiteralCStringExpression, LiteralFormatStringExpression, LiteralFormatCStringExpression, LiteralFormatPathItemExpression, LiteralPathItemExpression, LiteralTypedFormatStringExpression, LiteralTypedStringExpression, LiteralTypedCStringExpression, LiteralTypedPathExpression, FormatStringComponent, FormatStringTextComponent, FormatStringArgComponent, LiteralTypedFormatCStringExpression, LiteralTypedPathFormatExpression, AccessEnvValueExpression, TaskAccessInfoExpression, InterpolateFormatExpression, PostfixSliceOperator, HoleExpression, LogicAndExpression, LogicOrExpression, TaskRunExpression, EnvironmentGenerationExpression, EmptyEnvironmentExpression, CurrentEnvironmentExpression, InitializeEnvironmentExpression, TaskMultiExpression, TaskAllExpression, TaskDashExpression, TaskDashAnyExpression, TaskRaceExpression, TaskRaceAnyExpression, APIInvokeExpression, AgentInvokeExpression, ChkLogicImpliesExpression, ChkLogicBaseExpression, BaseRValueExpression, ConditionalValueExpression, ShortCircuitAssignRHSExpressionFail, ShortCircuitAssignRHSExpressionReturn, CallTaskActionExpression, SelfUpdateStatement, TaskCheckAndHandleTerminationStatement, TaskStatusStatement, TaskYieldStatement, DispatchTaskStatement, DispatchPatternStatement, HoleStatement, HoleBodyImplementation, SkipArgumentValue } from "./body.js";
import { APIDecl, APIResultTypeDecl, AbstractNominalTypeDecl, AdditionalTypeDeclTag, Assembly, ConceptTypeDecl, ConstMemberDecl, DatatypeMemberEntityTypeDecl, DatatypeTypeDecl, DeclarationAttibute, EntityTypeDecl, EnumTypeDecl, EnvironmentVariableInformation, EventListTypeDecl, FunctionInvokeDecl, InternalConceptTypeDecl, InvariantDecl, InvokeTemplateTermDecl, InvokeTemplateTypeRestriction, InvokeTemplateTypeRestrictionClause, LambdaDecl, ListTypeDecl, MapEntryTypeDecl, MapTypeDecl, MemberFieldDecl, MethodDecl, NamespaceDeclaration, NamespaceFunctionDecl, NamespaceUsing, PostConditionDecl, PreConditionDecl, PrimitiveEntityTypeDecl, QueueTypeDecl, ResourceInformation, ResultTypeDecl, SetTypeDecl, StackTypeDecl, TaskActionDecl, TaskDecl, TaskMethodDecl, TypeFunctionDecl, TypeTemplateTermDecl, TypedeclTypeDecl, ValidateDecl, WELL_KNOWN_EVENTS_VAR_NAME, WELL_KNOWN_RETURN_VAR_NAME, SomeTypeDecl, OptionTypeDecl, TemplateTermDeclExtraTag, InvokeParameterDecl, OkTypeDecl, FailTypeDecl, APIErrorTypeDecl, APIRejectedTypeDecl, APIDeniedTypeDecl, APIFlaggedTypeDecl, APISuccessTypeDecl, InternalEntityTypeDecl, AbstractCollectionTypeDecl, TestAssociation, TaskConfiguration, AgentDecl } from "./assembly.js";
import { BuildLevel, CodeFileInfo, CodeFormatter, SourceInfo } from "./build_decls.js";
import { AllAttributes, CoreOnlyAttributes, KeywordStrings, KW__debug, KW_abort, KW_action, KW_agent, KW_api, KW_as, KW_assert, KW_chktest, KW_concept, KW_configs, KW_const, KW_datatype, KW_debug, KW_declare, KW_dispatch, KW_do, KW_elif, KW_else, KW_ensures, KW_entity, KW_enum, KW_env, KW_errtest, KW_event, KW_example, KW_fail, KW_false, KW_field, KW_fn, KW_function, KW_if, KW_inout, KW_invariant, KW_let, KW_match, KW_method, KW_namespace, KW_none, KW_of, KW_ok, KW_out, KW_out_q, KW_parallel, KW_pred, KW_predicate, KW_provides, KW_recursive, KW_recursive_q, KW_ref, KW_release, KW_requires, KW_resource, KW_return, KW_safety, KW_self, KW_sequential, KW_slice, KW_softcheck, KW_some, KW_spec, KW_status, KW_switch, KW_task, KW_Task, KW_test, KW_this, KW_true, KW_type, KW_under, KW_using, KW_validate, KW_var, KW_when, KW_yield, LeftScanParens, ParenSymbols, RightScanParens, SpaceFrontSymbols, SpaceRequiredSymbols, SpecialNominalTypes, SpecialPathFormatTypes, SpecialStringFormatTypes, StandardSymbols, SYM_amp, SYM_ampamp, SYM_arrow, SYM_at, SYM_atat, SYM_bang, SYM_bangeq, SYM_bangeqeq, SYM_bar, SYM_barbar, SYM_bigarrow, SYM_colon, SYM_coloncolon, SYM_coma, SYM_div, SYM_dot, SYM_dotdotdot, SYM_eq, SYM_eqeq, SYM_eqeqeq, SYM_gt, SYM_gteq, SYM_hash, SYM_HOLE, SYM_implies, SYM_langle, SYM_lbrace, SYM_lbrack, SYM_lparen, SYM_lparenbar, SYM_lt, SYM_lteq, SYM_minus, SYM_negate, SYM_plus, SYM_positive, SYM_question, SYM_questionat, SYM_rangle, SYM_rbrace, SYM_rbrack, SYM_rparen, SYM_rparenbar, SYM_semicolon, SYM_times, TaskConfigs, TermRestrictions } from "./parser_kw.js";

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
    NumberinoRational: "[LITERAL_NUMBERINO_RATIONAL]",

    AtDexNumber: "[LITERAL_ATDEX_NUMBER]",

    Nat: "[LITERAL_NAT]",
    Int: "[LITERAL_INT]",
    ChkNat: "[LITERAL_CHKNAT]",
    ChkInt: "[LITERAL_CHKINT]",
    Float: "[LITERAL_FLOAT]",
    Decimal: "[LITERAL_DECIMAL]",
    Rational: "[LITERAL_RATIONAL]",
    DecimalDegree: "[LITERAL_DECIMAL_DEGREE]",
    LatLong: "[LITERAL_LATLONG]",
    Complex: "[LITERAL_COMPLEX]",
    
    ByteBuffer: "[LITERAL_BYTEBUFFER]",
    UUIDValue: "[LITERAL_UUID]",
    ShaHashcode: "[LITERAL_SHA]",

    Byte: "[LITERAL_BYTE]",
    CChar: "[LITERAL_CCHAR]",
    UnicodeChar: "[LITERAL_UNICODECHAR]",

    String: "[LITERAL_STRING]",
    CString: "[LITERAL_EX_STRING]",
    FormatString: "[LITERAL_FORMAT_STRING]",
    FormatCString: "[LITERAL_FORMAT_EX_STRING]",

    Regex: "[LITERAL_REGEX]",
    PathItem: "[LITERAL_PATH_ITEM]",
    FormatPathItem: "[LITERAL_FORMAT_PATH_ITEM]",

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

    EndOfStream: "[EOS]"
};

const PRIMITIVE_ENTITY_TYPE_NAMES = [
    "None", "Bool", 
    "Nat", "Int", "ChkInt", "ChkNat", "Rational", "Float", "Decimal", "DecimalDegree", "LatLongCoordinate", "Complex",
    "ByteBuffer", "UUIDv4", "UUIDv7", "SHAContentHash", 
    "TZDateTime", "TAITime", "PlainDate", "PlainTime", "LogicalTime", "ISOTimestamp",
    "DeltaDateTime", "DeltaSeconds", "DeltaLogicalTime", "DeltaISOTimestamp",
    "Byte", "CChar", "UnicodeChar",
    "CCharBuffer", "UnicodeCharBuffer",
    "String", "CString",
    "Regex", "CRegex",
    "Path", "PathFragment", "Glob"
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
    private jsStrEnd: number;

    cline: number;
    linestart: number;
    
    tokens: Token[];
    errors: ParserError[];

    private advancePosition(epos: number) {
        this.jsStrPos += epos - this.jsStrPos;
    }

    private trylex(re: RegExp): string | null {
        re.lastIndex = this.jsStrPos;
        const mm = re.exec(this.input);
        if(mm === null) {
            return null;
        }
        else {
            return mm[0];
        }
    }

    private static readonly _s_whitespaceRe = new RegExp('\\s+', "y");    
    private trylexWSPlus(options: string[], suffix: RegExp): string | null {
        Lexer._s_whitespaceRe.lastIndex = this.jsStrPos;
        const mmpre = Lexer._s_whitespaceRe.exec(this.input);
        if(mmpre === null) {
            return null;
        }
        
        const mopt = options.find((opt) => this.input.startsWith(opt, this.jsStrPos + mmpre[0].length));
        if(mopt === undefined) {
            return null;
        }

        suffix.lastIndex = this.jsStrPos + mmpre[0].length + mopt.length;
        const mmsuf = suffix.exec(this.input);
        if(mmsuf === null) {
            return null;
        }

        return this.input.slice(this.jsStrPos, this.jsStrPos + mmpre[0].length + mopt.length + mmsuf[0].length);
    }

    constructor(iscore: boolean, srcfile: string, input: string, lstart: number, macrodefs: string[]) {
        this.iscore = iscore;
        this.srcfile = srcfile;
        this.macrodefs = macrodefs;
        this.scanmode = [LexerStateScanMode.Enabled];

        this.input = input;
        this.jsStrPos = 0;
        this.jsStrEnd = this.input.length;

        this.cline = lstart + 1;
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
    
    private tryLexWS(): boolean {
        const arop = this.trylexWSPlus(SpaceRequiredSymbols, Lexer._s_whitespaceRe);
        if (arop !== null) {
            return false;
        }

        const frop = this.trylexWSPlus(SpaceFrontSymbols, /[^0-9+-]/y);
        if (frop !== null) {
            return false;
        }

        const m = this.trylex(Lexer._s_whitespaceRe);
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
            this.updatePositionInfo(this.jsStrPos, this.jsStrEnd);
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
            this.recordLexTokenWData(jepos, TokenStrings.DocComment, this.input.slice(this.jsStrPos, jepos));
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
            
            this.updatePositionInfo(this.jsStrPos, this.jsStrEnd);
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

    private static readonly _s_nonzeroIntValNoSign = '[1-9][0-9]*';
    private static readonly _s_nonzeroIntVal = `[+-]?${Lexer._s_nonzeroIntValNoSign}`;
    private static readonly _s_intValueNoSign = `(0|${Lexer._s_nonzeroIntValNoSign})`;
    private static readonly _s_intValue = `(0|[+]0|${Lexer._s_nonzeroIntVal})`;

    private static readonly _s_floatValueNoSign = '[0-9]+[.][0-9]+([eE][-+]?[0-9]+)?';
    private static readonly _s_floatValue = `[+-]?${Lexer._s_floatValueNoSign}([eE][-+]?[0-9]+)?`;

    private static readonly _s_floatSimpleValueNoSign = '[0-9]+[.][0-9]+';
    private static readonly _s_floatSimpleValue = `[+-]?${Lexer._s_floatSimpleValueNoSign}`;

    private static readonly _s_idexValue = new RegExp(`@(${Lexer._s_intValue})`, "y");

    private static readonly _s_intNumberinoRe = new RegExp(`${Lexer._s_intValue}`, "y");
    private static readonly _s_floatNumberinoRe = new RegExp(`${Lexer._s_floatValue}`, "y");
    private static readonly _s_rationalNumberinoRe = new RegExp(`(${Lexer._s_intValue})/(${Lexer._s_nonzeroIntValNoSign})`, "y");

    private static readonly _s_intRe = new RegExp(`(${Lexer._s_intValue})i`, "y");
    private static readonly _s_natRe = new RegExp(`(${Lexer._s_intValue})n`, "y");
    private static readonly _s_chkintRe = new RegExp(`ChkInt::npos|(${Lexer._s_intValue})I`, "y");
    private static readonly _s_chknatRe = new RegExp(`ChkNat::npos|(${Lexer._s_intValue})N`, "y");

    private static readonly _s_floatRe = new RegExp(`(${Lexer._s_floatValue})f`, "y");
    private static readonly _s_decimalRe = new RegExp(`(${Lexer._s_floatValue})d`, "y");
    private static readonly _s_rationalRe = new RegExp(`(${Lexer._s_intValue})(/(${Lexer._s_nonzeroIntValNoSign}))?R`, "y");
    private static readonly _s_complexRe = new RegExp(`(${Lexer._s_floatValue})[+-](${Lexer._s_floatValueNoSign})j`, "y");

    private static readonly _s_decimalDegreeRe = new RegExp(`(${Lexer._s_floatSimpleValue})dd`, "y");
    private static readonly _s_latlongRe = new RegExp(`(${Lexer._s_floatSimpleValue})lat[+-]${Lexer._s_floatSimpleValueNoSign}long`, "y");
    
    private static readonly _s_logicaltimeRe = new RegExp(`(${Lexer._s_intValue})l`, "y");

    private static readonly _s_deltasecondsRE = new RegExp(`[+-](${Lexer._s_floatValueNoSign})ds`, "y");
    private static readonly _s_deltalogicaltimeRE = new RegExp(`[+-](${Lexer._s_intValueNoSign})dl`, "y");

    private static readonly _s_zerodenomRationalNumberinoRe = new RegExp(`(${Lexer._s_intValue})/0`, "y");
    private static readonly _s_zerodenomRationalRe = new RegExp(`(${Lexer._s_intValue})/0R`, "y");

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

    private tryLexIdexToken(): boolean {
        const midex = this.trylex(Lexer._s_idexValue);
        if(midex !== null) {
            this.recordLexTokenWData(this.jsStrPos + midex.length, TokenStrings.AtDexNumber, midex);
            return true;
        }
        return false;
    }

    private tryLexFloatCompositeLikeToken(): boolean {
        const mcomplex = this.trylex(Lexer._s_complexRe);
        if(mcomplex !== null) {
            this.recordLexTokenWData(this.jsStrPos + mcomplex.length, TokenStrings.Complex, mcomplex);
            return true;
        }

        const mlatlong = this.trylex(Lexer._s_latlongRe);
        if(mlatlong !== null) {
            this.recordLexTokenWData(this.jsStrPos + mlatlong.length, TokenStrings.LatLong, mlatlong);
            return true;
        }

        return false;
    }

    private tryLexFloatLikeToken(): boolean {
        const mdecimaldegree = this.trylex(Lexer._s_decimalDegreeRe);
        if(mdecimaldegree !== null) {
            this.recordLexTokenWData(this.jsStrPos + mdecimaldegree.length, TokenStrings.DecimalDegree, mdecimaldegree);
            return true;
        }

        const mdeltaseconds = this.trylex(Lexer._s_deltasecondsRE);
        if(mdeltaseconds !== null) {
            this.recordLexTokenWData(this.jsStrPos + mdeltaseconds.length, TokenStrings.DeltaSeconds, mdeltaseconds);
            return true;
        }

        const mdecimal = this.trylex(Lexer._s_decimalRe);
        if(mdecimal !== null) {
            this.recordLexTokenWData(this.jsStrPos + mdecimal.length, TokenStrings.Decimal, mdecimal);
            return true;
        }

        const mfloat = this.trylex(Lexer._s_floatRe);
        if(mfloat !== null) {
            this.recordLexTokenWData(this.jsStrPos + mfloat.length, TokenStrings.Float, mfloat);
            return true;
        }

        const unumberino = this.trylex(Lexer._s_floatNumberinoRe);
        if(unumberino !== null) {
            this.recordLexTokenWData(this.jsStrPos + unumberino.length, TokenStrings.NumberinoFloat, unumberino);
            return true;
        }

        return false;
    }

    private tryLexIntegralCompositeLikeToken(): boolean {
        const mzerodenom = this.trylex(Lexer._s_zerodenomRationalRe);
        if(mzerodenom !== null) {
            this.pushError(new SourceInfo(this.cline, this.linestart, this.jsStrPos, mzerodenom.length), "Zero denominator in rational number");
            this.recordLexTokenWData(this.jsStrPos + mzerodenom.length, TokenStrings.Rational, mzerodenom);
            return true;
        }

        const mrational = this.trylex(Lexer._s_rationalRe);
        if(mrational !== null) {
            this.recordLexTokenWData(this.jsStrPos + mrational.length, TokenStrings.Rational, mrational);
            return true;
        }

        const mzerodenomtagged = this.trylex(Lexer._s_zerodenomRationalNumberinoRe);
        if(mzerodenomtagged !== null) {
            this.pushError(new SourceInfo(this.cline, this.linestart, this.jsStrPos, mzerodenomtagged.length), "Zero denominator in rational number");
            this.recordLexTokenWData(this.jsStrPos + mzerodenomtagged.length, TokenStrings.NumberinoRational, mzerodenomtagged);
            return true;
        }

        const mnumberino = this.trylex(Lexer._s_rationalNumberinoRe);
        if(mnumberino !== null) {
            this.recordLexTokenWData(this.jsStrPos + mnumberino.length, TokenStrings.NumberinoRational, mnumberino);
            return true;
        }

        return false;
    }

    private tryLexIntegralLikeToken(): boolean {
        const mlogical = this.trylex(Lexer._s_logicaltimeRe);
        if(mlogical !== null) {
            this.recordLexTokenWData(this.jsStrPos + mlogical.length, TokenStrings.LogicalTime, mlogical);
            return true;
        }

        const m_deltalogical = this.trylex(Lexer._s_deltalogicaltimeRE);
        if(m_deltalogical !== null) {
            this.recordLexTokenWData(this.jsStrPos + m_deltalogical.length, TokenStrings.DeltaLogicalTime, m_deltalogical);
            return true;
        }
        
        const mint = this.trylex(Lexer._s_intRe);
        if(mint !== null) {
            this.recordLexTokenWData(this.jsStrPos + mint.length, TokenStrings.Int, mint);
            return true;
        }

        const mnat = this.trylex(Lexer._s_natRe);
        if(mnat !== null) {
            this.recordLexTokenWData(this.jsStrPos + mnat.length, TokenStrings.Nat, mnat);
            return true;
        }

        const mchkint = this.trylex(Lexer._s_chkintRe);
        if(mchkint !== null) {
            this.recordLexTokenWData(this.jsStrPos + mchkint.length, TokenStrings.ChkInt, mchkint);
            return true;
        }

        const mchknat = this.trylex(Lexer._s_chknatRe);
        if(mchknat !== null) {
            this.recordLexTokenWData(this.jsStrPos + mchknat.length, TokenStrings.ChkNat, mchknat);
            return true;
        }

        const mnumberino = this.trylex(Lexer._s_intNumberinoRe);
        if(mnumberino !== null) {
            this.recordLexTokenWData(this.jsStrPos + mnumberino.length, TokenStrings.NumberinoInt, mnumberino);
            return true;
        }

        return false;
    }

    private tryLexNumberLikeToken(): boolean {
        this.checkRedundantSigns();

        const idex = this.tryLexIdexToken();
        if(idex) {
            return true;
        }

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

    private static _s_byteRe = new RegExp('0x[0-9a-fA-F]{1,2}', "y");
    private tryLexByte(): boolean {
        const m = this.trylex(Lexer._s_byteRe);
        if(m !== null) {
            this.recordLexTokenWData(this.jsStrPos + m.length, TokenStrings.Byte, m);
            return true;
        }

        return false;
    }

    private static _s_bytebufferRe = new RegExp('0x\\[\\]|0x\\[[0-9a-fA-F]{1,2}(,[0-9a-fA-F]{1,2})*\\]', "y");
    private tryLexByteBuffer(): boolean {
        const m = this.trylex(Lexer._s_bytebufferRe);
        if(m !== null) {
            this.recordLexTokenWData(this.jsStrPos + m.length, TokenStrings.ByteBuffer, m);
            return true;
        }

        return false;
    }

    private static _s_uuidRe = new RegExp('uuid[47]\\{[a-fA-F0-9]{8}-[a-fA-F0-9]{4}-[a-fA-F0-9]{4}-[a-fA-F0-9]{4}-[a-fA-F0-9]{12}\\}', "y");
    private tryLexUUID(): boolean {
        const m = this.trylex(Lexer._s_uuidRe);
        if(m !== null) {
            this.recordLexTokenWData(this.jsStrPos + m.length, TokenStrings.UUIDValue, m);
            return true;
        }

        return false;
    }

    private static _s_shaRe = new RegExp('sha3\\{[a-fA-F0-9]{64}\\}', "y");
    private tryLexHashCode(): boolean {
        const m = this.trylex(Lexer._s_shaRe);
        if(m !== null) {
            this.recordLexTokenWData(this.jsStrPos + m.length, TokenStrings.ShaHashcode, m);
            return true;
        }

        return false;
    }

    private tryLexUnicodeChar(): boolean {
        let ncpos = this.jsStrPos;
        if(!this.input.startsWith('c"', this.jsStrPos)) {
            return false;
        }
        ncpos += 2;

        let jepos = this.input.indexOf('"', ncpos);
        if(jepos === -1) {
            this.pushError(new SourceInfo(this.cline, this.linestart, this.jsStrPos, this.jsStrEnd - this.jsStrPos), "Unterminated UnicodeChar literal");
            this.recordLexToken(this.jsStrEnd, TokenStrings.Error);

            return true;
        }
        else {
            // Defer checking for single character to type checker
            jepos++;
            let strval = this.input.slice(this.jsStrPos, jepos);
            
            this.updatePositionInfo(this.jsStrPos, jepos);
            this.recordLexTokenWData(jepos, TokenStrings.UnicodeChar, strval);
            return true;
        }
    }
    
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
            let strval = this.input.slice(this.jsStrPos, jepos);

            this.updatePositionInfo(this.jsStrPos, jepos);
            this.recordLexTokenWData(jepos, istemplate ? TokenStrings.FormatString : TokenStrings.String, strval);
            return true;
        }
    }

    static _s_validCStringChars = /^[ -~\t\n]*$/;
    private tryLexCChar(): boolean {
        let ncpos = this.jsStrPos;
        if(!this.input.startsWith('c\'', this.jsStrPos)) { // Byte char
            return false;
        }
        ncpos += 2;

        let jepos = this.input.indexOf('\'', ncpos);
        if(jepos === -1) {
            this.pushError(new SourceInfo(this.cline, this.linestart, this.jsStrPos, this.jsStrEnd - this.jsStrPos), "Unterminated CChar literal");
            this.recordLexToken(this.jsStrEnd, TokenStrings.Error);

            return true;
        }
        else {
            const mstr = this.input.slice(ncpos, jepos);
            if(!Lexer._s_validCStringChars.test(mstr)) {
                this.pushError(new SourceInfo(this.cline, this.linestart, this.jsStrPos, jepos - this.jsStrPos), "Invalid chacaters in CChar literal");
                this.recordLexToken(jepos, TokenStrings.Error);

                return true;
            }

            if((jepos - ncpos) > 1) {
                this.pushError(new SourceInfo(this.cline, this.linestart, this.jsStrPos, this.jsStrEnd - this.jsStrPos), "More than one character in CChar literal");
                this.recordLexToken(this.jsStrEnd, TokenStrings.Error);
    
                return true;
            }

            jepos++;
            let strval = this.input.slice(this.jsStrPos, jepos);

            this.updatePositionInfo(this.jsStrPos, jepos);
            this.recordLexTokenWData(jepos, TokenStrings.CChar, strval);
            return true;
        }
    }

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
            let strval = this.input.slice(this.jsStrPos, jepos);

            this.updatePositionInfo(this.jsStrPos, jepos);
            this.recordLexTokenWData(jepos, istemplate ? TokenStrings.FormatCString : TokenStrings.CString, strval);
            return true;
        }
    }

    private tryLexCharLike() {
        const bb = this.tryLexByte();
        if(bb) {
            return true;
        }

        const cc = this.tryLexCChar();
        if(cc) {
            return true;
        }

        const uc = this.tryLexUnicodeChar();
        if(uc) {
            return true;
        }
        return false;
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

        return false;
    }

    private static _s_validRegexChars = /([!-.0-~]|\s)+/;
    private tryLexRegex() {
        if(!this.input.startsWith("/", this.jsStrPos)) {
            return false;
        }

        let jepos = this.input.indexOf("/", this.jsStrPos + 1);
        if(jepos === -1) {
            this.pushError(new SourceInfo(this.cline, this.linestart, this.jsStrPos, this.jsStrEnd - this.jsStrPos), "Unterminated Regex literal");
            this.recordLexToken(this.jsStrEnd, TokenStrings.Error);

            return true;
        }
        else {
            const mstr = this.input.slice(this.jsStrPos + 1, jepos);
            if(!Lexer._s_validRegexChars.test(mstr)) {
                this.pushError(new SourceInfo(this.cline, this.linestart, this.jsStrPos, jepos - this.jsStrPos), "Invalid characters in (or empty) Regex literal");
                this.recordLexToken(jepos, TokenStrings.Error);

                return true;
            }

            jepos++;
            if(this.input.startsWith("c", jepos) || this.input.startsWith("p", jepos)) {
                jepos++;
            }

            let strval = this.input.slice(this.jsStrPos, jepos);

            this.updatePositionInfo(this.jsStrPos, jepos);
            this.recordLexTokenWData(jepos, TokenStrings.Regex, strval);
            return true;
        }
    }

    private static _s_pathRe = /[$]?[gf]?\\[ !-Z^-~\[\]]\\/y;
    private tryLexPath() {
        let ncpos = this.jsStrPos;
        let istemplate = false;
        if(this.input.startsWith("$", this.jsStrPos)) {
            ncpos += 1;
            istemplate = true;
        }

        Lexer._s_pathRe.lastIndex = ncpos;
        const mpth = Lexer._s_pathRe.exec(this.input);
        if(mpth !== null) {
            let jepos = ncpos + mpth[0].length;
            let pthval = mpth[0];
            
            this.updatePositionInfo(this.jsStrPos, jepos);
            this.recordLexTokenWData(jepos, istemplate ? TokenStrings.FormatPathItem : TokenStrings.PathItem, pthval);
            return true;
        }

        return false;
    }

    private static _s_datevalue = '([0-9]{4})-([0-9]{2})-([0-9]{2})';
    private static _s_timevalue = '([0-9]{2}):([0-9]{2}):([0-9]{2})';
    private static _s_tzvalue = '((\{[a-zA-Z0-9/, _-]+\})|[A-Z]+)';

    private static _s_datatimeRE = new RegExp(`${Lexer._s_datevalue}T${Lexer._s_timevalue}@${Lexer._s_tzvalue}`, "y");
    private static _s_taitimeRE = new RegExp(`${Lexer._s_datevalue}T${Lexer._s_timevalue}`, "y");
    private static _s_plaindateRE = new RegExp(`${Lexer._s_datevalue}`, "y");
    private static _s_plaintimeRE = new RegExp(`${Lexer._s_timevalue}`, "y");
    private static _s_timestampRE = new RegExp(`${Lexer._s_datevalue}T${Lexer._s_timevalue}[.]([0-9]{3})Z`, "y");

    private tryLexDateTime() {
        const mdt = this.trylex(Lexer._s_datatimeRE);
        if(mdt !== null) {
            this.recordLexTokenWData(this.jsStrPos + mdt.length, TokenStrings.TZDateTime, mdt);
            return true;
        }

        const mutcdt = this.trylex(Lexer._s_taitimeRE);
        if(mutcdt !== null) {
            this.recordLexTokenWData(this.jsStrPos + mutcdt.length, TokenStrings.TAITime, mutcdt);
            return true;
        }

        const mts = this.trylex(Lexer._s_timestampRE);
        if(mts !== null) {
            this.recordLexTokenWData(this.jsStrPos + mts.length, TokenStrings.Timestamp, mts);
            return true;
        }

        const mpd = this.trylex(Lexer._s_plaindateRE);
        if(mpd !== null) {
            this.recordLexTokenWData(this.jsStrPos + mpd.length, TokenStrings.PlainDate, mpd);
            return true;
        }

        const mpt = this.trylex(Lexer._s_plaintimeRE);
        if(mpt !== null) {
            this.recordLexTokenWData(this.jsStrPos + mpt.length, TokenStrings.PlainTime, mpt);
            return true;
        }

        return false;
    }

    private static _s_deltadatevalue = '([0-9]{1,4})-([0-9]{1,10})-([0-9]{1,10})';
    private static _s_deltatimevalue = '([0-9]{1,10}):([0-9]{1,10}):([0-9]{1,10})';

    private static _s_datetimeDeltaRE = new RegExp(`[+-]${Lexer._s_deltadatevalue}T${Lexer._s_deltatimevalue}?`, "y");
    private static _s_plaindateDeltaRE = new RegExp(`[+-]${Lexer._s_deltadatevalue}`, "y");
    private static _s_plaintimeDeltaRE = new RegExp(`[+-]${Lexer._s_deltatimevalue}`, "y");
    private static _s_timestampDeltaRE = new RegExp(`[+-]${Lexer._s_deltadatevalue}T${Lexer._s_deltatimevalue}[.]([0-9]{18})Z`, "y");

    private tryLexDateTimeDelta() {
        const mdt = this.trylex(Lexer._s_datetimeDeltaRE);
        if(mdt !== null) {
            this.recordLexTokenWData(this.jsStrPos + mdt.length, TokenStrings.DeltaDateTime, mdt);
            return true;
        }

        const mts = this.trylex(Lexer._s_timestampDeltaRE);
        if(mts !== null) {
            this.recordLexTokenWData(this.jsStrPos + mts.length, TokenStrings.DeltaTimestamp, mts);
            return true;
        }

        const mpd = this.trylex(Lexer._s_plaindateDeltaRE);
        if(mpd !== null) {
            this.recordLexTokenWData(this.jsStrPos + mpd.length, TokenStrings.DeltaDateTime, mpd + "T00:00:00");
            return true;
        }

        const mpt = this.trylex(Lexer._s_plaintimeDeltaRE);
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
        const spaceop = this.trylexWSPlus(SpaceRequiredSymbols, Lexer._s_whitespaceRe);
        const frontop = this.trylexWSPlus(SpaceFrontSymbols, /[^0-9+-]/y);
        if(spaceop !== null) {
            const realstr = " " + spaceop.trim() + " ";

            this.recordLexToken(this.jsStrPos + spaceop.length, realstr);
            return true; 
        }
        else if(frontop !== null) {
            const realstr = " " + frontop.trim().slice(0, -1);

            this.recordLexToken(this.jsStrPos + frontop.length - 1, realstr);
            return true; 
        }
        else {
            const mm = ParenSymbols.find((value) => this.input.startsWith(value, this.jsStrPos)) || StandardSymbols.find((value) => this.input.startsWith(value, this.jsStrPos));
            if(mm !== undefined) {
                this.recordLexToken(this.jsStrPos + mm.length, mm);
                return true;
            }

        
            return false;
        }
    }

    private tryLexAttribute() {
        const mm = AllAttributes.find((value) => this.trylex(new RegExp(value + "[[ \n\t]", "y")) !== null);
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

            this.recordLexTokenWData(jepos, TokenStrings.Attribute, this.input.slice(this.jsStrPos, jepos));
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

    private static readonly _s_identiferName = new RegExp('[$]?[_a-zA-Z][_a-zA-Z0-9]*', "y");
    private tryLexName(): boolean {
        const identifiermatch = this.trylex(Lexer._s_identiferName);
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

    private static readonly _s_macroRe = new RegExp('(#if[ ]+([A-Z][_A-Z0-9]*)|#else|#endif)', "y");
    tryLexMacroOp(): [string, string | undefined] | undefined {
        const m = this.trylex(Lexer._s_macroRe);
        if (m === null) {
            return undefined;
        }

        this.updatePositionInfo(this.jsStrPos, this.jsStrPos + m.length);
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
                else if(this.tryLexCharLike()) {
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
                else if (this.tryLexPath() || this.tryLexRegex()) {
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
                const tkk = cstate.tokens[cstate.epos];
                return new Token(tkk.line, tkk.column, tkk.pos, tkk.span, TokenStrings.Recover, undefined);
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
                pscount = pscount - 1;
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
                pscount = pscount - 1;
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

    //scan until we find a balanaced xxx { ... } declaration -- eat the parens
    private scanOverBraceDelimitedDeclaration(allowcorebi?: boolean) {
        let pscount = 0;

        let tok = this.peekToken();
        while (tok.kind !== TokenStrings.EndOfStream && tok.kind !== TokenStrings.Recover) {
            if(tok.kind === SYM_rbrace && pscount === 1) {
                this.consumeToken();
                return;
            }

            if(allowcorebi && pscount === 0) {
                //check for the end of a builtin method "= @ID;"
                if(this.peekTokenKind() === SYM_eq && this.peekTokenKind(1) === SYM_at && this.peekTokenKind(2) === TokenStrings.IdentifierName && this.peekTokenKind(3) === SYM_semicolon) {
                    this.consumeToken();
                    this.consumeToken();
                    this.consumeToken();
                    this.consumeToken();

                    return;
                }
            }

            if (tok.kind === SYM_lbrace) {
                pscount = pscount + 1;
            }
            else if (tok.kind === SYM_rbrace) {
                pscount = pscount - 1;
            }
            else {
                //nop
            }

            this.consumeToken();
            tok = this.peekToken();
        }
    }

    //scan to and consume the end token
    private scanOverSemiDelimitedDeclaration() {
        this.scanToKWOptsInDeclaration(SYM_semicolon);
        this.testAndConsumeTokenIf(SYM_semicolon);
    }

    //given some possible follow kw/sym token scan until we find one of them
    private scanToKWOptsInDeclaration(...kwopts: string[]) {
        let pscount = 0;

        let tok = this.peekToken();
        while (tok.kind !== TokenStrings.EndOfStream && tok.kind !== TokenStrings.Recover) {
            if(kwopts.includes(tok.kind) && pscount === 0) {
                break;
            }

            if (LeftScanParens.indexOf(tok.kind) !== -1) {
                pscount = pscount + 1;
            }
            else if (RightScanParens.indexOf(tok.kind) !== -1) {
                pscount = pscount - 1;
            }
            else {
                //nop
            }

            this.consumeToken();
            tok = this.peekToken();
        }
    }

    private FA_TSigLookup(sinfo: SourceInfo, fmtstr: string): TypeSignature | undefined {
        //
        //TODO: A temp kludge to extract type info from the format string (can only be nominal without templates for now)
        //

        const parts = fmtstr.split("::");
        const corens = this.env.assembly.getCoreNamespace();
        const rns = this.env.currentNamespace;
        const tlns = this.env.assembly.getToplevelNamespace(rns.topnamespace);

        if(parts.length === 1) {
            const cnst = corens.typedecls.find((v) => v.name === parts[0]);
            const nnst = rns.typedecls.find((v) => v.name === parts[0]);
            const tnst = tlns !== undefined ? tlns.typedecls.find((v) => v.name === parts[0]) : undefined;

            if(cnst !== undefined) {
                return new NominalTypeSignature(sinfo, undefined, cnst, []);
            }
            else if(nnst !== undefined) {
                return new NominalTypeSignature(sinfo, undefined, nnst, []);
            }
            else if(tnst !== undefined) {
                return new NominalTypeSignature(sinfo, undefined, tnst, []);
            }
            else {
                return undefined;
            }
        }
        else if (tlns !== undefined) {
            let tns = tlns as NamespaceDeclaration;
            for(let i = 0; i < parts.length - 1; ++i) {
                tns = tns.subns.find((v) => v.name === parts[i]) as NamespaceDeclaration;
                if(tns === undefined) {
                    return undefined;
                }
            }
            
            const tnst = tns.typedecls.find((v) => v.name === parts[parts.length - 1]);
            if(tnst !== undefined) {
                return new NominalTypeSignature(sinfo, undefined, tnst, []);
            }
            else {
                return undefined;
            }
        }
        else {
            return undefined;
        }
    }

    private processFormatArguments(contents: string, sinfo: SourceInfo): FormatStringComponent[] {
        const parts = contents.split(/(\$\{[0-9a-zA-Z:]+\})/);

        return parts.map((part) => {
            if(!part.startsWith("${")) {
                return new FormatStringTextComponent(part);
            }
            else {
                const tpos = part.indexOf(":");
                if(tpos === -1) {
                    const argpos = part.slice(2, part.length - 1);
                    return new FormatStringArgComponent(argpos, new AutoTypeSignature(sinfo));
                }
                else {
                    const argpos = part.slice(2, tpos);
                    const fmtstr = part.slice(tpos + 1, part.length - 1);
                    
                    const fsig = this.FA_TSigLookup(sinfo, fmtstr);
                    if(fsig !== undefined) {
                        return new FormatStringArgComponent(argpos, fsig);
                    }
                    else {
                        this.recordErrorGeneral(sinfo, `Unable to resolve type signature "${fmtstr}" in format string argument`);
                        return new FormatStringArgComponent(argpos, new AutoTypeSignature(sinfo));
                    }    
                }
            }
        });
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
    // 2) I'll look in my (exact) namespce for the name
    // 3) The current TOP-LEVEL namespace is always in scope and implicit
    // 4) All other namespaces must be explicitly scoped -- so if I am in a sub-namespace I can either fully scope a name or drop the top-level name ONLY
    //
    ////////

    private identifierResolvesAsScopedConstOrFunction(name: string): [NamespaceDeclaration, "isfunction" | "isconstant"] | undefined {
        const coredecl = this.env.assembly.getCoreNamespace();
        if(coredecl.declaredFunctionNames.has(name)) {
            return [coredecl, "isfunction"];
        }
        if(coredecl.declaredConstNames.has(name)) {
            return [coredecl, "isconstant"];
        }

        const currnsdecl = this.env.currentNamespace
        if(currnsdecl.declaredFunctionNames.has(name)) {
            return [currnsdecl, "isfunction"];
        }
        if(currnsdecl.declaredConstNames.has(name)) {
            return [currnsdecl, "isconstant"];
        }
        
        const topnsdecl = this.env.assembly.getToplevelNamespace(this.env.currentNamespace.topnamespace) as NamespaceDeclaration;
        if(topnsdecl.declaredFunctionNames.has(name)) {
            return [topnsdecl, "isfunction"];
        }
        if(topnsdecl.declaredConstNames.has(name)) {
            return [topnsdecl, "isconstant"];
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
                else if(tsroot === "APIResult" && (ttname === "Error" || ttname === "Rejected" || ttname === "Denied" || ttname === "Flagged" || ttname === "Success")) {
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

        if(this.testToken(TokenStrings.Template)) {
            const tt = this.consumeTokenAndGetValue();
            return {altScope: undefined, nsScope: this.env.currentNamespace, typeTokens: [{ tname: tt, tterms: [] }]};
        }

        const nsroot = this.peekTokenData();
        if(!/^[A-Z][_a-zA-Z0-9]+/.test(nsroot)) {
            return undefined; //not a valid namespace or type name
        }

        const coredecl = this.env.assembly.getCoreNamespace();
        const topdecl = this.env.assembly.getToplevelNamespace(this.env.currentNamespace.topnamespace) as NamespaceDeclaration;

        //<---- First check if the name/namespace is in Core ---->
        if (nsroot === "Core") {
            this.consumeToken();
            
            const ach = this.parseIdentifierAccessChainHelper(this.testToken(SYM_coloncolon), coredecl, ["Core"]);
            return ach !== undefined ? {altScope: undefined, nsScope: ach.nsScope, typeTokens: ach.typeTokens} : undefined;
        }
        else if(coredecl.subns.find((ns) => ns.name === nsroot) !== undefined) {
            const ach = this.parseIdentifierAccessChainHelper(false, coredecl, []);
            return ach !== undefined ? {altScope: ach.scopeTokens, nsScope: ach.nsScope, typeTokens: ach.typeTokens} : undefined;
        }
        else if(coredecl.declaredNames.has(nsroot)) {
            const ach = this.parseIdentifierAccessChainHelper(false, coredecl, []);
            return ach !== undefined ? {altScope: ach.scopeTokens, nsScope: ach.nsScope, typeTokens: ach.typeTokens} : undefined;
        }
        //<---- Now see if we are explicitly refering to the current ROOT ---->
        else if(topdecl.name === nsroot) {
            this.consumeToken();
            
            const ach = this.parseIdentifierAccessChainHelper(this.testToken(SYM_coloncolon), topdecl, [nsroot]);
            return ach !== undefined ? {altScope: undefined, nsScope: ach.nsScope, typeTokens: ach.typeTokens} : undefined;
        }
        //<---- See if the name/namespace is in the current namespace (implicitly nested)---->
        else if(this.env.currentNamespace.subns.find((ns) => ns.name === nsroot) !== undefined) {
            const ach = this.parseIdentifierAccessChainHelper(false, this.env.currentNamespace, []);
            return ach !== undefined ? {altScope: ach.scopeTokens, nsScope: ach.nsScope, typeTokens: ach.typeTokens} : undefined;
        }
        else if(this.env.currentNamespace.declaredNames.has(nsroot)) {
            const ach = this.parseIdentifierAccessChainHelper(false, this.env.currentNamespace, []);
            return ach !== undefined ? {altScope: ach.scopeTokens, nsScope: ach.nsScope, typeTokens: ach.typeTokens} : undefined;
        }
        //<---- See if the name/namespace is in the current ROOT namespace (implicitly nested)---->
        else if(topdecl.subns.find((ns) => ns.name === nsroot) !== undefined) {
            const ach = this.parseIdentifierAccessChainHelper(false, topdecl, []);
            return ach !== undefined ? {altScope: ach.scopeTokens, nsScope: ach.nsScope, typeTokens: ach.typeTokens} : undefined;
        }
        else if(topdecl.declaredNames.has(nsroot)) {
            const ach = this.parseIdentifierAccessChainHelper(false, topdecl, []);
            return ach !== undefined ? {altScope: ach.scopeTokens, nsScope: ach.nsScope, typeTokens: ach.typeTokens} : undefined;
        }
        //<---- Finally resolve names through usings ---->
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

    private parseVarDeclKind(): "let" | "ref" | "var" {
        if(this.testToken(KW_let) || this.testToken(KW_ref) || this.testToken(KW_var)) {
            return this.consumeTokenAndGetValue() as "let" | "ref" | "var";
        }
        else {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Expected let, ref or var for variable declaration");
            return "let";
        }
    }

    private parseParamDeclKind(): "ref" | "out" | "out?" | "inout" | undefined {
        if(this.testToken(KW_ref) || this.testToken(KW_out) || this.testToken(KW_out_q) || this.testToken(KW_inout)) {
            return this.consumeTokenAndGetValue() as "ref" | "out" | "out?" | "inout";
        }
        else {
            return undefined;
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
        if(!/^[A-Z]$/.test(vv)) {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Invalid template variable name -- must be an uppercase letter");
        }

        return vv;
    }

    private parseIdentifierAsNamespaceOrTypeName(): string {
        const vv = this.consumeTokenAndGetValue();
        if(!/^[A-Z][_a-zA-Z0-9]+$/.test(vv)) {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Invalid namespace or type name -- must start with an uppercase letter");
        }

        return vv;
    }

    private parseIdentifierAsEnumMember(): string {
        const vv = this.consumeTokenAndGetValue();
        if(vv === "_") {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Cannot use _ as an identifier name -- it is special ignored variable");
        }
        
        if(!/^[_a-zA-Z0-9]+$/.test(vv)) {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Invalid enum member name -- must start with an uppercase letter");
        }

        return vv;
    }

    private parseIdentifierAsBinderVariable(): string {
        const vv = this.consumeTokenAndGetValue();
        if(vv === "_") {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Cannot use _ as an identifier name -- it is special ignored variable");
        }

        if(!/^[$][_a-z][_a-zA-Z0-9]*$/.test(vv)) {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Invalid binder name -- must start with $ followed by a valid identifier name");
        }

        return vv;
    }

    private parseIdentifierAsStdVariable(): string {
        const vv = this.consumeTokenAndGetValue();
        if(vv === "_") {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Cannot use _ as an identifier name -- it is special ignored variable");
        }

        if(!/^[_a-z][_a-zA-Z0-9]*$/.test(vv)) {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Invalid identifier name -- must start with a lowercase letter or _");
        }

        return vv;
    }

    private parseIdentifierAsIgnoreableVariable(): string {
        const vv = this.consumeTokenAndGetValue();
        
        if(!/^[_a-z][_a-zA-Z0-9]*$/.test(vv)) {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Invalid identifier name -- must start with a lowercase letter or _");
        }

        return vv;
    }

    private parseInvokeTermRestriction(): InvokeTemplateTypeRestriction  {
        if(!this.testFollows(SYM_lbrace, KW_when)) {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Invalid template term restriction -- expected { when ... }");
        }
        
        let first = true;
        const trl = this.parseListOf<InvokeTemplateTypeRestrictionClause>("template term restiction list", SYM_lbrace, SYM_rbrace, SYM_coma, () => {
            if(first) {
                this.consumeToken(); //the when
                first = false;
            }

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

    private parseTestAssociations(): TestAssociation[] | undefined {
        if(this.testToken(SYM_lbrack)) {
            return this.parseListOf<TestAssociation>("test association list", SYM_lbrack, SYM_rbrack, SYM_coma, () => {
                const access = this.parseIdentifierAccessChain();
                if(access === undefined) {
                    this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Invalid test association");
                    return new TestAssociation(this.env.currentFile, this.env.currentNamespace.fullnamespace, undefined, undefined);
                }
                else {
                    let tname: string | undefined = undefined;
                    if(this.testAndConsumeTokenIf(SYM_coloncolon)) {
                        this.ensureToken(TokenStrings.IdentifierName, "test association");
                        tname = this.consumeTokenAndGetValue();
                    }

                    if(access.typeTokens.length !== 0) {
                        return new TestAssociation(this.env.currentFile, access.nsScope.fullnamespace, access.typeTokens[0].tname, tname);    
                    }
                    else {
                        return new TestAssociation(this.env.currentFile, access.nsScope.fullnamespace, undefined, tname);
                    }
                }
            });
        }

        return undefined;
    }

    private parsePreAndPostConditions(sinfo: SourceInfo, argnames: Set<string>, mutparams: Set<string>, boundtemplates: Set<string>, taskcond: boolean, apicond: boolean): [PreConditionDecl[], PostConditionDecl[]] {
        let preconds: PreConditionDecl[] = [];

        this.env.scope = new StandardScopeInfo([...argnames].map((v) => new VariableDefinitionInfo("let", v)), boundtemplates, this.wellknownTypes.get("Bool") as TypeSignature);
        let ii = 0;
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
                    this.recordErrorGeneral(sinfo, "Softcheck is only allowed in API/Task pre/post conditions");
                }
            }

            const level = this.parseBuildInfo(KW_release);
            const exp = this.parseChkLogicExpression();

            preconds.push(new PreConditionDecl(this.env.currentFile, sinfo, tag, ii++, level, softcheck, exp));

            this.ensureAndConsumeTokenIf(SYM_semicolon, "requires");
        }
        this.env.scope = undefined;

        let postconds: PostConditionDecl[] = [];

        const refnames = [...mutparams].map((v) => new VariableDefinitionInfo("let", "$" + v));

        const postvardecls = [...[...argnames].map((v) => new VariableDefinitionInfo("let", v)), ...refnames, new VariableDefinitionInfo("let", WELL_KNOWN_RETURN_VAR_NAME)];
        if(taskcond || apicond) {
            postvardecls.push(new VariableDefinitionInfo("let", WELL_KNOWN_EVENTS_VAR_NAME));
        }

        this.env.scope = new StandardScopeInfo(postvardecls, boundtemplates, this.wellknownTypes.get("Bool") as TypeSignature);
        
        let jj = 0;
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
                    this.recordErrorGeneral(sinfo, "Softcheck is only allowed in API/Task pre/post conditions");
                }
            }

            const level = this.parseBuildInfo(KW_release);
            const exp = this.parseChkLogicExpression();

            postconds.push(new PostConditionDecl(this.env.currentFile, sinfo, tag, jj++, level, softcheck, exp));

            this.ensureAndConsumeTokenIf(SYM_semicolon, "ensures");
        }
        this.env.scope = undefined;

        return [preconds, postconds];
    }

    private parseLambdaSignatureParameter(): LambdaParameterSignature {
        const cinfo = this.peekToken().getSourceInfo();

        const pkind = this.parseParamDeclKind();
        const isrest = this.testAndConsumeTokenIf(SYM_dotdotdot);

        if(pkind !== undefined && isrest) {
            this.recordErrorGeneral(cinfo, "Cannot have a parameter that is both a reference and a rest");
        }

        const ptype = this.parseParameterTypeSignature();

        if(ptype instanceof LambdaTypeSignature) {
            this.recordErrorGeneral(cinfo, "Cannot have a lambda type as a parameter type of a lambda signature");
        }

        if(this.testToken(SYM_eq)) {
            this.recordErrorGeneral(this.peekToken(), "Cannot have default values for lambda parameters");
            this.consumeToken();
            this.parseExpression(); //try to eat the expression to recover nicely
        }

        return new LambdaParameterSignature(undefined, ptype, pkind, isrest);
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

        if(params.filter((p) => p.pkind !== undefined).length > 1) {
            this.recordErrorGeneral(cinfo, "Cannot have more than one special passing parameter");
        }

        return params;
    }

    private parseInvokeDeclParameter(boundtemplates: Set<string>): InvokeParameterDecl {
        const cinfo = this.peekToken().getSourceInfo();

        const pkind = this.parseParamDeclKind();
        const isrest = this.testAndConsumeTokenIf(SYM_dotdotdot);

        if(pkind !== undefined && isrest) {
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

        let optDefaultExp: Expression | undefined = undefined;
        if(this.testAndConsumeTokenIf(SYM_eq)) {
            optDefaultExp = this.parseConstScopedExpression(ptype, boundtemplates);
        }

        if(isrest && optDefaultExp !== undefined) {
            this.recordErrorGeneral(cinfo, "Cannot have a default value for rest parameters");
        }

        if(pkind !== undefined && optDefaultExp !== undefined) {
            this.recordErrorGeneral(cinfo, "Cannot have a default value for reference parameters");
        }

        return new InvokeParameterDecl(pname, ptype, optDefaultExp, pkind, isrest);
    }

    private parseInvokeDeclParameters(cinfo: SourceInfo, argSpecialAllowed: boolean, boundtemplates: Set<string>): InvokeParameterDecl[] {
        const params = this.parseListOf<InvokeParameterDecl>("function parameter list", SYM_lparen, SYM_rparen, SYM_coma, () => {
            return this.parseInvokeDeclParameter(boundtemplates)
        });
        
        if(params.length !== 0) {
            if(params.slice(0, -1).some((param) => param.isRestParam)) {
                this.recordErrorGeneral(cinfo, "Rest parameter must be the last parameter");
            }

            if(argSpecialAllowed) {
                if(params.filter((p) => p.pkind !== undefined).length > 1) {
                    this.recordErrorGeneral(cinfo, "Cannot have more than one special passing parameter");
                }
            }
            else {
                if(params.some((param) => param.pkind !== undefined)) {
                    this.recordErrorGeneral(cinfo, "Cannot have more than one special passing parameter");
                }
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
        const caninfer = this.testAndConsumeTokenIf(SYM_question);

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

        return new InvokeTemplateTermDecl(tname, tags, ttype, caninfer);
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

        const pkind = this.parseParamDeclKind();
        const isrest = this.testAndConsumeTokenIf(SYM_dotdotdot);

        if(pkind !== undefined && isrest) {
            this.recordErrorGeneral(cinfo, "Cannot have a parameter that is both a special passing and a rest");
        }

        const idok = this.ensureToken(TokenStrings.IdentifierName, "function parameter");
        const pname = idok ? this.parseIdentifierAsStdVariable() : "[error]";

        let ptype = this.env.SpecialAutoSignature;
        if(this.testAndConsumeTokenIf(SYM_colon)) {
            ptype = this.parseParameterTypeSignature();
        }

        if(ptype instanceof LambdaTypeSignature) {
            this.recordErrorGeneral(cinfo, "Cannot have a lambda type as a parameter type of a lambda declaration");
        }

        if(this.testToken(SYM_eq)) {
            this.recordErrorGeneral(this.peekToken(), "Cannot have default values for lambda parameters");
            this.consumeToken();
            this.parseExpression(); //try to eat the expression to recover nicely
        }

        return new InvokeParameterDecl(pname, ptype, undefined, pkind, isrest);
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

        if(params.filter((p) => p.pkind !== undefined).length > 1) {
            this.recordErrorGeneral(cinfo, "Cannot have more than one special passing parameter");
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
            resultInfo = this.parseReturnTypeSignature(true);
        }

        if(!this.testToken(SYM_bigarrow)) {
            this.recordExpectedError(this.peekToken(), SYM_bigarrow, "lambda declaration");
        }
        else {
            this.consumeToken();
        }
        
        const lambdaargs = params.map((param) => new VariableDefinitionInfo(param.pkind || "let", param.name));
        this.env.pushLambdaScope(lambdaargs, (resultInfo instanceof AutoTypeSignature) ? undefined : resultInfo);
        const body = this.parseBody([], false, true);
        this.env.popLambdaScope();

        return new LambdaDecl(this.env.currentFile, cinfo, [], ispred ? "pred" : "fn", isrecursive, params, resultInfo, body, !someTypedParams);
    }

    private parseFunctionInvokeDecl(functionkind: "namespace" | "predicate" | "errtest" | "chktest" | "example" | "typescope", attributes: DeclarationAttibute[], typeTerms: Set<string>): FunctionInvokeDecl | undefined {
        const cinfo = this.peekToken().getSourceInfo();

        let isrecursive: "yes" | "no" | "cond" = "no";
        if(this.testToken(KW_recursive) || this.testToken(KW_recursive_q)) {
            isrecursive = this.testToken(KW_recursive) ? "yes" : "cond";
            this.consumeToken();
        }

        let fkind: "function" | "predicate" | "chktest" | "errtest" | "example" = "function";
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
        else if(functionkind === "example") {
            fkind = "example";
            this.ensureAndConsumeTokenAlways(KW_example, "example declaration");
        }
        else {
            this.ensureAndConsumeTokenAlways(KW_function, "function declaration");
        }

        const tassoc = this.parseTestAssociations();

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
            resultInfo = this.parseReturnTypeSignature(false);
        }

        const argNames = new Set<string>(params.map((param) => param.name));
        const cargs = params.map((param) => new VariableDefinitionInfo(param.pkind || "let", param.name));
        const mutparams = new Set<string>(params.filter((param) => param.pkind !== undefined).map((param) => param.name));

        const [preconds, postconds] = this.parsePreAndPostConditions(cinfo, argNames, mutparams, boundtemplates, false, false);
        
        this.env.pushStandardFunctionScope(cargs, boundtemplates, resultInfo);
        const body = this.parseBody(attributes, functionkind === "predicate", false);
        this.env.popStandardFunctionScope();

        if(functionkind === "typescope") {
            return new TypeFunctionDecl(this.env.currentFile, cinfo, attributes, fname, isrecursive, params, resultInfo, body, terms, termRestrictions, preconds, postconds);
        }
        else {
            return new NamespaceFunctionDecl(this.env.currentFile, cinfo, attributes, fname, isrecursive, params, resultInfo, body, terms, termRestrictions, preconds, postconds, tassoc, fkind);
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
            resultInfo = this.parseReturnTypeSignature(false);
        }

        const argNames = new Set<string>(params.map((param) => param.name));
        let cargs = params.map((param) => new VariableDefinitionInfo(param.pkind || "let", param.name));
        const mutparams = new Set<string>(params.filter((param) => param.pkind !== undefined).map((param) => param.name));

        if(taskscope) {
            argNames.add("self");
            cargs = [new VariableDefinitionInfo(isref ? "ref" : "let", "self"), ...cargs];
            if(isref) {
                mutparams.add("self");
            }
        }
        else {
            argNames.add("this");
            cargs = [new VariableDefinitionInfo(!isref ? "let" : "ref", "this"), ...cargs];
            if(isref) {
                mutparams.add("this");
            }
        }

        const [preconds, postconds] = this.parsePreAndPostConditions(cinfo, argNames, mutparams, boundtemplates, false, false);
    
        this.env.pushStandardFunctionScope(cargs, boundtemplates, resultInfo);
        const body = this.parseBody(attributes, false, false);
        this.env.popStandardFunctionScope();

        if(taskscope) {
            return new TaskMethodDecl(this.env.currentFile, cinfo, attributes, fname, isrecursive, params, resultInfo, body, terms, termRestrictions, preconds, postconds, isref);
        }
        else {
            return new MethodDecl(this.env.currentFile, cinfo, attributes, fname, isrecursive, params, resultInfo, body, terms, termRestrictions, preconds, postconds, isref);
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
            resultInfo = this.parseReturnTypeSignature(false);
        }

        const argNames = new Set<string>(params.map((param) => param.name));
        let cargs = params.map((param) => new VariableDefinitionInfo(param.pkind || "let", param.name));
        const mutparams = new Set<string>(params.filter((param) => param.pkind !== undefined).map((param) => param.name));

        argNames.add("self");
        cargs = [new VariableDefinitionInfo("ref", "self"), ...cargs];
        mutparams.add("self");

        const [preconds, postconds] = this.parsePreAndPostConditions(cinfo, argNames, mutparams, boundtemplates, fname === taskmain, false);

        this.env.pushStandardFunctionScope(cargs, boundtemplates, resultInfo);
        const body = this.parseBody(attributes, false, false);
        this.env.popStandardFunctionScope();

        return new TaskActionDecl(this.env.currentFile, cinfo, attributes, fname, params, resultInfo, body, terms, termRestrictions, preconds, postconds);
    }

    ////
    //Type parsing

    //parse just types that are legal as return types
    private parseSingleReturnTypeSignature(): TypeSignature {
        switch (this.peekTokenKind()) {
            case TokenStrings.Template: {
                return this.parseTemplateTypeReference();
            }
            case TokenStrings.IdentifierName: {
                return this.parseNominalType();
            }
            case SYM_lparenbar: {
                return this.parseElistType();
            }
            default: {
                return new ErrorTypeSignature(this.peekToken().getSourceInfo(), undefined);
            }
        }
    }

    private parseReturnTypeSignature(explicitelist: boolean): TypeSignature {
        if(explicitelist) {
            return this.parseSingleReturnTypeSignature(); //lambdas need to always have explicit (|...|) for multi returns
        }
        else {
            let ttl = [this.parseSingleReturnTypeSignature()];
            while(this.testToken(SYM_coma)) {
                this.consumeToken();
                const ntt = this.parseSingleReturnTypeSignature();

                if(ntt instanceof ErrorTypeSignature) {
                    break;
                }

                ttl.push(ntt);
            }

            if(ttl.length === 1) {
                return ttl[0];
            }
            else {
                return new EListTypeSignature(ttl[0].sinfo, ttl);
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
            case SYM_lparenbar: {
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
            case SYM_lparenbar: {
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

    private parseFormatTypeTermList(sinfo: SourceInfo): [TypeSignature, {argname: string, argtype: TypeSignature}[]] {
        this.ensureAndConsumeTokenAlways(SYM_langle, "format type term list");

        let rtype = this.parseStdTypeSignature();
        let terms: {argname: string, argtype: TypeSignature}[] = [];

        let ncount = 0;
        while(!this.testToken(SYM_rangle)) {
            let argname: string = "_";

            if(this.testToken(TokenStrings.IdentifierName)) {
                ncount++;
                argname = this.consumeTokenAndGetValue();
                this.ensureAndConsumeTokenAlways(SYM_colon, "format type term");
            }
            
            const rtype = this.parseStdTypeSignature();
            terms.push({argname: argname, argtype: rtype});
        }

        this.ensureAndConsumeTokenAlways(SYM_rangle, "format type term list");

        if(terms.length === 0) {
            this.recordErrorGeneral(this.peekToken(), "Format type term list cannot be empty");
            return [new ErrorTypeSignature(sinfo, undefined), []];
        }

        if(ncount !== terms.length) {
            this.recordErrorGeneral(sinfo, "All format type terms must *either* be named or be positional");
        }

        if(ncount !== 0) {
            terms = terms.sort((a, b) => a.argname.localeCompare(b.argname));
        }

        return [rtype, terms];
    }

    private parseNominalType(): TypeSignature {
        const sinfo = this.peekToken().getSourceInfo();

        const tokenData = this.peekTokenData();
        if(this.testToken(TokenStrings.IdentifierName) && SpecialNominalTypes.includes(tokenData)) {
            const stype = this.consumeTokenAndGetValue();

            if(SpecialStringFormatTypes.includes(stype)) {
                const [rtype, terms] = this.parseFormatTypeTermList(sinfo);
                return new FormatStringTypeSignature(sinfo, stype.slice(1) as "String" | "CString", rtype, terms);
            }
            else if(SpecialPathFormatTypes.includes(stype)) {
                const [rtype, terms] = this.parseFormatTypeTermList(sinfo);
                return new FormatPathTypeSignature(sinfo, stype.slice(1) as "Path" | "PathFragment" | "PathGlob", rtype, terms);
            }
            else {
                const terms = this.parseTermList();
                return new DashResultTypeSignature(sinfo, terms);
            }
        }

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
        if(this.testToken(KW_fn) || this.testToken(KW_pred)) {
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
        const resultInfo = this.parseReturnTypeSignature(true);

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
        if (this.testAndConsumeTokenIf(KW_under)) {
            return undefined;
        }
        else {
            return this.parseStdTypeSignature();
        }
    }

    private parseSwitchLiteralGuard(): Expression | undefined {
        if (this.testAndConsumeTokenIf(KW_under)) {
            return undefined;
        }
        else {
            const exp = this.parseExpression();
    
            if(!exp.isLiteralExpression() && !(exp instanceof AccessNamespaceConstantExpression) && !(exp instanceof AccessStaticFieldExpression) && !(exp instanceof AccessEnumExpression)) {
                this.recordErrorGeneral(exp.sinfo, "Expected literal expression")
            }

            return exp;
        }
    }

    private parseDispatchGuard(): Expression | string[] | undefined {
        if (this.testAndConsumeTokenIf(KW_under)) {
            return undefined;
        }
        else {
            if(this.testAndConsumeTokenIf(TokenStrings.AtDexNumber)) {
                return [this.consumeTokenAndGetValue()];
            }
            else {
                const exp = this.parseExpression();
        
                if(!exp.isLiteralExpression() && !(exp instanceof AccessNamespaceConstantExpression) && !(exp instanceof AccessStaticFieldExpression)) {
                    this.recordErrorGeneral(exp.sinfo, "Expected literal expression or binder variable")
                }

                return exp;
            }
        }
    }

    private parseITypeTest(isnot: boolean): ITest {
        this.consumeToken();
        const ttype = this.parseStdTypeSignature();
        this.ensureAndConsumeTokenAlways(SYM_rangle, "ITest");

        return new ITestType(isnot, ttype);
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

    private checkITestFirstToken(): boolean {
        return this.testToken(SYM_bang) || this.testToken(SYM_langle) || this.testToken(KW_none) || this.testToken(KW_some) || this.testToken(KW_ok) || this.testToken(KW_fail);
    }

    private parseRValueInTopTestExpression(): Expression {
        if(this.testToken(KW_ref)) {
            return this.parseRefRValueExpression();
        }
        else if(this.testToken(KW_do)) {
            return this.parseTaskActionRValueExpression();
        }
        else {
            return this.parseExpression();
        }
    }

    private parseITestGuard(): ITestGuard {
        if(this.testFollows(SYM_lparen, TokenStrings.IdentifierName, SYM_eq)) {
            this.consumeToken();
            const binfo = this.parseBinderInfo();
            this.ensureAndConsumeTokenAlways(SYM_eq, "binder in ITest guard");
            const bexp = this.parseRValueInTopTestExpression();
            this.ensureAndConsumeTokenAlways(SYM_rparen, "binder in ITest guard");

            this.ensureAndConsumeTokenAlways(SYM_at, "binder in ITest guard");
            const itest = this.parseITest() as ITest;
            return new ITestBinderGuard(bexp, itest, new BinderInfo(binfo as string, false));
        }
        else {
            const isparened = this.testToken(SYM_lparen);
            const bexp = this.parseRValueInTopTestExpression();
            
            if((this.testToken(SYM_at) || this.checkITestFirstToken()) && !isparened) {
                this.recordErrorGeneral(bexp.sinfo, "ITest guard expression is missing parentheses");
            }

            if(this.testToken(SYM_at)) {
                let stdbindname = "$_";
                if(bexp instanceof AccessVariableExpression) {
                    stdbindname = "$" + bexp.srcname;
                }

                this.consumeToken();
                const itest = this.parseITest() as ITest;
                return new ITestBinderGuard(bexp, itest, new BinderInfo(stdbindname, true));
            }
            else if(this.checkITestFirstToken()) {
                const itest = this.parseITest() as ITest;
                return new ITestTypeGuard(bexp, itest);
            }
            else {
                return new ITestSimpleGuard(bexp);
            }
        }
    }

    private parseITestGuardSet(): ITestGuardSet {
        const lg = this.parseITestGuard();
        let guards = [lg];

        while (this.testToken(SYM_ampamp)) {
            this.consumeToken();
            guards.push(this.parseITestGuard());
        }

        return new ITestGuardSet(guards);
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

    private checkArgs(args: AbstractArgumentValue[]) {
        const namedParams = args.filter((arg) => arg instanceof NamedArgumentValue).map((arg) => (arg as NamedArgumentValue).name);
        const duplicateNames = namedParams.find((name, index) => namedParams.indexOf(name) !== index);
        if(duplicateNames !== undefined) {
            this.recordErrorGeneral(this.peekToken(), `Duplicate argument name ${duplicateNames}`);
        }

        const multiplerefs = args.filter((arg) => arg instanceof PassingArgumentValue).length > 1;
        if(multiplerefs) {
            this.recordErrorGeneral(this.peekToken(), "Cannot have multiple special passing arguments");
        }
    }

    private parseArgumentsCallStd(refok: boolean): ArgumentList {
        const args = this.parseListOf<AbstractArgumentValue>("argument list", SYM_lparen, SYM_rparen, SYM_coma, () => {
            if(this.testToken(KW_under)) {
                this.consumeToken();
                return new SkipArgumentValue();
            }
            else if(this.testToken(KW_ref) || this.testToken(KW_out) || this.testToken(KW_out_q) || this.testToken(KW_inout)) {
                if(!refok) {
                    this.recordErrorGeneral(this.peekToken(), "Cannot have a reference argument in this context");
                }

                const pk = this.consumeTokenAndGetValue() as "ref" | "out" | "out?" | "inout";
                const exp = this.parseExpression();
                if(!(exp instanceof AccessVariableExpression)) {
                    this.recordErrorGeneral(exp.sinfo, "Expected variable as target in special passing argument");
                }

                return new PassingArgumentValue(pk, exp as AccessVariableExpression);
            }
            else if(this.testToken(SYM_dotdotdot)) {
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
                const exp = this.parseLambdaOkExpression();
                
                return new PositionalArgumentValue(exp);
            }
        });

        this.checkArgs(args);

        return new ArgumentList(args);
    }

    private parseArgumentsCallLambda(refok: boolean): ArgumentList {
        const args = this.parseListOf<AbstractArgumentValue>("argument list", SYM_lparen, SYM_rparen, SYM_coma, () => {
            if(this.testToken(KW_under)) {
                this.consumeToken();
                return new SkipArgumentValue();
            }
            else if(this.testToken(KW_ref) || this.testToken(KW_out) || this.testToken(KW_out_q) || this.testToken(KW_inout)) {
                if(!refok) {
                    this.recordErrorGeneral(this.peekToken(), "Cannot have a special passing argument in this context");
                }

                const pk = this.consumeTokenAndGetValue() as "ref" | "out" | "out?" | "inout";
                const exp = this.parseExpression();
                if(!(exp instanceof AccessVariableExpression)) {
                    this.recordErrorGeneral(exp.sinfo, "Expected variable as target in special passing argument");
                }

                return new PassingArgumentValue(pk, exp as AccessVariableExpression);
            }
            else if(this.testToken(SYM_dotdotdot)) {
                this.consumeToken();
                const exp = this.parseExpression();

                return new SpreadArgumentValue(exp);
            }
            else if(this.testFollows(TokenStrings.IdentifierName, SYM_eq)) {
                this.recordErrorGeneral(this.peekToken(), "Cannot have named arguments in lambda call context");

                const name = this.parseIdentifierAsStdVariable();
                this.consumeToken();
                const exp = this.parseExpression();

                return new NamedArgumentValue(name, exp);
            }
            else {
                const exp = this.parseLambdaOkExpression();
                
                return new PositionalArgumentValue(exp);
            }
        });

        this.checkArgs(args);

        return new ArgumentList(args);
    }

    private parseArgumentsConstructorStd(): ArgumentList {
        const args = this.parseListOf<AbstractArgumentValue>("argument list", SYM_lbrace, SYM_rbrace, SYM_coma, () => {
            if(this.testToken(KW_under)) {
                this.consumeToken();
                return new SkipArgumentValue();
            }
            else if(this.testToken(KW_ref) || this.testToken(KW_out) || this.testToken(KW_out_q) || this.testToken(KW_inout)) {
                this.recordErrorGeneral(this.peekToken(), "Cannot have a special passing argument in this context");

                this.consumeToken();
                const exp = this.parseExpression();
                if(!(exp instanceof AccessVariableExpression)) {
                    this.recordErrorGeneral(exp.sinfo, "Expected variable as target in special passing argument");
                }

                //Drop the special passing argument and treat as positional so we can continue to type checker
                return new PositionalArgumentValue(exp as AccessVariableExpression);
            }
            else if(this.testToken(SYM_dotdotdot)) {
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
                const exp = this.parseExpression();
                
                return new PositionalArgumentValue(exp);
            }
        });

        this.checkArgs(args);

        return new ArgumentList(args);
    }

    private parseArgumentsCollection(mapargs: boolean): ArgumentList {
        const args = this.parseListOf<AbstractArgumentValue>("argument list", SYM_lbrace, SYM_rbrace, SYM_coma, () => {
            if(this.testToken(KW_ref) || this.testToken(KW_out) || this.testToken(KW_out_q) || this.testToken(KW_inout)) {
                this.recordErrorGeneral(this.peekToken(), "Cannot have a special passing argument in collection constructor context");

                this.consumeToken();
                const exp = this.parseExpression();
                if(!(exp instanceof AccessVariableExpression)) {
                    this.recordErrorGeneral(exp.sinfo, "Expected variable as target in special passing argument");
                }

                //Drop the special passing argument and treat as positional so we can continue to type checker
                return new PositionalArgumentValue(exp as AccessVariableExpression);
            }
            else if(this.testToken(SYM_dotdotdot)) {
                this.consumeToken();
                const exp = this.parseExpression();

                return new SpreadArgumentValue(exp);
            }
            else if(this.testFollows(TokenStrings.IdentifierName, SYM_eq)) {
                this.recordErrorGeneral(this.peekToken(), "Cannot have named arguments in collection constructor");

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
                else {
                    exp = this.parseExpression();
                }
                
                return new PositionalArgumentValue(exp);
            }
        });

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

    private processTaggedLiteral(): TypeSignature {
        this.ensureAndConsumeTokenAlways(SYM_langle, "tagged literal");
        const ttype = this.parseTypeTagSignature();
        this.ensureAndConsumeTokenAlways(SYM_rangle, "tagged literal");
        
        return ttype;
    }

    private processSimplyTaggableLiteral(sinfo: SourceInfo, tag: ExpressionTag, val: string): Expression {
        if(!this.testToken(SYM_langle)) {
            return new LiteralSimpleExpression(tag, sinfo, val);
        }
        else {
            const ttype = this.processTaggedLiteral();
            return new LiteralTypeDeclValueExpression(sinfo, new LiteralSimpleExpression(tag, sinfo, val), ttype);
        }
    }

    private trySpecialNamespaceCall(sinfo: SourceInfo, ns: NamespaceDeclaration, name: string, targs: TypeSignature[], args: ArgumentList): Expression | undefined {
        if(ns.fullnamespace.ns[0] !== "Core") {
            return undefined;
        }

        if(ns.name === "KeyComparator") {
            if(targs.length !== 1) {
                this.recordErrorGeneral(sinfo, "KeyComparator expects exactly one (keytype) template argument");
                return undefined;
            }

            if(args.args.length !== 2 || !args.args.every((arg) => arg instanceof PositionalArgumentValue)) {
                this.recordErrorGeneral(sinfo, "KeyComparator expects exactly two positional arguments");
                return undefined;
            }

            if(name === "equal") {
                return new KeyCompareEqExpression(sinfo, targs[0], (args.args[0] as PositionalArgumentValue).exp, (args.args[1] as PositionalArgumentValue).exp);
            }
            else {
                assert(name === "less");

                return new KeyCompareLessExpression(sinfo, targs[0], (args.args[0] as PositionalArgumentValue).exp, (args.args[1] as PositionalArgumentValue).exp);
            }
        }

        if(ns.name === "Interpolate") {
            if(targs.length > 1) {
                this.recordErrorGeneral(sinfo, "Interpolate expects at most one template argument");
            }

            if(args.args.length === 0 || !(args.args[0] instanceof PositionalArgumentValue)) {
                this.recordErrorGeneral(sinfo, "Interpolate expects the format string as the first (positional) argument");
            }

            if(name === "string") {
                return new InterpolateFormatExpression(sinfo, "string", targs[0], (args.args[0] as PositionalArgumentValue).exp, args.args.slice(1));
            }
            else if(name === "cstring") {
                return new InterpolateFormatExpression(sinfo, "cstring", targs[0], (args.args[0] as PositionalArgumentValue).exp, args.args.slice(1));
            }
            else if(name === "path") {
                return new InterpolateFormatExpression(sinfo, "path", targs[0], (args.args[0] as PositionalArgumentValue).exp, args.args.slice(1));
            }
            else {
                if(targs.length !== 0) {
                    this.recordErrorGeneral(sinfo, "Interpolate fragment/glob do not allow template argument");
                }

                if(name === "fragment") {
                    return new InterpolateFormatExpression(sinfo, "fragment", undefined, (args.args[0] as PositionalArgumentValue).exp, args.args.slice(1));
                }
                else {
                    assert(name === "glob");

                    return new InterpolateFormatExpression(sinfo, "glob", undefined, (args.args[0] as PositionalArgumentValue).exp, args.args.slice(1));
                }
            }
        }

        return undefined;
    }

    private parseImplicitNamespaceScopedConstOrFunc(ns: NamespaceDeclaration, decl: "isfunction" | "isconstant"): Expression {
        const sinfo = this.peekToken().getSourceInfo();

        const idname = this.parseIdentifierAsStdVariable();

        if(decl === "isconstant") {
            return new AccessNamespaceConstantExpression(sinfo, true, ns.fullnamespace, idname);
        }
        else {
            const rec = this.parseInvokeRecursiveArgs();
            const targs = this.parseInvokeTemplateArguments();
            const args = this.parseArgumentsCallStd(true);

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

        const isConstOpt = nspace.declaredConstNames.has(idname);
        const isFunOpt = nspace.declaredFunctionNames.has(idname);
        if(isConstOpt) {
            return new AccessNamespaceConstantExpression(sinfo, false, nspace.fullnamespace, idname);
        }
        else if(isFunOpt) {
            const rec = this.parseInvokeRecursiveArgs();
            const targs = this.parseInvokeTemplateArguments();
            const args = this.parseArgumentsCallStd(true);

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

        if(this.testToken(SYM_hash) || this.testToken(SYM_lbrace)) {
            const resolved = this.normalizeTypeNameChain(sinfo, access.nsScope, access.typeTokens);
            if(resolved === undefined) {
                this.recordErrorGeneral(sinfo, `Could not resolve type '${access.nsScope.fullnamespace.emit()}::${access.typeTokens.map((tt) => tt.tname).join("::")}'`);
                return new ErrorExpression(sinfo, {ns: access.nsScope, typeopt: undefined}, undefined);
            }
            
            const altns = access.altScope !== undefined ? new FullyQualifiedNamespace(access.altScope) : undefined;
            const tsig = new NominalTypeSignature(sinfo, altns, resolved, access.typeTokens.flatMap((te) => te.tterms));

            if(this.testToken(SYM_hash)) {
                this.consumeToken();
            
                const ename = this.parseIdentifierAsEnumMember();
                return new AccessEnumExpression(sinfo, tsig, ename);
            }
            else {
                const isContainer = tsig instanceof NominalTypeSignature && tsig.decl instanceof AbstractCollectionTypeDecl;
                const isMap = isContainer && (tsig instanceof NominalTypeSignature) && (tsig.decl instanceof MapTypeDecl);

                if(isContainer) {
                    const args = this.parseArgumentsCollection(isMap);
                    return new ConstructorPrimaryExpression(sinfo, tsig, args);
                }
                else {
                    const args = this.parseArgumentsConstructorStd();
                    return new ConstructorPrimaryExpression(sinfo, tsig, args);
                }
            }
        }
        else if(this.testToken(SYM_coloncolon)) {
            let tsig: TypeSignature | undefined = undefined;
            if(access.typeTokens.length === 1 && /^[A-Z]$/.test(access.typeTokens[0].tname)) {
                tsig = new TemplateTypeSignature(sinfo, access.typeTokens[0].tname);
            }
            else {
                const resolved = this.normalizeTypeNameChain(sinfo, access.nsScope, access.typeTokens);
                if(resolved === undefined) {
                    this.recordErrorGeneral(sinfo, `Could not resolve type '${access.nsScope.fullnamespace.emit()}::${access.typeTokens.map((tt) => tt.tname).join("::")}'`);
                    tsig = new ErrorTypeSignature(sinfo, access.nsScope.fullnamespace);
                }
                else {
                    const altns = access.altScope !== undefined ? new FullyQualifiedNamespace(access.altScope) : undefined;
                    tsig = new NominalTypeSignature(sinfo, altns, resolved, access.typeTokens.flatMap((te) => te.tterms));
                }
            }

            this.consumeToken();
            const idname = this.parseIdentifierAsStdVariable();

            //We can always safely parse these as they are optional but check below to make sure they are valid
            const hasrec = this.testToken(SYM_lbrack);
            const isrecursive = this.parseInvokeRecursiveArgs();

            const hastargs = this.testToken(SYM_langle);
            const targs = this.parseInvokeTemplateArguments();

            if(this.testToken(SYM_lparen)) {
                const args = this.parseArgumentsCallStd(true);

                return new CallTypeFunctionExpression(sinfo, tsig, idname, targs, isrecursive, args);
            }
            else {
                if(hasrec || hastargs) {
                    this.recordErrorGeneral(sinfo, "Invalid static field access -- cannot have recursive or template arguments");
                }

                return new AccessStaticFieldExpression(sinfo, tsig, idname);
            }
        }
        else {
            this.recordErrorGeneral(sinfo, "Unknown type scoped expression");
            return new ErrorExpression(sinfo, {ns: access.nsScope, typeopt: undefined}, undefined);
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

            if(this.testToken(SYM_lparen) || this.testFollows(SYM_lbrack, KW_recursive) || this.testFollows(SYM_lbrack, KW_recursive_q)) {
                const recursive = this.parseInvokeRecursiveArgs();
                const args = this.parseArgumentsCallLambda(true);
                return new LambdaInvokeExpression(sinfo, idname, recursive, args);
            }
            else {
                return new AccessVariableExpression(sinfo, idname);
            }
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

    private parseEnvExpression(): Expression {
        const sinfo = this.peekToken().getSourceInfo();

        this.consumeToken(); //env
        this.ensureAndConsumeTokenAlways(SYM_dot, "env expression");

        this.ensureToken(TokenStrings.IdentifierName, "env expression");
        const key = this.consumeTokenAndGetValue();
        if(key === "has" || key === "get" || key === "tryGet") {
            this.ensureAndConsumeTokenAlways(SYM_lparen, "env expression");
            let envkey: string | undefined;
            if(this.testToken(TokenStrings.IdentifierName)) {
                envkey = this.consumeTokenAndGetValue();
            }
            else if(this.testToken(TokenStrings.String) || this.testToken(TokenStrings.CString)) {
                envkey = this.consumeTokenAndGetValue();
            }
            else {
                envkey = undefined;
            }

            this.ensureAndConsumeTokenAlways(SYM_rparen, "env expression");

            if(envkey !== undefined) {
                return new AccessEnvValueExpression(sinfo, key, envkey);
            }
            else {
                this.recordErrorGeneral(sinfo, "Missing environment variable key name to access");
                return new ErrorExpression(sinfo, undefined, undefined);
                
            }
        }
        else {
            return new AccessEnvValueExpression(sinfo, undefined, key);
        }
    }

    private parseTaskFunctionExpression(): Expression {
        const sinfo = this.peekToken().getSourceInfo();

        this.consumeToken(); //Task
        this.ensureAndConsumeTokenAlways(SYM_coloncolon, "Task function expression");
        
        this.ensureToken(TokenStrings.IdentifierName, "Task function expression");
        const fname = this.consumeTokenAndGetValue();

        this.ensureAndConsumeTokenAlways(SYM_lparen, "Task function expression");
        this.ensureAndConsumeTokenAlways(SYM_rparen, "Task function expression");

        if(fname === "currentID") {
            return new TaskAccessInfoExpression(ExpressionTag.TaskAccessIDExpression, sinfo, fname);
        }
        else if(fname === "parentID") {
            return new TaskAccessInfoExpression(ExpressionTag.TaskAccessParentIDExpression, sinfo, fname);
        }
        else {
            this.recordErrorGeneral(sinfo, `Unknown Task function '${fname}'`);
            return new ErrorExpression(sinfo, undefined, undefined);
        }
    }

    private parseHoleExpression(): Expression {
        const sinfo = this.peekToken().getSourceInfo();

        this.consumeToken();

        let hname: string | undefined = undefined;
        if(this.testToken(TokenStrings.IdentifierName)) {
            hname = this.consumeTokenAndGetValue();
        }

        let captures: string[] = [];
        if(this.testToken(SYM_lbrack)) {
            captures = this.parseListOf<string>("hole captures", SYM_lbrack, SYM_rbrack, SYM_coma, () => {
                this.ensureToken(TokenStrings.IdentifierName, "hole capture list");
                return this.consumeTokenAndGetValue();
            });
        }        

        let doccomment: string | undefined = undefined;
        if(this.testToken(SYM_lparen)) {
            this.consumeToken();
            this.ensureToken(TokenStrings.DocComment, "hole expression");
            doccomment = this.consumeTokenAndGetValue();
            this.ensureAndConsumeTokenAlways(SYM_rparen, "hole expression");
        }

        let samplesfile: Expression | undefined = undefined;
        if(this.testToken(KW_of)) {
            this.consumeToken();
            samplesfile = this.parseExpression();
        }

        let explicittype: TypeSignature | undefined;
        if(this.testToken(SYM_arrow)) {
            this.consumeToken();
            explicittype = this.parseStdTypeSignature();
        }

        return new HoleExpression(sinfo, hname, captures, explicittype, doccomment, samplesfile);
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
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralBoolExpression, tk);
        }
        else if (tk === TokenStrings.Nat) {
            const istr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralNatExpression, istr);
        }
        else if (tk === TokenStrings.Int) {
            const istr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralIntExpression, istr);
        }
        else if(tk === TokenStrings.ChkNat) {
            const istr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralChkNatExpression, istr);
        }
        else if (tk === TokenStrings.ChkInt) {
            const istr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralChkIntExpression, istr);
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
            return new LiteralRegexExpression(rstr.endsWith("/") ? ExpressionTag.LiteralUnicodeRegexExpression : ExpressionTag.LiteralCRegexExpression, sinfo, this.env.currentNamespace.fullnamespace, rstr);
        }
        else if(tk === TokenStrings.Byte) {
            const bstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralByteExpression, bstr);
        }
        else if(tk === TokenStrings.CChar) {
            const cstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralCCharExpression, cstr);
        }
        else if(tk === TokenStrings.UnicodeChar) {
            const cstr = this.consumeTokenAndGetValue();
            return this.processSimplyTaggableLiteral(sinfo, ExpressionTag.LiteralUnicodeCharExpression, cstr);
        }
        else if(tk === TokenStrings.String) {
            const sstr = this.consumeTokenAndGetValue();
            if(!this.testToken(SYM_langle)) {
                return new LiteralStringExpression(sinfo, sstr);
            }
            else {
                const ttype = this.processTaggedLiteral();
                return new LiteralTypedStringExpression(sinfo, sstr, ttype);
            }
        }
        else if(tk === TokenStrings.CString) {
            const cstr = this.consumeTokenAndGetValue();
            if(!this.testToken(SYM_langle)) {
                return new LiteralCStringExpression(sinfo, cstr);
            }
            else {
                const ttype = this.processTaggedLiteral();
                return new LiteralTypedCStringExpression(sinfo, cstr, ttype);
            }
        }
        else if(tk === TokenStrings.PathItem) {
            const pstr = this.consumeTokenAndGetValue();

            let ptag = ExpressionTag.LiteralPathExpression;
            if(!pstr.startsWith("\\")) {
                ptag = pstr.startsWith("g") ? ExpressionTag.LiteralGlobExpression : ExpressionTag.LiteralPathFragmentExpression;
            }

            if(!this.testToken(SYM_langle)) {
                return new LiteralPathItemExpression(ptag, sinfo, pstr);
            }
            else {
                const ttype = this.processTaggedLiteral();

                if(ptag === ExpressionTag.LiteralPathExpression) {
                    return new LiteralTypedPathExpression(sinfo, pstr, ttype);
                }
                else {
                    this.recordErrorGeneral(sinfo, "Only full path literals can be tagged");
                    return new ErrorExpression(sinfo, undefined, undefined);
                }
            }
            
        }
        else if(tk === TokenStrings.FormatString) {
            const tkinfo = this.peekToken().getSourceInfo();

            const sstr = this.consumeTokenAndGetValue();
            const fmts = this.processFormatArguments(sstr, tkinfo);

            if(!this.testToken(SYM_langle)) {
                return new LiteralFormatStringExpression(sinfo, sstr, fmts);
            }
            else {
                const ttype = this.processTaggedLiteral();
                return new LiteralTypedFormatStringExpression(sinfo, sstr, fmts, ttype);
            }
        }
        else if(tk === TokenStrings.FormatCString) {
            const tkinfo = this.peekToken().getSourceInfo();

            const cstr = this.consumeTokenAndGetValue();
            const fmts = this.processFormatArguments(cstr, tkinfo);

            if(!this.testToken(SYM_langle)) {
                return new LiteralFormatCStringExpression(sinfo, cstr, fmts);
            }
            else {
                const ttype = this.processTaggedLiteral();
                return new LiteralTypedFormatCStringExpression(sinfo, cstr, fmts, ttype);
            }
        }
        else if(tk === TokenStrings.FormatPathItem) {
            const tkinfo = this.peekToken().getSourceInfo();

            const pstr = this.consumeTokenAndGetValue();
            const fmts = this.processFormatArguments(pstr, tkinfo);

            let ptag = ExpressionTag.LiteralPathExpression;
            if(!pstr.startsWith("\\")) {
                ptag = pstr.startsWith("g") ? ExpressionTag.LiteralGlobExpression : ExpressionTag.LiteralPathFragmentExpression;
            }

            if(!this.testToken(SYM_langle)) {
                return new LiteralFormatPathItemExpression(ptag, sinfo, pstr, fmts);
            }
            else {
                const ttype = this.processTaggedLiteral();

                if(ptag === ExpressionTag.LiteralPathExpression) {
                    return new LiteralTypedPathFormatExpression(sinfo, pstr, ttype);
                }
                else {
                    this.recordErrorGeneral(sinfo, "Only full path literal formats can be tagged");
                    return new ErrorExpression(sinfo, undefined, undefined);
                }
            }
        }
        else if(tk === TokenStrings.NumberinoInt || tk === TokenStrings.NumberinoFloat || tk === TokenStrings.NumberinoRational) {
            this.consumeToken();
            this.recordErrorGeneral(sinfo, "Un-annotated numeric literals are not supported");
            return new ErrorExpression(sinfo, undefined, undefined);
        }
        else if (tk === KW_this) {
            this.consumeToken();
            return new AccessVariableExpression(sinfo, "this");
        }
        else if (tk === KW_self) {
            this.consumeToken();
            return new AccessVariableExpression(sinfo, "self");
        }
        else if (tk == KW_env) {
            return this.parseEnvExpression();
        }
        else if(tk === KW_some || tk === KW_ok || tk === KW_fail) {
            return this.parseSpecialConstructorExpression();
        }
        else if(tk === SYM_lparenbar) {
            return this.parseEListConstructorExpression();
        }
        else if(tk === SYM_langle) {
            return this.parseParseAsTypeExpression();
        }
        else if(tk === SYM_lparen) {
            const closeparen = this.scanMatchingParens(SYM_lparen, SYM_rparen);
            this.prepStateStackForNested("paren-type", closeparen);

            this.consumeToken();
            let exp = this.parseExpression();
            
            if(this.testToken(SYM_rparen)) {
                this.consumeToken();
            }
            else {
                if(closeparen !== undefined) {
                    this.recordErrorGeneral(this.peekToken(), "Missing closing ')' in expression");
                    this.currentState().moveToRecoverPosition();
                }
            }

            this.popStateIntoParentOk();
            return exp;
        }
        else if(tk === SYM_HOLE) {
            return this.parseHoleExpression();
        }
        else if(tk === KW_Task) {
            return this.parseTaskFunctionExpression();
        }
        else if (tk === TokenStrings.IdentifierName || tk === TokenStrings.Template) {
            return this.parseIdentifierFirstExpression();
        }
        else {
            this.recordErrorGeneral(sinfo, `Unexpected token in expression -- ${tk}`);
            return new ErrorExpression(sinfo, undefined, undefined);
        }
    }

    private testPostfixInvokePrefix(): boolean {
        if(this.testToken(SYM_langle) || this.testToken(SYM_lparen)) {
            return true;
        }

        if(this.testToken(SYM_lbrack) && (this.peekTokenKind(1) === KW_recursive || this.peekTokenKind(1) === KW_recursive_q)) {
            return true;
        }

        return false;
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
                const updates = this.parseVarUpdates();

                if(updates.length === 0) {
                    this.recordErrorGeneral(sinfo, "Empty update list is not allowed");
                }
                else {
                    ops.push(new PostfixAssignFields(sinfo, updates));
                }
            }
            else {
                this.ensureAndConsumeTokenAlways(SYM_dot, "postfix access/update/invoke");

                if(this.testToken(SYM_lparenbar)) {
                    assert(false, "Not implemented yet -- project fields");
                }
                else if(this.testToken(KW_slice)) {
                    this.consumeToken();
                    const args = this.parseArgumentsCallStd(false);
                    ops.push(new PostfixSliceOperator(sinfo, args));
                }
                else if(this.testToken(TokenStrings.NumberinoInt)) {
                    const nval = this.consumeTokenAndGetValue();
                    ops.push(new PostfixAccessFromIndex(sinfo, parseInt(nval)));
                }
                else {
                    this.ensureToken(TokenStrings.IdentifierName, "postfix access/invoke");
                    
                    let resolvedScope: TypeSignature | undefined = undefined;
                    if(this.peekTokenKind(1) === SYM_coloncolon) { //it is either T::f or N::T...::f
                        resolvedScope = this.parseNominalType();
                        this.ensureToken(SYM_coloncolon, "postfix access");
                    }

                    const name = this.parseIdentifierAsStdVariable();
                    if(!this.testPostfixInvokePrefix()) {
                        if(resolvedScope !== undefined) {
                            this.recordErrorGeneral(sinfo, "Encountered named access but given type resolver (only valid on method calls)");
                        }

                        ops.push(new PostfixAccessFromName(sinfo, name));
                    }
                    else {
                        const rec = this.parseInvokeRecursiveArgs();
                        const targs = this.parseInvokeTemplateArguments();
                        const args = this.parseArgumentsCallStd(true);

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

        const exp = this.parsePostfixExpression();
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
        const iexp = this.parseRelationalExpression();

        if(!this.testToken(SYM_ampamp)) {
            return iexp;
        }
        else {
            let expl = [iexp];
            while(this.testAndConsumeTokenIf(SYM_ampamp)) {
                expl.push(this.parseRelationalExpression());
            }

            return new LogicAndExpression(sinfo, expl);
        }
    }

    private parseOrExpression(): Expression {
        const sinfo = this.peekToken().getSourceInfo();
        const iexp = this.parseAndExpression();

        if(!this.testToken(SYM_barbar)) {
            return iexp;
        }
        else {
            let expl = [iexp];
            while(this.testAndConsumeTokenIf(SYM_barbar)) {
                expl.push(this.parseAndExpression());
            }

            return new LogicOrExpression(sinfo, expl);
        }
    }

    private parseExpression(): Expression {
        return this.parseOrExpression();
    }

    private parseMapEntryConstructorExpression(): Expression {
        const sinfo = this.peekToken().getSourceInfo();

        const lexp = this.parseExpression();   
        if(this.testAndConsumeTokenIf(SYM_bigarrow)) {
            const rexp = this.parseExpression();
            return new MapEntryConstructorExpression(sinfo, lexp, rexp);
        }
        else {
            return lexp;
        }
    }

    private parseLambdaOkExpression(): Expression {
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

    private parseConstScopedExpression(etype: TypeSignature | undefined, boundtemplates: Set<string>): Expression {
        this.env.pushStandardFunctionScope([], boundtemplates, etype);
        this.env.pushBlockScope();
        const exp = this.parseExpression();
        this.env.popBlockScope();
        this.env.popStandardFunctionScope();

        return exp;
    }

    private parseEnvConstructionExpression(): EnvironmentGenerationExpression {
        const sinfo = this.peekToken().getSourceInfo();
        this.ensureAndConsumeTokenAlways(KW_env, "environment construction expression");

        if(!this.testToken(SYM_lbrace)) {
            return new CurrentEnvironmentExpression(sinfo);
        }
        else {
            const pprms = this.parseListOf<{envkey: string, value: RValueExpression}>("environment construction parameters", SYM_lbrace, SYM_rbrace, SYM_coma, () => {
                this.ensureToken(TokenStrings.IdentifierName, "environment construction parameter");
                const envkey = this.consumeTokenAndGetValue();
                this.ensureAndConsumeTokenAlways("=", "environment construction parameter");
                const value = this.parseRValueExpression();

                return { envkey: envkey, value: value };
            });

            if(pprms.length === 0) {
                return new EmptyEnvironmentExpression(sinfo);
            }
            else {
                return new InitializeEnvironmentExpression(sinfo, pprms);
            }
        }
    }

    private parseTaskTailArgs(): Expression[] {
        let args: Expression[] = [];

        while(this.testToken(SYM_coma)) {
            this.consumeToken();

            args.push(this.parseExpression());
        }

        return args;
    }

    private parseTaskArguments(): [Expression[], EnvironmentGenerationExpression] {
        this.ensureAndConsumeTokenAlways(SYM_lparen, "Task arguments");

        const envexp = this.parseEnvConstructionExpression();
        let args: Expression[] = [];
        if(this.testToken(SYM_coma)) {
            args = this.parseTaskTailArgs();
        }

        this.ensureAndConsumeTokenAlways(SYM_rparen, "Task arguments");

        return [args, envexp];
    }

    private parseTaskConfigs(config: TaskConfiguration)  {
        while(this.testToken(TokenStrings.IdentifierName) && TaskConfigs.includes(this.peekToken().data as string)) {
            const sinfo = this.peekToken().getSourceInfo();

            const cname = this.consumeTokenAndGetValue();
            this.ensureAndConsumeTokenAlways(SYM_eq, "task configs section");

            if(cname === "priority") {
                this.ensureToken(TokenStrings.IdentifierName, "task configs section");
                const pstr = this.consumeTokenAndGetValue();
                if(!["immediate", "fast", "normal", "longrunning", "background", "optional"].includes(pstr)) {
                    this.recordErrorGeneral(sinfo, `Invalid task priority -- ${pstr}`);
                }
                    
                config.priority = pstr as "immediate" | "fast" | "normal" | "longrunning" | "background" | "optional";
            }
            else if(cname === "retry") {
                this.ensureAndConsumeTokenAlways(SYM_lparen, "task configs section");
                this.ensureToken(TokenStrings.NumberinoInt, "task configs section");
                const retrycount = Number.parseInt(this.consumeTokenAndGetValue());
                this.ensureAndConsumeTokenAlways(SYM_coma, "task configs section");
                this.ensureToken(TokenStrings.NumberinoInt, "task configs section");
                const retrydelay = Number.parseInt(this.consumeTokenAndGetValue());
                this.ensureAndConsumeTokenAlways(TokenStrings.IdentifierName, "ms value");
                this.ensureAndConsumeTokenAlways(SYM_rparen, "task configs section");

                config.retry = { tries: retrycount, delay: retrydelay };
            }
            else if(cname === "timeout") {
                this.ensureToken(TokenStrings.NumberinoInt, "task configs section");
                const msexp = Number.parseInt(this.consumeTokenAndGetValue());
                this.ensureAndConsumeTokenAlways(TokenStrings.IdentifierName, "ms value");

                config.timeout = msexp;
            }
            else {
                this.recordErrorGeneral(sinfo, `Unknown task config -- ${cname}`);
            }
        }
    }

    private parseTaskRunExpression(sinfo: SourceInfo, execmode: "parallel" | "sequential" | "std"): Expression {
        if(execmode !== "std") {
            this.recordErrorGeneral(sinfo, "Parallel/Sequential are not allowed on single Task::run");
        }

        this.consumeToken(); //<
        const task = this.parseNominalType();
        const configs = new TaskConfiguration(undefined, undefined, undefined);
        this.parseTaskConfigs(configs);
        this.consumeToken(); //>

        const [args, envexp] = this.parseTaskArguments();

        return new TaskRunExpression(sinfo, task, args, envexp, configs);
    }

    private parseTaskMultiExpression(sinfo: SourceInfo, execmode: "parallel" | "sequential" | "std"): Expression {
        const tasks = this.parseListOf<[TypeSignature, TaskConfiguration]>("Task multi types", SYM_langle, SYM_rangle, SYM_coma, () => {
            const task = this.parseNominalType();
            const configs = new TaskConfiguration(undefined, undefined, undefined);
            this.parseTaskConfigs(configs);

            return [task, configs];
        });

        const args = this.parseListOf<[Expression[], EnvironmentGenerationExpression]>("Task multi arguments", SYM_lparen, SYM_rparen, SYM_semicolon, () => {
            return this.parseTaskArguments();
        });

        return new TaskMultiExpression(sinfo, execmode, tasks, args);
    }

    private parseTaskAllExpression(sinfo: SourceInfo, execmode: "parallel" | "sequential" | "std"): Expression {
        this.consumeToken(); //<
        const task = this.parseNominalType();
        const configs = new TaskConfiguration(undefined, undefined, undefined);
        this.parseTaskConfigs(configs);
        this.consumeToken(); //>

        this.ensureAndConsumeTokenAlways(SYM_lparen, "Task all expression");
        const envexp = this.parseEnvConstructionExpression();
        this.ensureAndConsumeTokenAlways(SYM_coma, "Task all expression");
        const argl = this.parseExpression();
        this.ensureAndConsumeTokenAlways(SYM_rparen, "Task all expression");

        return new TaskAllExpression(sinfo, execmode, task, argl, envexp, configs);
    }

    private parseTaskDashStyleExpression(sinfo: SourceInfo, execmode: "parallel" | "sequential" | "std", isany: boolean): Expression {
        const tasks = this.parseListOf<[TypeSignature, TaskConfiguration]>("Task dash types", SYM_langle, SYM_rangle, SYM_coma, () => {
            const task = this.parseNominalType();
            const configs = new TaskConfiguration(undefined, undefined, undefined);
        this.parseTaskConfigs(configs);

            return [task, configs];
        });

        const args = this.parseListOf<[Expression[], EnvironmentGenerationExpression]>("Task dash arguments", SYM_lparen, SYM_rparen, SYM_semicolon, () => {
            return this.parseTaskArguments();
        });

        if(!isany) {
            return new TaskDashExpression(sinfo, execmode, tasks, args);
        }
        else {
            return new TaskDashAnyExpression(sinfo, execmode, tasks, args);
        }
    }

    private parseTaskRaceStyleExpression(sinfo: SourceInfo, execmode: "parallel" | "sequential" | "std", isany: boolean): Expression {
        this.consumeToken(); //<
        const task = this.parseNominalType();
        const configs = new TaskConfiguration(undefined, undefined, undefined);
        this.parseTaskConfigs(configs);
        this.consumeToken(); //>

        this.ensureAndConsumeTokenAlways(SYM_lparen, "Task race expression");
        const envexp = this.parseEnvConstructionExpression();
        this.ensureAndConsumeTokenAlways(SYM_coma, "Task race expression");
        const argl = this.parseExpression();
        this.ensureAndConsumeTokenAlways(SYM_rparen, "Task race expression");

        if(!isany) {
            return new TaskRaceExpression(sinfo, execmode, task, argl, envexp, configs);
        }
        else {
            return new TaskRaceAnyExpression(sinfo, execmode, task, argl, envexp, configs);
        }
    }

    private parseAPIInvokeExpression(): APIInvokeExpression {
        const sinfo = this.peekToken().getSourceInfo();

        this.ensureAndConsumeTokenAlways(KW_api, "API invoke expression");

        const peekname = this.peekTokenData();
        const access = this.parseIdentifierAccessChain();
        if(access === undefined || access.typeTokens.length === 0) {
            this.recordErrorGeneral(sinfo, `Could not resolve '${peekname}' in this context`);
        }

        this.ensureAndConsumeTokenAlways(SYM_coloncolon, "api scoped expression");
        this.ensureToken(TokenStrings.IdentifierName, "api scoped expression");

        const api = this.parseIdentifierAsStdVariable();
        const configs = new TaskConfiguration(undefined, undefined, undefined);
        this.parseTaskConfigs(configs);

        const [args, envexp] = this.parseTaskArguments();

        return new APIInvokeExpression(sinfo, access!.nsScope.fullnamespace, api, args, envexp, configs);
    }

    private parseAgentInvokeExpression(): AgentInvokeExpression {
        const sinfo = this.peekToken().getSourceInfo();

        this.ensureAndConsumeTokenAlways(KW_agent, "API invoke expression");

        const peekname = this.peekTokenData();
        const access = this.parseIdentifierAccessChain();
        if(access === undefined || access.typeTokens.length === 0) {
            this.recordErrorGeneral(sinfo, `Could not resolve '${peekname}' in this context`);
        }

        this.ensureAndConsumeTokenAlways(SYM_coloncolon, "api scoped expression");
        this.ensureToken(TokenStrings.IdentifierName, "api scoped expression");

        const api = this.parseIdentifierAsStdVariable();
        const configs = new TaskConfiguration(undefined, undefined, undefined);
        this.parseTaskConfigs(configs);
        let explicittype: TypeSignature | undefined = undefined;
        if(this.testToken(SYM_langle)) {
            this.consumeToken(); //<
            explicittype = this.parseStdTypeSignature();
            this.ensureAndConsumeTokenAlways(SYM_rangle, "agent invoke explicit type");
        }

        const [args, envexp] = this.parseTaskArguments();

        return new AgentInvokeExpression(sinfo, access!.nsScope.fullnamespace, api, explicittype, args, envexp, configs);
    }

    private parseChkLogicExpression(): ChkLogicExpression {
        const sinfo = this.peekToken().getSourceInfo();

        const cle = this.parseITestGuardSet();

        if(this.testToken(SYM_implies)) {
            this.consumeToken();

            const rhs = this.parseExpression();
            return new ChkLogicImpliesExpression(sinfo, cle, rhs);
        }
        else {
            let llexps: Expression[] = [];

            if(!cle.guards.every((g) => g instanceof ITestSimpleGuard)) {
                this.recordErrorGeneral(sinfo, "Complex guard sets are not allowed in standalone chk logic expressions");
                llexps.push(new ErrorExpression(sinfo, undefined, undefined));
            }
            else {
                if(cle.guards.length === 1) {
                    llexps.push((cle.guards[0] as ITestSimpleGuard).exp);
                }
                else {
                    llexps.push(new LogicAndExpression(sinfo, cle.guards.map((g) => (g as ITestSimpleGuard).exp)));
                }
            }

            while(this.testToken(SYM_barbar)) {
                this.consumeToken();
                const ng = this.parseExpression();
                llexps.push(ng);
            }

            return new ChkLogicBaseExpression(llexps.length === 1 ? llexps[0] : new LogicOrExpression(sinfo, llexps));

        }
    }

    private parseChkLogicScopedExpression(boundtemplates: Set<string>): ChkLogicExpression {
        this.env.pushStandardFunctionScope([], boundtemplates, this.wellknownTypes.get("Bool"));
        this.env.pushBlockScope();
        const exp = this.parseChkLogicExpression();
        this.env.popBlockScope();
        this.env.popStandardFunctionScope();

        return exp;
    }

    private parseConditionalExpressionTail(sinfo: SourceInfo, exp: ITestGuardSet): RValueExpression {
        this.ensureAndConsumeTokenAlways(SYM_question, "conditional expression");

        const thenexp = this.parseExpression();
        this.ensureAndConsumeTokenAlways(SYM_colon, "conditional expression");
        const elseexp = this.parseExpression();

        return new ConditionalValueExpression(sinfo, exp, thenexp, elseexp);
    }

    private parseShortCircuitOptions(exp: Expression): RValueExpression {
        if(this.testToken(SYM_atat)) {
            this.consumeToken();

            const itest = this.parseITest() as ITest;
            return new ShortCircuitAssignRHSExpressionFail(exp, itest);
        } 
        else {
            this.ensureAndConsumeTokenAlways(SYM_questionat, "short-circuit options");

            const itest = this.parseITest() as ITest;
            this.ensureAndConsumeTokenAlways(SYM_colon, "short-circuit options");
            const rexp = this.parseExpression();

            return new ShortCircuitAssignRHSExpressionReturn(exp, itest, rexp);
        }
    }

    private parseRefRValueExpression(): Expression {
        const sinfo = this.peekToken().getSourceInfo();
        this.consumeToken();

        if(!this.testToken(TokenStrings.IdentifierName) && !this.testToken(KW_this) && !this.testToken(KW_self)) {
            this.recordErrorGeneral(sinfo, "Expected a variable name after ref");
            return new ErrorExpression(sinfo, undefined, undefined);
        }

        const rcvr = new AccessVariableExpression(this.peekToken().getSourceInfo(), this.consumeTokenAndGetValue());
        this.ensureAndConsumeTokenAlways(SYM_dot, "ref invoke");

        this.ensureToken(TokenStrings.IdentifierName, "ref invoke");
                    
        let resolvedScope: TypeSignature | undefined = undefined;
        if(this.peekTokenKind(1) === SYM_coloncolon) { //it is either T::f or N::T...::f
            resolvedScope = this.parseNominalType();
            this.ensureToken(SYM_coloncolon, "postfix access");
        }

        const name = this.parseIdentifierAsStdVariable();

        const rec = this.parseInvokeRecursiveArgs();
        const targs = this.parseInvokeTemplateArguments();
        const args = this.parseArgumentsCallStd(false);

        if(rcvr.srcname === "this") {
            return new CallRefThisExpression(sinfo, rcvr, resolvedScope, name, targs, rec, args);
        }
        if(rcvr.srcname === "self") {
            return new CallRefSelfExpression(sinfo, rcvr, name, targs, rec, args);                
        }
        else {
            return new CallRefVariableExpression(sinfo, rcvr, resolvedScope, name, targs, rec, args);
        }
    }

    private parseTaskActionRValueExpression(): Expression {
        const sinfo = this.peekToken().getSourceInfo();

        this.ensureAndConsumeTokenAlways(KW_do, "Task action expression");
        this.ensureAndConsumeTokenAlways(KW_self, "Task action expression");
        this.ensureAndConsumeTokenAlways(SYM_dot, "Task action expression");

        this.ensureToken(TokenStrings.IdentifierName, "Task action expression");
        const name = this.parseIdentifierAsStdVariable();

        const terms = this.parseInvokeTemplateArguments();
        const args = this.parseArgumentsCallStd(false);

        return new CallTaskActionExpression(sinfo, name, terms, args);
    }

    private parseTaskRunRValueExpression(execmode: "parallel" | "sequential" | "std"): Expression {
        this.ensureAndConsumeTokenAlways(KW_Task, "Task run expression");
        this.ensureAndConsumeTokenAlways(SYM_coloncolon, "Task run expression");

        this.ensureToken(TokenStrings.IdentifierName, "Task run expression");
        const taskname = this.consumeTokenAndGetValue();

        if(taskname === "run") {
            return this.parseTaskRunExpression(this.peekToken().getSourceInfo(), execmode);
        }
        else if(taskname === "multi") {
            return this.parseTaskMultiExpression(this.peekToken().getSourceInfo(), execmode);
        }
        else if(taskname === "all") {
            return this.parseTaskAllExpression(this.peekToken().getSourceInfo(), execmode);
        }
        else if(taskname === "dash") {
            return this.parseTaskDashStyleExpression(this.peekToken().getSourceInfo(), execmode, false);
        }
        else if(taskname === "dashAny") {
            return this.parseTaskDashStyleExpression(this.peekToken().getSourceInfo(), execmode, true);
        }
        else if(taskname ===  "race") {
            return this.parseTaskRaceStyleExpression(this.peekToken().getSourceInfo(), execmode, false);
        }
        else if(taskname ===  "raceAny") {
            return this.parseTaskRaceStyleExpression(this.peekToken().getSourceInfo(), execmode, true);
        }
        else {
            this.recordErrorGeneral(this.peekToken().getSourceInfo(), `Unknown Task function '${taskname}'`);
            return new ErrorExpression(this.peekToken().getSourceInfo(), undefined, undefined);
        }
    }

    private parseRValueOfLHSExpression(sinfo: SourceInfo): RValueExpression {
        const eexpr = this.parseITestGuardSet();

        if(this.testToken(SYM_question)) {
            return this.parseConditionalExpressionTail(sinfo, eexpr);
        }
        else {
            if(eexpr.guards.length !== 1 || !(eexpr.guards[0] instanceof ITestSimpleGuard)) {
                this.recordErrorGeneral(sinfo, "Guard set found where simple expression expected");
            }

            const lexp = eexpr.guards[0].exp;
            if(this.testToken(SYM_atat) || this.testToken(SYM_questionat)) {
                return this.parseShortCircuitOptions(lexp);
            }
            else {
                return new BaseRValueExpression(lexp);
            }
        }
    }

    private parseRValueOfLHSExpressionSimple(sinfo: SourceInfo, expr: Expression): RValueExpression {
        if(this.testToken(SYM_question)) {
            return this.parseConditionalExpressionTail(sinfo, new ITestGuardSet([new ITestSimpleGuard(expr)]));
        }
        else {
            if(this.testToken(SYM_atat) || this.testToken(SYM_questionat)) {
                return this.parseShortCircuitOptions(expr);
            }
            else {
                return new BaseRValueExpression(expr);
            }
        }
    }

    private parseRValueExpression(): RValueExpression {
        const sinfo = this.peekToken().getSourceInfo();

        if(this.testToken(KW_ref)) {
            const expr = this.parseRefRValueExpression();
            return this.parseRValueOfLHSExpressionSimple(sinfo, expr);
        }
        else if(this.testToken(KW_do)) {
            const expr = this.parseTaskActionRValueExpression(); 
            return this.parseRValueOfLHSExpressionSimple(sinfo, expr);
        }
        else if(this.testToken(KW_sequential) || this.testToken(KW_parallel) || this.testToken(KW_Task)) {
            let execmode: "sequential" | "parallel" | "std" = "std";
            if(this.testToken(KW_sequential) || this.testToken(KW_parallel)) {
                execmode = this.consumeTokenAndGetValue() as "sequential" | "parallel";
            }

            const oop = this.peekToken(2);
            if(oop.kind === TokenStrings.IdentifierName && (oop.data === "currentID" || oop.data === "parentID")) {
                return this.parseRValueOfLHSExpression(sinfo); //Task::currentID() or Task::parentID() -- followed maybe by some more stuff
            }
            else {
                const expr = this.parseTaskRunRValueExpression(execmode);
                return new BaseRValueExpression(expr);
            }
        }
        else if(this.testToken(KW_api)) {
            const apiexpr = this.parseAPIInvokeExpression();
            return new BaseRValueExpression(apiexpr);
        }
        else if(this.testToken(KW_agent)) {
            const expr = this.parseAgentInvokeExpression();
            return new BaseRValueExpression(expr);
        }
        else {
            return this.parseRValueOfLHSExpression(sinfo);
        }
    }

    parseTestRValueExpression(): RValueExpression {
        const sinfo = this.peekToken().getSourceInfo();

        const eexpr = this.parseITestGuardSet();

        if(this.testToken(SYM_question)) {
            return this.parseConditionalExpressionTail(sinfo, eexpr);
        }
        else {
            if(eexpr.guards.length !== 1 || !(eexpr.guards[0] instanceof BaseRValueExpression)) {
                this.recordErrorGeneral(sinfo, "Guard set found where simple expression expected");
            }

            const lexp = eexpr.guards[0].exp;
            return new BaseRValueExpression(lexp);
        }
    }

    private parseStatementExpression(): Statement {
        const sinfo = this.peekToken().getSourceInfo();

        if(this.testFollows(KW_ref, KW_this, SYM_lbrack)) {
            this.consumeToken(); //consume ref

            const vexp = new AccessVariableExpression(this.peekToken().getSourceInfo(), "this");
            this.consumeToken(); //consume this

            const updates = this.parseVarUpdates();

            if(updates.length === 0) {
                this.recordErrorGeneral(sinfo, "Empty update list is not allowed");
                return new ErrorStatement(sinfo);
            }

            return new ThisUpdateStatement(sinfo, vexp, updates);
        }
        else if(this.testFollows(KW_ref, TokenStrings.IdentifierName, SYM_lbrack)) {
            this.consumeToken(); //consume ref

            const vexp = new AccessVariableExpression(this.peekToken().getSourceInfo(), this.consumeTokenAndGetValue());
            const updates = this.parseVarUpdates();

            if(updates.length === 0) {
                this.recordErrorGeneral(sinfo, "Empty update list is not allowed");
                return new ErrorStatement(sinfo);
            }

            return new VarUpdateStatement(sinfo, vexp, updates);
        }
        else if(this.testFollows(KW_ref, KW_self, SYM_lbrack)) {
            this.consumeToken(); //consume self
            const updates = this.parseVarUpdates();

            if(updates.length === 0) {
                this.recordErrorGeneral(sinfo, "Empty update list is not allowed");
                return new ErrorStatement(sinfo);
            }

            return new SelfUpdateStatement(sinfo, updates);
        }
        else if(this.testToken(KW_do)) {
            const rhs = this.parseTaskActionRValueExpression();
            return new VoidRefCallStatement(sinfo, rhs);  
        }
        else {
            const rhs = this.parseExpression(); //must be a call (with a ref/out param)
            if(!(rhs instanceof CallNamespaceFunctionExpression) && !(rhs instanceof CallTypeFunctionExpression) && !(rhs instanceof PostfixOp) && !(rhs instanceof CallRefInvokeExpression)) {
                this.recordErrorGeneral(sinfo, "Expected a call expression");
                return new ErrorStatement(sinfo);
            }

            if((rhs instanceof PostfixOp) && ((rhs.ops.length !== 1) && !(rhs.ops[0] instanceof PostfixInvoke))) {
                this.recordErrorGeneral(sinfo, "Postfix expression with ref must be simple (not later in a chained operation");
                return new ErrorStatement(sinfo);
            }

            return new VoidRefCallStatement(sinfo, rhs);  
        }
    }

    ////
    //Statement parsing

    private parseSingleDeclarationVarInfo(): {name: string, vtype: TypeSignature} {
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

    private parseMultiDeclarationVarInfo(isfirst: boolean): {name: string, vtype: TypeSignature}[] {
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

    private parseSingleAssignmentVarInfo(): string {
        const sinfo = this.peekToken().getSourceInfo();

        this.ensureTokenOptions(TokenStrings.IdentifierName, KW_under);
        const name = this.parseIdentifierAsIgnoreableVariable();

        if(!/^[a-z_]/.test(name)) {
            this.recordErrorGeneral(sinfo, `Local variables must start with a lowercase letter or underscore but got "${name}"`);
        }

        return name;
    }

    private parseMultiAssignmentVarInfo(isfirst: boolean): string[] {
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

    private parseVarUpdates(): [string, Expression][] {
        return this.parseListOf<[string, Expression]>("variable update list", SYM_lbrack, SYM_rbrack, SYM_coma, () => {
            this.ensureToken(TokenStrings.IdentifierName, "variable update list");
            const name = this.consumeTokenAndGetValue();

            this.ensureAndConsumeTokenAlways("=", "variable update list");
            const exp = this.parseExpression();

            return [name, exp];
        });
    }

    private parseHoleStatement(): Statement {
        const sinfo = this.peekToken().getSourceInfo();
        this.consumeToken();

        let hname: string | undefined = undefined;
        if(this.testToken(TokenStrings.IdentifierName)) {
            hname = this.consumeTokenAndGetValue();
        }

        let captures: string[] = [];
        if(this.testToken(SYM_lbrack)) {
            captures = this.parseListOf<string>("hole captures", SYM_lbrack, SYM_rbrack, SYM_coma, () => {
                this.ensureToken(TokenStrings.IdentifierName, "hole capture list");
                return this.consumeTokenAndGetValue();
            });
        }        

        let doccomment: string | undefined = undefined;
        if(this.testToken(SYM_lparen)) {
            this.consumeToken();
            this.ensureToken(TokenStrings.DocComment, "hole expression");
            doccomment = this.consumeTokenAndGetValue();
            this.ensureAndConsumeTokenAlways(SYM_rparen, "hole expression");
        }

        let samplesfile: Expression | undefined = undefined;
        if(this.testToken(KW_of)) {
            this.consumeToken();
            samplesfile = this.parseExpression();
        }

        let nvars: {name: string, tsig: TypeSignature}[] = [];
        let ensures: ChkLogicExpression[] = [];
        if(this.testToken(SYM_arrow)) {
            this.consumeToken();
            
            if(this.testToken(SYM_lbrack)) {
                nvars = this.parseListOf<{name: string, tsig: TypeSignature}>("hole named variables", SYM_lbrack, SYM_rbrack, SYM_coma, () => {
                    this.ensureToken(TokenStrings.IdentifierName, "hole named variable");
                    const name = this.consumeTokenAndGetValue();
                    this.ensureAndConsumeTokenAlways(SYM_colon, "hole named variable");
                    const tsig = this.parseStdTypeSignature();

                    return { name: name, tsig: tsig };
                });
            }

            if(this.testToken(SYM_lbrace)) {
                ensures = this.parseListOf<ChkLogicExpression>("hole ensures expressions", SYM_lbrace, SYM_rbrace, SYM_semicolon, () => {
                    this.ensureAndConsumeTokenAlways(KW_ensures, "hole ensures expression");
                    return this.parseChkLogicExpression();
                });
            }
        }

        return new HoleStatement(sinfo, hname, captures, doccomment, samplesfile, nvars, ensures);
    }

    private isVarDeclPrefix(): boolean {
        if(!this.testToken(KW_var) && !this.testToken(KW_ref) && !this.testToken(KW_let)) {
            return false;
        }

        if(this.testToken(KW_var) || this.testToken(KW_let)) {
            return true;
        }
        else {
            const wtype = this.testFollows(KW_ref, TokenStrings.IdentifierName, SYM_colon); //ref x: T ... case
            const wtypeu = this.testFollows(KW_ref, KW_under, SYM_colon); //ref _: T ... case
            const wassign = this.testFollows(KW_ref, TokenStrings.IdentifierName, SYM_eq); //ref x = ... case
            const wassignu = this.testFollows(KW_ref, KW_under, SYM_eq); //ref _ = ... case
            const wmulti = this.testFollows(KW_ref, TokenStrings.IdentifierName, SYM_coma); //ref x, y = ... case
            const wmultiu = this.testFollows(KW_ref, KW_under, SYM_coma); //ref _, y = ... case

            return wtype || wtypeu || wassign || wassignu || wmulti || wmultiu;
        }
    }

    private isTaskStatementPrefix(): boolean {
        if(!this.testFollows(KW_Task, SYM_coloncolon, TokenStrings.IdentifierName)) {
            return false;
        }

        const taskname = this.peekTokenData(2);
        return taskname === "emitStatusUpdate" || taskname === "checkAndHandleTermination";
    }

    private parseLineStatement(): Statement {
        const sinfo = this.peekToken().getSourceInfo();

        if (this.testToken(SYM_semicolon)) {
            return new EmptyStatement(sinfo);
        }
        else if (this.isVarDeclPrefix()) {
            const vtype = this.parseVarDeclKind();
            const assigns = this.parseMultiDeclarationVarInfo(true);

            if(this.testToken(SYM_semicolon)) {
                if(vtype !== "var") {
                    this.recordErrorGeneral(sinfo, "Cannot declare as let/ref without an assignment");
                }

                if(assigns.some((vv) => vv.vtype instanceof AutoTypeSignature)) {
                    this.recordErrorGeneral(sinfo, "Cannot declare a variable with an auto type without an assignment");
                }

                assigns.forEach((vv) => {
                    const okadd = this.env.addVariable(vv.name, vtype, false);
                    if(!okadd) {
                        this.recordErrorGeneral(sinfo, `Variable ${vv.name} cannot be defined`);
                    }
                });

                return assigns.length === 1 ? new VariableDeclarationStatement(sinfo, assigns[0].name, assigns[0].vtype) : new VariableMultiDeclarationStatement(sinfo, assigns);
            }
            else if(this.testToken(SYM_eq)) {
                this.consumeToken();

                const exp = this.parseRValueExpression();
                if(this.testToken(SYM_semicolon)) {
                    //could be elist type expression but we need to wait for type checking
                    assigns.forEach((vv) => {
                        const okadd = this.env.addVariable(vv.name, vtype, assigns.length > 1);
                        if(!okadd) {
                            this.recordErrorGeneral(sinfo, `Variable ${vv.name} cannot be defined`);
                        }
                    });

                    return assigns.length === 1 ? new VariableInitializationStatement(sinfo, vtype, assigns[0].name, assigns[0].vtype, exp) : new VariableMultiInitializationStatement(sinfo, vtype, assigns, exp);
                }
                else {
                    //we need as many expressions as there are variables
                    let exps: Expression[] = [];
                    while(this.testToken(SYM_coma) && exps.length < assigns.length) {
                        this.consumeToken();
                        exps.push(this.parseExpression());
                    }

                    if(exps.length + 1 !== assigns.length) {
                        this.recordErrorGeneral(sinfo, "Mismatch in number of variables and expressions in assignment");
                    }

                    assigns.forEach((vv) => {
                        const okadd = this.env.addVariable(vv.name, vtype, true);
                        if(!okadd) {
                            this.recordErrorGeneral(sinfo, `Variable ${vv.name} is already defined`);
                        }
                    });

                    if(assigns.length === 1) {
                        return new VariableInitializationStatement(sinfo, vtype, assigns[0].name, assigns[0].vtype, exp);
                    }
                    else {
                        let bexp: Expression = new ErrorExpression(sinfo, undefined, undefined);
                        if(exp instanceof BaseRValueExpression) {
                            bexp = exp.exp;
                        }
                        else {
                            this.recordErrorGeneral(sinfo, "Cannot use complex RHS expression in multi-initialization");
                        }

                        return new VariableMultiInitializationStatement(sinfo, vtype, assigns, [bexp, ...exps]);
                    }
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
            const exp = this.parseRValueExpression();

            return new VariableAssignmentStatement(sinfo, vname, exp);
        }
        else if (this.testFollows(TokenStrings.IdentifierName, SYM_coma) || this.testFollows(KW_under, SYM_coma)) {
            const vnames = this.parseMultiAssignmentVarInfo(true);

            this.ensureAndConsumeTokenIf(SYM_eq, "assignment statement");
            const exp = this.parseRValueExpression();

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
                let exps: Expression[] = [];
                while(this.testToken(SYM_coma) && exps.length < vnames.length) {
                    this.consumeToken();
                    exps.push(this.parseExpression());
                }

                if(exps.length + 1 !== vnames.length) {
                    this.recordErrorGeneral(sinfo, "Mismatch in number of variables and expressions in assignment");
                }

                vnames.forEach((vv) => {
                    this.env.assignVariable(vv);
                });

                if(vnames.length === 1) {
                    return new VariableAssignmentStatement(sinfo, vnames[0], exp);
                }
                else {
                    let bexp: Expression = new ErrorExpression(sinfo, undefined, undefined);
                    if(exp instanceof BaseRValueExpression) {
                        bexp = exp.exp;
                    }
                    else {
                        this.recordErrorGeneral(sinfo, "Cannot use complex RHS expression in multi-assignment");
                    }

                    return new VariableMultiAssignmentStatement(sinfo, vnames, [bexp, ...exps]);
                }
            }
        }
        else if (this.testToken(KW_return)) {
            this.consumeToken();

            if(this.testToken(SYM_semicolon)) {
                return new ReturnVoidStatement(sinfo);
            }
            else {
                const rexp = this.parseRValueExpression();
                if(this.testToken(SYM_semicolon)) {
                    return new ReturnSingleStatement(sinfo, rexp);
                }
                else {
                    let rexps: Expression[] = [];
                    while(this.testToken(SYM_coma)) {
                        this.consumeToken();
                        rexps.push(this.parseExpression());
                    }


                    let bexp: Expression = new ErrorExpression(sinfo, undefined, undefined);
                    if(rexp instanceof BaseRValueExpression) {
                        bexp = rexp.exp;
                    }
                    else {
                        this.recordErrorGeneral(sinfo, "Cannot use complex RHS expression in multi-return");
                    }

                    return new ReturnMultiStatement(sinfo, [bexp, ...rexps]);
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
            const exp = this.parseChkLogicExpression();

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

            const exp = this.parseChkLogicExpression();
            return new ValidateStatement(sinfo, exp, diagnosticTag);
        }
        else if (this.testToken(KW__debug)) {
            this.consumeToken();

            const value = this.parseExpression();
            
            return new DebugStatement(sinfo, value);
        }
        else if(this.isTaskStatementPrefix()) {
            this.consumeToken(); //Task
            this.consumeToken(); //::

            const op = this.consumeTokenAndGetValue();
            if(op === "checkAndHandleTermination") {
                return new TaskCheckAndHandleTerminationStatement(sinfo);
            }
            else {
                this.ensureAndConsumeTokenAlways(SYM_lparen, `Task::${op} operation`);
                const exp = this.parseExpression();
                this.ensureAndConsumeTokenAlways(SYM_rparen, `Task::${op} operation`);

                return new TaskStatusStatement(sinfo, exp);
            }
        }
        else if(this.testToken(KW_yield)) {
            this.consumeToken();
            const exp = this.parseRValueExpression();
            return new TaskYieldStatement(sinfo, exp);
        }
        else if (this.testToken(SYM_HOLE)) {
            return this.parseHoleStatement();
        }
        else {
            return this.parseStatementExpression();
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

        const itest = this.parseITestGuardSet();
        const ifbody = this.parseScopedBlockStatement();

        let conds: {cond: Expression, block: BlockStatement}[] = [];
        while (this.testAndConsumeTokenIf(KW_elif)) {
            const kiexp = this.parseExpression();
            const elifbody = this.parseScopedBlockStatement();

            conds.push({cond: kiexp, block: elifbody});
        }

        if(conds.length === 0) {
            if(!this.testAndConsumeTokenIf(KW_else)) {
                return new IfStatement(sinfo, itest, ifbody);
            }
            else {
                const elsebody = this.parseScopedBlockStatement();
                return new IfElseStatement(sinfo, itest, ifbody, elsebody);
            }
        }
        else {
            this.ensureAndConsumeTokenIf(KW_else, "if-elif-else statement");

            let itexp: Expression = new ErrorExpression(sinfo, undefined, undefined);
            if(itest.guards.length === 1 && itest.guards[0] instanceof ITestSimpleGuard) {
                itexp = itest.guards[0].exp;
            }
            else {
                this.recordErrorGeneral(sinfo, "Cannot have a binder in an if-elif-else statement");
            }

            const elssebody = this.parseScopedBlockStatement();
            return new IfElifElseStatement(sinfo, [{cond: itexp, block: ifbody}, ...conds], elssebody);
        }
    }

    private parseSwitchStatement(): Statement {
        const sinfo = this.peekToken().getSourceInfo();
        
        this.ensureAndConsumeTokenAlways(KW_switch, "switch statement dispatch value");

        this.ensureAndConsumeTokenAlways(SYM_lparen, "switch statement dispatch value");
        const sexp = this.parseExpression();
        this.ensureAndConsumeTokenAlways(SYM_rparen, "switch statement dispatch value");

        let entries: { lval: Expression | undefined, value: BlockStatement }[] = [];
        this.ensureAndConsumeTokenAlways(SYM_lbrace, "switch statement options");
        
        this.ensureAndConsumeTokenAlways(SYM_bar, "switch statement entry");
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

        const sguard = this.parseITestGuard();

        let entries: { mtype: TypeSignature | undefined, value: BlockStatement }[] = [];
        this.ensureAndConsumeTokenAlways(SYM_lbrace, "match statement options");

        this.ensureAndConsumeTokenAlways(SYM_bar, "match statement entry");
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


        return new MatchStatement(sinfo, sguard, entries);
    }

    private parseDispatchStatement(): Statement {
        const sinfo = this.peekToken().getSourceInfo();

        this.ensureAndConsumeTokenAlways(KW_dispatch, "dispatch statement target");

        const dguard = this.parseITestGuard();

        this.ensureAndConsumeTokenAlways(SYM_lbrace, "dispatch statement options");

        this.ensureAndConsumeTokenAlways(SYM_bar, "dispatch statement entry");
        const dtype = this.parseDispatchGuard();
        this.ensureAndConsumeTokenIf(SYM_bigarrow, "dispatch statement entry");
        const dvalue = this.parseScopedBlockStatement();

        if(dtype === undefined || Array.isArray(dtype)) {
            let entries: { kidx: string | undefined, value: BlockStatement }[] = [];
            entries.push({ kidx: dtype !== undefined ? dtype[0] : undefined, value: dvalue });

            while (this.testToken(SYM_bar)) {
                this.consumeToken();

                const dtypex = this.parseDispatchGuard();
                let dd: string | undefined;
                if(dtypex === undefined) {
                    dd = undefined;
                }
                else if(Array.isArray(dtypex)) {
                    dd = dtypex[0];
                }
                else {
                    this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Mixed dispatch type guard styles in dispatch statement");
                    dd = undefined;
                }

                this.ensureAndConsumeTokenIf(SYM_bigarrow, "dispatch statement entry");
                const dvaluex = this.parseScopedBlockStatement();

                entries.push({ kidx: dd, value: dvaluex });
            }
            this.ensureAndConsumeTokenAlways(SYM_rbrace, "dispatch statement options");

            return new DispatchTaskStatement(sinfo, dguard, entries);
        }
        else {
            let entries: { kidx: Expression | undefined, value: BlockStatement }[] = [];
            entries.push({ kidx: dtype, value: dvalue });

            while (this.testToken(SYM_bar)) {
                this.consumeToken();

                const dtypex = this.parseDispatchGuard();
                let dd: Expression | undefined;
                if(dtypex === undefined) {
                    dd = undefined;
                }
                else if(!Array.isArray(dtypex)) {
                    dd = dtypex;
                }
                else {
                    this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Mixed dispatch type guard styles in dispatch statement");
                    dd = undefined;
                }

                this.ensureAndConsumeTokenIf(SYM_bigarrow, "dispatch statement entry");
                const dvaluex = this.parseScopedBlockStatement();

                entries.push({ kidx: dd, value: dvaluex });
            }
            this.ensureAndConsumeTokenAlways(SYM_rbrace, "dispatch statement options");

            return new DispatchPatternStatement(sinfo, dguard, entries);
        }
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
        else if (this.testToken(KW_dispatch)) {
            return this.parseDispatchStatement();
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

            this.ensureAndConsumeTokenAlways(SYM_at, "expression body");
            this.ensureToken(TokenStrings.IdentifierName, "body");
            const iname = this.parseIdentifierAsStdVariable();
            this.ensureAndConsumeTokenAlways(SYM_semicolon, "body");

            return new BuiltinBodyImplementation(sinfo, this.env.currentFile, iname);
        }
        else if(this.testFollows(SYM_lbrace, SYM_HOLE)) {
            this.consumeToken(); //{
            this.consumeToken(); //HOLE

            let hname: string | undefined = undefined;
            if(this.testToken(TokenStrings.IdentifierName)) {
                hname = this.consumeTokenAndGetValue();
            }

            let doccomment: string | undefined = undefined;
            if(this.testToken(SYM_lparen)) {
                this.consumeToken();
                this.ensureToken(TokenStrings.DocComment, "hole expression");
                doccomment = this.consumeTokenAndGetValue();
                this.ensureAndConsumeTokenAlways(SYM_rparen, "hole expression");
            }

            let samplesfile: Expression | undefined = undefined;
            if(this.testToken(KW_of)) {
                this.consumeToken();
                samplesfile = this.parseExpression();
            }

            this.ensureAndConsumeTokenAlways(SYM_rbrace, "hole body");

            return new HoleBodyImplementation(sinfo, this.env.currentFile, hname, doccomment, samplesfile);
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
                this.scanOverSemiDelimitedDeclaration();
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

            if(this.testToken(KW_as)) {
                this.consumeToken();
                this.ensureToken(TokenStrings.IdentifierName, "namespace import");
                this.parseIdentifierAsNamespaceOrTypeName();
            }
        }
    }

    private parseNamespaceMembers() {
        const rpos = this.scanToRecover(SYM_rbrace);
        this.prepStateStackForNested("namespace", rpos);

        while (!this.testToken(SYM_rbrace) && !this.testToken(TokenStrings.EndOfStream) && !this.testToken(TokenStrings.Recover)) {
            let attributes: DeclarationAttibute[] = [];
            while(this.testToken(TokenStrings.Attribute) || this.testToken(TokenStrings.DocComment)) {
                const attr = this.parseAttribute();
                attributes.push(attr);
            }

            const sinfo = this.peekToken().getSourceInfo();
            if (this.testToken(KW_const)) {
                this.parseNamespaceConstant(attributes);
            }
            else if(this.testFollows(KW_function) || this.testFollows(KW_recursive, KW_function) || this.testFollows(KW_recursive_q, KW_function)) {
                this.parseNamespaceFunction(attributes);
            }
            else if(this.testFollows(KW_predicate)) {
                this.parseNamespaceFunction(attributes);
            }
            else if(this.testFollows(KW_chktest) || this.testFollows(KW_errtest) || this.testFollows(KW_example)) {
                this.parseNamespaceFunction(attributes);
            }
            else if(this.testFollows(KW_entity) || this.testFollows(KW_status, KW_entity) || this.testFollows(KW_event, KW_entity)) {
                this.parseEntity(attributes);
            }
            else if(this.testFollows(KW_concept) || this.testFollows(KW_status, KW_concept) || this.testFollows(KW_event, KW_concept)) {
                this.parseConcept(attributes);
            }
            else if(this.testFollows(KW_enum) || this.testFollows(KW_status, KW_enum) || this.testFollows(KW_event, KW_enum)) {
                this.parseEnum(attributes);
            }
            else if(this.testFollows(KW_type) || this.testFollows(KW_status, KW_type) || this.testFollows(KW_event, KW_type)) {
                this.parseTypeDecl(attributes);
            }
            else if(this.testFollows(KW_datatype) || this.testFollows(KW_status, KW_datatype) || this.testFollows(KW_event, KW_datatype)) {
                this.parseDataTypeDecl(attributes);
            }
            else if(this.testToken(KW_task)) {
                this.parseTask(attributes);
            }
            else if(this.testToken(KW_api)) {
                this.parseAPI(attributes);
            }
            else if(this.testToken(KW_agent)) {
                this.parseAgent(attributes);
            }
            else if(this.testToken(KW_namespace)) {
                this.parseSubNamespace();
            }
            else {
                this.recordErrorGeneral(sinfo, `Unknown member ${this.peekTokenData()}`);

                this.currentState().skipToPosition(rpos);
            }
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
            this.parseNamespaceMembers();
            this.ensureAndConsumeTokenAlways(SYM_rbrace, "nested namespace declaration");

            this.env.currentNamespace = ons;
        }
        else {
            const ons = this.env.currentNamespace;

            const nsdecl = this.env.currentNamespace.subns.find((ns) => ns.name === nsname) as NamespaceDeclaration;
            nsdecl.usings = ons.usings;

            this.env.currentNamespace = nsdecl;
            this.ensureAndConsumeTokenAlways(SYM_lbrace, "nested namespace declaration");
            this.parseNamespaceMembers();
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
            this.env.currentNamespace.declaredNames.add(sname);
            this.env.currentNamespace.declaredConstNames.add(sname);

            this.scanOverSemiDelimitedDeclaration();
        }
        else {
            if(this.env.currentNamespace.checkDeclNameClashMemberSimple(sname)) {
                const mconst = this.env.currentNamespace.consts.find((cc) => cc.name === sname);
                const mfunc = this.env.currentNamespace.functions.find((ff) => ff.name === sname);

                if(mconst !== undefined || mfunc !== undefined) {
                    this.recordErrorGeneral(sinfo, `Collision between const and other names -- ${sname}`);
                }
            }

            this.ensureAndConsumeTokenIf(SYM_colon, "const member");
            const stype = this.parseStdTypeSignature();

            this.ensureAndConsumeTokenIf(SYM_eq, "const member");
            const value = this.parseConstScopedExpression(stype, new Set<string>());
        
            this.env.currentNamespace.consts.push(new ConstMemberDecl(this.env.currentFile, sinfo, attributes, sname, stype, value));

            this.ensureAndConsumeTokenIf(SYM_semicolon, "const member");
        }
    }

    private parseNamespaceFunction(attributes: DeclarationAttibute[]) {
        const sinfo = this.peekToken().getSourceInfo();

        if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterNames)) {
            this.consumeTokenIf(KW_recursive);
            this.consumeTokenIf(KW_recursive_q);
            this.consumeToken();

            const fname = this.consumeTokenAndGetValue();
            this.env.currentNamespace.declaredNames.add(fname);
            this.env.currentNamespace.declaredFunctionNames.add(fname);

            const allowcorebi = this.env.currentNamespace.topnamespace === "Core";
            this.scanOverBraceDelimitedDeclaration(allowcorebi);
        }
        else {
            let fkind: "namespace" | "predicate" | "chktest" | "errtest" | "example" = "namespace";
            if(this.testToken(KW_predicate)) {
                fkind = "predicate";
            }
            else if(this.testToken(KW_chktest)) {
                fkind = "chktest";
            }
            else if(this.testToken(KW_errtest)) {
                fkind = "errtest";
            }
            else if(this.testToken(KW_example)) {
                fkind = "example";
            }
            else {
                ;
            }

            const fdecl = this.parseFunctionInvokeDecl(fkind, attributes, new Set<string>());

            if(fdecl === undefined) {
                return;
            }

            if(this.env.currentNamespace.checkDeclNameClashMemberSimple(fdecl.name)) {
                const mconst = this.env.currentNamespace.consts.find((cc) => cc.name === fdecl.name);
                const mfunc = this.env.currentNamespace.functions.find((ff) => Assembly.checkFunctionSigMatch(ff, fdecl));

                if(mconst !== undefined || mfunc !== undefined) {
                    this.recordErrorGeneral(sinfo, `Collision between function and other names -- ${fdecl.name}`);
                }
            }

            this.env.currentNamespace.functions.push(fdecl as NamespaceFunctionDecl);
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

    private parseConstMember(constMembers: ConstMemberDecl[] | undefined, allMemberNames: Set<string>, attributes: DeclarationAttibute[], typeTerms: Set<string>) {
        assert(isParsePhase_Enabled(this.currentPhase, ParsePhase_CompleteParsing));

        const sinfo = this.peekToken().getSourceInfo();
        this.ensureAndConsumeTokenAlways(KW_const, "const member");

        this.ensureToken(TokenStrings.IdentifierName, "const member");
        const sname = this.parseIdentifierAsStdVariable();

        this.ensureAndConsumeTokenIf(SYM_colon, "const member");
        const stype = this.parseStdTypeSignature();

        this.ensureAndConsumeTokenIf(SYM_eq, "const member");
        const value = this.parseConstScopedExpression(stype, typeTerms);

        if(constMembers === undefined) {
            this.recordErrorGeneral(sinfo, "Cannot have a const member on this type");
        }
        if(allMemberNames.has(sname)) {
            this.recordErrorGeneral(sinfo, `Duplicate const member ${sname}`);
        }
        allMemberNames.add(sname);

        if(constMembers !== undefined) {
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
        
        if(memberFunctions !== undefined && allMemberNames.has(fdecl.name)) {
            const ffdecl = memberFunctions.find((mf) => Assembly.checkFunctionSigMatch(mf, fdecl));
            const fndecl = memberFunctions.find((mf) => mf.name === fdecl.name);

            if(fndecl === undefined) {
                this.recordErrorGeneral(sinfo, `Duplicate member ${fdecl.name} with same name`);
            }
            if(fndecl !== undefined && ffdecl !== undefined) {
                this.recordErrorGeneral(sinfo, `Duplicate member ${fdecl.name} with same signature`);
            }
        }
        allMemberNames.add(fdecl.name);

        if(memberFunctions !== undefined) {
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

        let ivalue: Expression | undefined = undefined;
        if (this.testAndConsumeTokenIf(SYM_eq)) {
            ivalue = this.parseConstScopedExpression(ftype, typeTerms);
        }

        if(memberFields === undefined) {
            this.recordErrorGeneral(sinfo, "Cannot have a field member on this type");
        }
        if(allMemberNames.has(fname)) {
            this.recordErrorGeneral(sinfo, `Duplicate field member ${fname}`);
        }
        allMemberNames.add(fname);

        if(memberFields !== undefined) {
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
        
        if(memberMethods !== undefined && allMemberNames.has(mdecl.name)) {
            const mfdecl = memberMethods.find((mf) => Assembly.checkMethodSigMatch(mf, mdecl));
            const mndecl = memberMethods.find((mf) => mf.name === mdecl.name);

            if(mndecl === undefined) {
                this.recordErrorGeneral(sinfo, `Duplicate member ${mdecl.name} with same name`);
            }
            if(mndecl !== undefined && mfdecl !== undefined) {
                this.recordErrorGeneral(sinfo, `Duplicate member ${mdecl.name} with same signature`);
            }
        }
        allMemberNames.add(mdecl.name);

        if(memberMethods !== undefined) {
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

        if(taskMemberMethods !== undefined) {
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

        if(taskMemberAction !== undefined) {
            taskMemberAction.push(adecl);
        }
    }

    private parseInvariantsInto(invs: InvariantDecl[] | undefined, vdates: ValidateDecl[] | undefined, typeTerms: Set<string>) {
        assert(isParsePhase_Enabled(this.currentPhase, ParsePhase_CompleteParsing));

        while (this.testToken(KW_invariant) || this.testToken(KW_validate)) {
            const sinfo = this.peekToken().getSourceInfo();
            
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
                const exp = this.parseChkLogicScopedExpression(typeTerms);

                if(vdates === undefined) {
                    this.recordErrorGeneral(sinfo, "Cannot have a validate on this type");
                }
                else {
                    vdates.push(new ValidateDecl(this.env.currentFile, sinfo, vdates.length, tag, exp));
                }
            }
            else {
                const level = this.parseBuildInfo(KW_release);
                const exp = this.parseChkLogicScopedExpression(typeTerms);

                if(invs === undefined) {
                    this.recordErrorGeneral(sinfo, "Cannot have an invariant on this type");
                }
                else {
                    invs.push(new InvariantDecl(this.env.currentFile, sinfo, invs.length, tag, level, exp));
                }
            }

            this.ensureAndConsumeTokenIf(SYM_semicolon, "invariant");
        }
    }

    private parseOOPMembersCommonAll(istask: boolean, specialConcept: InternalConceptTypeDecl | undefined, typeTerms: Set<string>,
        invariants: InvariantDecl[] | undefined, validates: ValidateDecl[] | undefined,
        constMembers: ConstMemberDecl[] | undefined, functionMembers: TypeFunctionDecl[] | undefined, 
        memberFields: MemberFieldDecl[] | undefined, memberMethods: MethodDecl[] | undefined, 
        taskMemberMethods: TaskMethodDecl[] | undefined, taskMemberAction: TaskActionDecl[] | undefined) {
        let allMemberNames = new Set<string>();

        const rpos = this.scanMatchingParens(SYM_lbrace, SYM_rbrace);
        this.prepStateStackForNested("oop-members", rpos);

        this.ensureAndConsumeTokenAlways(SYM_lbrace, "type members");

        while (!this.testToken(SYM_rbrace) && !this.testToken(TokenStrings.EndOfStream) && !this.testToken(TokenStrings.Recover)) {
            let attributes: DeclarationAttibute[] = [];
            while(this.testToken(TokenStrings.Attribute) || this.testToken(TokenStrings.DocComment)) {
                const attr = this.parseAttribute();
                attributes.push(attr);
            }

            const sinfo = this.peekToken().getSourceInfo();
            if (this.testToken(KW_field)) {
                this.parseMemberField(memberFields, allMemberNames, attributes, typeTerms);
            }
            else if (this.testToken(KW_invariant) || this.testToken(KW_validate)) {
                this.parseInvariantsInto(invariants, validates, typeTerms);
            }
            else if (this.testToken(KW_const)) {
                this.parseConstMember(constMembers, allMemberNames, attributes, typeTerms);
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
                this.parseTaskMemberAction(taskMemberAction, allMemberNames, attributes, typeTerms, "main");
            }
            else if(this.testToken(KW_entity)) {
                if(specialConcept === undefined) {
                    this.recordErrorGeneral(this.peekToken().getSourceInfo(), "Cannot have nested entities on this type");

                    //scan to the next declaration or end brace
                    this.currentState().moveToRecoverPosition();
                    this.popStateIntoParentOk();
                    return;
                }
                else {
                    this.parseNestedEntity(specialConcept, attributes, typeTerms);
                }
            }
            else {
                this.recordErrorGeneral(sinfo, `Unknown member ${this.peekTokenData()}`);
                this.currentState().moveToRecoverPosition();
                this.popStateIntoParentOk();
                return;
            }
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

            this.parseOOPMembersCommonAll(false, undefined, typeTerms, undefined, undefined, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined);
        }
        else {
            const tdecl = (specialConcept as APIResultTypeDecl).nestedEntityDecls.find((ned) => ned.name === ename) as InternalEntityTypeDecl;

            const provides = this.parseProvides();
            if(provides.length !== 0) {
                tdecl.provides.push(...provides);
            }

            this.parseOOPMembersCommonAll(false, undefined, typeTerms, undefined, undefined, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined);
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
            this.parseOOPMembersCommonAll(false, undefined, new Set<string>(), undefined, undefined, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined);
        }
        else if(tdecl instanceof SomeTypeDecl) {
            this.parseOOPMembersCommonAll(false, undefined, new Set<string>("T"), undefined, undefined, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined);
        }
        else if(tdecl instanceof ListTypeDecl || tdecl instanceof StackTypeDecl || tdecl instanceof QueueTypeDecl || tdecl instanceof SetTypeDecl) {
            this.parseOOPMembersCommonAll(false, undefined, new Set<string>("T"), undefined, undefined, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined);
        }
        else if(tdecl instanceof MapEntryTypeDecl) {
            this.parseOOPMembersCommonAll(false, undefined, new Set<string>(["K", "V"]), undefined, undefined, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined);
        }
        else if(tdecl instanceof MapTypeDecl) {
            this.parseOOPMembersCommonAll(false, undefined, new Set<string>(["K", "V"]), undefined, undefined, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined);
        }
        else if(tdecl instanceof EventListTypeDecl) {
            this.parseOOPMembersCommonAll(false, undefined, new Set<string>("T"), undefined, undefined, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined);
        }
        else {
            const edecl = tdecl as EntityTypeDecl;
            this.parseOOPMembersCommonAll(false, undefined, new Set<string>(edecl.terms.map((term) => term.name)), edecl.invariants, edecl.validates, edecl.consts, edecl.functions, edecl.fields, edecl.methods, undefined, undefined);
        }
    }

    private parseEntity(attributes: DeclarationAttibute[]) {
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

            this.scanOverBraceDelimitedDeclaration();
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
            if(ename === "APIErrorTypeDecl") {
                rdecl.nestedEntityDecls.push(new APIErrorTypeDecl(this.env.currentFile, sinfo, attributes, ename));
            }
            else if(ename === "APIRejectedTypeDecl") {
                rdecl.nestedEntityDecls.push(new APIRejectedTypeDecl(this.env.currentFile, sinfo, attributes, ename));
            }
            else if(ename === "APIDeniedTypeDecl") {
                rdecl.nestedEntityDecls.push(new APIDeniedTypeDecl(this.env.currentFile, sinfo, attributes, ename));
            }
            else if(ename === "APIFlaggedTypeDecl") {
                rdecl.nestedEntityDecls.push(new APIFlaggedTypeDecl(this.env.currentFile, sinfo, attributes, ename));
            }
            else {
                rdecl.nestedEntityDecls.push(new APISuccessTypeDecl(this.env.currentFile, sinfo, attributes, ename));
            }   
        }

        this.scanOverBraceDelimitedDeclaration();
    }

    private parseConceptRegisterType(sinfo: SourceInfo, attributes: DeclarationAttibute[], name: string, etag: AdditionalTypeDeclTag) {
        let tdecl: AbstractNominalTypeDecl | undefined = undefined;

        if(this.env.currentNamespace.fullnamespace.ns[0] === "Core") {
            if(name === "Option") {
                tdecl = new OptionTypeDecl(this.env.currentFile, sinfo, attributes, "Option");

                this.scanOverBraceDelimitedDeclaration();
            }
            else if(name === "Result") {
                tdecl = new ResultTypeDecl(this.env.currentFile, sinfo, attributes, "Result");

                this.scanToKWOptsInDeclaration(SYM_lbrace);
                this.consumeToken();
                this.parseNestedEntityRegisterType(tdecl);
                this.parseNestedEntityRegisterType(tdecl);

                this.scanToKWOptsInDeclaration(SYM_rbrace);
                this.consumeToken();
            }
            else if(name === "APIResult") {
                tdecl = new APIResultTypeDecl(this.env.currentFile, sinfo, attributes, "APIResult");

                this.scanToKWOptsInDeclaration(SYM_lbrace);
                this.consumeToken();
                this.parseNestedEntityRegisterType(tdecl);
                this.parseNestedEntityRegisterType(tdecl);
                this.parseNestedEntityRegisterType(tdecl);
                this.parseNestedEntityRegisterType(tdecl);
                this.parseNestedEntityRegisterType(tdecl);

                this.scanToKWOptsInDeclaration(SYM_rbrace);
                this.consumeToken();
            }
            else {
                assert(false, "Unknown special concept type -- " + name);
            }
        }
        else {
            assert(!attributes.some((attr) => attr.name === "__internal"), "Missing special case on primitive concept parse");

            tdecl = new ConceptTypeDecl(this.env.currentFile, sinfo, attributes, this.env.currentNamespace.fullnamespace, name, etag);

            this.scanOverBraceDelimitedDeclaration();
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
            this.parseOOPMembersCommonAll(false, undefined, new Set<string>("T"), undefined, undefined, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined);
        }
        else if(tdecl instanceof ResultTypeDecl) {
            this.parseOOPMembersCommonAll(false, tdecl, new Set<string>(["T", "E"]), undefined, undefined, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined);
        }
        else if(tdecl instanceof APIResultTypeDecl) {
            this.parseOOPMembersCommonAll(false, tdecl, new Set<string>(["T", "E"]), undefined, undefined, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined);
        }
        else {
            const cdecl = tdecl as ConceptTypeDecl;
            this.parseOOPMembersCommonAll(false, undefined, new Set<string>(cdecl.terms.map((term) => term.name)), cdecl.invariants, cdecl.validates, cdecl.consts, cdecl.functions, cdecl.fields, cdecl.methods, undefined, undefined);
        }
    }

    private parseConcept(attributes: DeclarationAttibute[]) {
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
        }
        else {
            this.parseConceptCompleteParse(sinfo, ename);
        }
    }
    
    private parseEnum(attributes: DeclarationAttibute[]) {
        const sinfo = this.peekToken().getSourceInfo();

        const etag: AdditionalTypeDeclTag = this.parseAdditionalTypeDeclTag();
        this.ensureAndConsumeTokenAlways(KW_enum, "enum declaration");
        this.ensureToken(TokenStrings.IdentifierName, "enum declaration");
        const ename = this.parseIdentifierAsNamespaceOrTypeName();

        if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterNames)) {
            if(this.env.currentNamespace.checkDeclNameClashType(ename, false)) {
                this.recordErrorGeneral(sinfo, `Collision between enum and other names -- ${ename}`);
            }

            const members = this.parseListOf<string>("enum members", SYM_lbrace, SYM_rbrace, SYM_coma, () => {
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

            this.scanOverBraceDelimitedDeclaration();
        }
    }

    private parseTypeDecl(attributes: DeclarationAttibute[]) {
        const sinfo = this.peekToken().getSourceInfo();

        const etag: AdditionalTypeDeclTag = this.parseAdditionalTypeDeclTag();
        this.ensureAndConsumeTokenAlways(KW_type, "type alias declaration");
        this.ensureToken(TokenStrings.IdentifierName, "type alias declaration");
        const iname = this.parseIdentifierAsNamespaceOrTypeName();

        this.ensureAndConsumeTokenIf(SYM_eq, "type declaration");

        if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterNames)) {
            if(this.env.currentNamespace.checkDeclNameClashType(iname, false)) {
                this.recordErrorGeneral(sinfo, `Collision between type and other names -- ${iname}`);
            }

            const tdecl = new TypedeclTypeDecl(this.env.currentFile, sinfo, attributes, this.env.currentNamespace.fullnamespace, iname, etag, new ErrorTypeSignature(sinfo, undefined));
            this.env.currentNamespace.typedecls.push(tdecl);

            this.env.currentNamespace.declaredNames.add(iname);
            this.env.currentNamespace.declaredTypeNames.push({name: iname, hasterms: this.testToken(SYM_langle)});

            this.scanToKWOptsInDeclaration(SYM_lbrace, SYM_semicolon);
            if(!this.testAndConsumeTokenIf(SYM_semicolon)) {
                if(this.peekTokenKind(1) === TokenStrings.Nat || this.peekTokenKind(1) === SYM_coma) {
                    this.consumeToken();
                    this.ensureAndConsumeTokenIf(TokenStrings.Nat, "type declaration size min");
                    this.ensureAndConsumeTokenAlways(SYM_coma, "type declaration size range");
                    this.ensureAndConsumeTokenIf(TokenStrings.Nat, "type declaration size max");
                    this.ensureAndConsumeTokenAlways(SYM_rbrace, "type declaration size range");
                }

                this.scanOverBraceDelimitedDeclaration();
            }
        }
        else {
            const tdecl = this.env.currentNamespace.typedecls.find((td) => td.name === iname);
            assert(tdecl !== undefined && (tdecl instanceof TypedeclTypeDecl), "Failed to find type type");

            const ttype = this.parseTypedeclRHSSignature();
            (tdecl as TypedeclTypeDecl).valuetype = ttype;

            if(this.testAndConsumeTokenIf(SYM_lbrace)) {;
                let min: string | undefined = undefined;
                let max: string | undefined = undefined;

                if(this.testToken(TokenStrings.Nat)) {
                    min = this.consumeTokenAndGetValue();
                }
                this.ensureAndConsumeTokenAlways(SYM_coma, "type declaration size range");
                if(this.testToken(TokenStrings.Nat)) {
                    max = this.consumeTokenAndGetValue();
                }

                this.ensureAndConsumeTokenAlways(SYM_rbrace, "type declaration size range");

                (tdecl as TypedeclTypeDecl).optsizerng = { min: min, max: max };
            }

            if(this.testAndConsumeTokenIf(KW_of)) {
                const ofexp = this.parseConstScopedExpression(undefined, new Set<string>());
                (tdecl as TypedeclTypeDecl).optofexp = ofexp;
            }

            if(!this.testAndConsumeTokenIf(SYM_semicolon)) {
                this.ensureAndConsumeTokenIf(SYM_amp, "type declaration");

               const provides = this.parseProvides();
                if(provides.length !== 0) {
                    tdecl.provides.push(...provides);
                }

                this.parseOOPMembersCommonAll(false, undefined, new Set<string>(), tdecl.invariants, tdecl.validates, tdecl.consts, tdecl.functions, undefined, tdecl.methods, undefined, undefined);
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

            this.scanOverBraceDelimitedDeclaration();
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
                this.parseOOPMembersCommonAll(false, undefined, new Set<string>(parenttype.terms.map((term) => term.name)), tdecl.invariants, tdecl.validates, tdecl.consts, tdecl.functions, (tdecl as DatatypeMemberEntityTypeDecl).fields, tdecl.methods, undefined, undefined);
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

            this.scanToKWOptsInDeclaration(KW_of);
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
                    this.parseOOPMembersCommonAll(false, undefined, new Set<string>(tdecl.terms.map((term) => term.name)), tdecl.invariants, tdecl.validates, tdecl.consts, tdecl.functions, tdecl.fields, tdecl.methods, undefined, undefined);
                    if(tdecl.functions.length !== 0 || tdecl.methods.length !== 0) {
                        this.recordErrorGeneral(sinfo, "Using component cannot include functions or methods");
                    }
                }
            }
        }

        if(!this.testAndConsumeTokenIf(KW_of)) {
            //missing something so skip to known position
            this.recordErrorGeneral(sinfo, "Missing clause in datatype declaration");
            
            this.currentState().moveToRecoverPosition();
            return;
        }

        while (!this.testToken(SYM_semicolon) && !this.testToken(SYM_amp) && !this.testToken(TokenStrings.EndOfStream) && !this.testToken(TokenStrings.Recover)) {
            this.ensureAndConsumeTokenAlways(SYM_bar, "datatype member");
            this.parseDatatypeMemberEntityTypeDecl(attributes, tdecl, hasTerms, etag);
        }

        if(this.testAndConsumeTokenIf(SYM_amp)) {
            if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterNames)) {
                this.scanOverBraceDelimitedDeclaration();
            }
            else {
                this.parseOOPMembersCommonAll(false, undefined, new Set<string>(tdecl.terms.map((tt) => tt.name)), tdecl.invariants, tdecl.validates, tdecl.consts, tdecl.functions, tdecl.fields, tdecl.methods, undefined, undefined);
            }
        }

        this.testAndConsumeTokenIf(SYM_semicolon);
    }

    private parseStatusInfo(statusinfo: TypeSignature[]) {
        this.consumeToken();

        statusinfo.push(this.parseNominalType());
        while(this.testAndConsumeTokenIf(SYM_bar)) {
            statusinfo.push(this.parseNominalType());
        }

        this.ensureAndConsumeTokenAlways(SYM_semicolon, "task status section");
    }

    private parseResourceInfo(resinfo: ResourceInformation) {
        this.consumeToken();
        const rri = this.parseListOf<{ pg: Expression[], optas: Expression | undefined }>("resource section", SYM_lbrace, SYM_rbrace, SYM_coma, () => {
            let pg: Expression[] = [];
            let optas: Expression | undefined = undefined;

            if(this.testToken(SYM_lbrack)) {
                pg = this.parseListOf<Expression>("pathglob expression", SYM_lbrack, SYM_rbrack, SYM_coma, () => {
                    return this.parseConstScopedExpression(undefined, new Set<string>());
                });
            }
            else {
                pg.push(this.parseConstScopedExpression(undefined, new Set<string>()));
            }

            if(this.testAndConsumeTokenIf(KW_as)) {
                optas = this.parseConstScopedExpression(undefined, new Set<string>());
            }

            return { pg: pg, optas: optas };
        });

        resinfo.pathglobs.push(...rri);
    }

    private parseEnvInfo(envinfo: EnvironmentVariableInformation[]) {
        this.consumeToken();

        let ei = this.parseListOf<EnvironmentVariableInformation>("env section", SYM_lbrace, SYM_rbrace, SYM_coma, () => {
            let ename = "";
            if(this.testToken(TokenStrings.CString)) {
                ename = this.consumeTokenAndGetValue();
            }
            else {
                this.ensureToken(TokenStrings.IdentifierName, "env section");
                ename = this.consumeTokenAndGetValue();
            }

            const isoptional = this.testAndConsumeTokenIf(SYM_question);
            this.ensureAndConsumeTokenIf(SYM_colon, "task env section");
            const ttype = this.parseStdTypeSignature();
                        
            let exp: Expression | undefined = undefined;
            if(this.testAndConsumeTokenIf(SYM_eq)) {
                exp = this.parseConstScopedExpression(ttype, new Set<string>());
            }

            return new EnvironmentVariableInformation(ename, ttype, !isoptional, exp);
        });

        envinfo.push(...ei);
    }

    private parseTask(attributes: DeclarationAttibute[]) {
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

            this.scanOverBraceDelimitedDeclaration();
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

            while(this.testToken(KW_status) || this.testToken(KW_resource) || this.testToken(KW_env) || this.testToken(KW_event) ||this.testToken(KW_configs) ) {
                if(this.testToken(KW_event)) {
                    if(tdecl.eventinfo.length !== 0) {
                        this.recordErrorGeneral(sinfo, "Cannot have multiple event sections");
                    }
    
                    this.consumeToken();
                    tdecl.eventinfo.push(this.parseNominalType());
                    while(this.testAndConsumeTokenIf(SYM_bar)) {
                        tdecl.eventinfo.push(this.parseNominalType());
                    }

                    this.ensureAndConsumeTokenAlways(SYM_semicolon, "task event section");
                }
                else if(this.testToken(KW_configs)) {
                    if(tdecl.configs.priority !== undefined || tdecl.configs.retry !== undefined || tdecl.configs.timeout !== undefined) {
                        this.recordErrorGeneral(sinfo, "Cannot have multiple config sections");
                    }

                    this.consumeToken();
                    this.ensureAndConsumeTokenAlways(SYM_lbrace, "task configs section");

                    this.parseTaskConfigs(tdecl.configs);

                    this.ensureAndConsumeTokenAlways(SYM_rbrace, "task configs section");
                }
                else if(this.testToken(KW_status)) {
                    if(tdecl.statusinfo.length !== 0) {
                        this.recordErrorGeneral(sinfo, "Cannot have multiple status sections");
                    }

                    this.parseStatusInfo(tdecl.statusinfo);
                }
                else if(this.testToken(KW_resource)) {
                    if(tdecl.resourcereqs.pathglobs.length !== 0) {
                        this.recordErrorGeneral(sinfo, "Cannot have multiple resource sections");
                    }

                    this.parseResourceInfo(tdecl.resourcereqs);
                }
                else {
                    if(tdecl.envreqs.length !== 0) {
                        this.recordErrorGeneral(sinfo, "Cannot have multiple env sections");
                    }

                    this.parseEnvInfo(tdecl.envreqs);
                }
            }

            this.parseOOPMembersCommonAll(true, undefined, new Set<string>(tdecl.terms.map((term) => term.name)), tdecl.invariants, tdecl.validates, tdecl.consts, tdecl.functions, tdecl.fields, undefined, tdecl.selfmethods, tdecl.actions);
        }
    }

    private parseAPI(attributes: DeclarationAttibute[]) {
        const sinfo = this.peekToken().getSourceInfo();

        this.ensureAndConsumeTokenAlways(KW_api, "api declaration");
        this.ensureToken(TokenStrings.IdentifierName, "api declaration");
        const apiname = this.parseIdentifierAsStdVariable();

        if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterNames)) {
            if(this.env.currentNamespace.checkDeclNameClashMemberSimple(apiname)) {
                this.recordErrorGeneral(sinfo, `Collision between API and other names -- ${apiname}`);
            }

            this.env.currentNamespace.declaredNames.add(apiname);
            this.env.currentNamespace.declaredAPINames.add(apiname);

            this.scanOverSemiDelimitedDeclaration();
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
            const resultInfo = this.parseReturnTypeSignature(true);

            let eventType: TypeSignature | undefined = undefined;
            if(this.testAndConsumeTokenIf(SYM_coma)) {
                eventType = this.parseNominalType();
            }

            const argNames = new Set<string>(params.map((param) => param.name));
            const cargs = params.map((param) => new VariableDefinitionInfo(param.pkind || "let", param.name));

            const [preconds, postconds] = this.parsePreAndPostConditions(sinfo, argNames, new Set<string>(), new Set<string>(), true, true);
    
            let configs: TaskConfiguration = new TaskConfiguration(undefined, undefined, undefined);
            let statusinfo: TypeSignature[] = [];
            let resourcereqs: ResourceInformation = new ResourceInformation([]);
            let envreqs: EnvironmentVariableInformation[] = [];
            while(this.testToken(KW_status) || this.testToken(KW_resource) || this.testToken(KW_env) || this.testToken(KW_configs)) {
                if(this.testToken(KW_configs)) {
                    if(configs.priority !== undefined || configs.retry !== undefined || configs.timeout !== undefined) {
                        this.recordErrorGeneral(sinfo, "Cannot have multiple config sections");
                    }

                    this.consumeToken();
                    this.ensureAndConsumeTokenAlways(SYM_lbrace, "task configs section");

                    this.parseTaskConfigs(configs);

                    this.ensureAndConsumeTokenAlways(SYM_rbrace, "task configs section");
                }
                else if(this.testToken(KW_status)) {
                    if(statusinfo.length !== 0) {
                        this.recordErrorGeneral(sinfo, "Cannot have multiple status sections");
                    }

                    this.parseStatusInfo(statusinfo);
                }
                else if(this.testToken(KW_resource)) {
                    if(resourcereqs.pathglobs.length !== 0) {
                        this.recordErrorGeneral(sinfo, "Cannot have multiple resource sections");
                    }

                    this.parseResourceInfo(resourcereqs);
                }
                else {
                    if(envreqs.length !== 0) {
                        this.recordErrorGeneral(sinfo, "Cannot have multiple env sections");
                    }

                    this.parseEnvInfo(envreqs);
                }
            }

            this.env.pushStandardFunctionScope(cargs, boundtemplates, resultInfo);
            const body = this.parseBody(attributes, false, false);
            this.env.popStandardFunctionScope();
            
            const api = new APIDecl(this.env.currentFile, sinfo, attributes, apiname, params, resultInfo, eventType, preconds, postconds, configs, statusinfo, envreqs, resourcereqs, body);
            this.env.currentNamespace.apis.push(api);
        }
    }

    private parseAgent(attributes: DeclarationAttibute[]) {
        const sinfo = this.peekToken().getSourceInfo();

        this.ensureAndConsumeTokenAlways(KW_agent, "agent declaration");
        this.ensureToken(TokenStrings.IdentifierName, "agent declaration");
        const agentname = this.parseIdentifierAsStdVariable();

        if(isParsePhase_Enabled(this.currentPhase, ParsePhase_RegisterNames)) {
            if(this.env.currentNamespace.checkDeclNameClashMemberSimple(agentname)) {
                this.recordErrorGeneral(sinfo, `Collision between Agent and other names -- ${agentname}`);
            }

            this.env.currentNamespace.declaredNames.add(agentname);
            this.env.currentNamespace.declaredAgentNames.add(agentname);

            this.scanOverSemiDelimitedDeclaration();
        }
        else {
            const okdecl = this.testToken(SYM_lparen);
            if(!okdecl) {
                this.recordErrorGeneral(sinfo, "Agent declaration missing parameter list");
                return;
            }

            const boundtemplates = new Set<string>();
            const params: InvokeParameterDecl[] = this.parseInvokeDeclParameters(sinfo, false, boundtemplates);
        
            this.ensureAndConsumeTokenIf(SYM_colon, "agent declaration");
            const resultInfo = this.parseReturnTypeSignature(true);

            let eventType: TypeSignature | undefined = undefined;
            if(this.testAndConsumeTokenIf(SYM_coma)) {
                eventType = this.parseNominalType();
            }

            const argNames = new Set<string>(params.map((param) => param.name));
            const cargs = params.map((param) => new VariableDefinitionInfo("let", param.name));

            const [preconds, postconds] = this.parsePreAndPostConditions(sinfo, argNames, new Set<string>(), new Set<string>(), true, true);
    
            let configs: TaskConfiguration = new TaskConfiguration(undefined, undefined, undefined);
            let statusinfo: TypeSignature[] = [];
            let resourcereqs: ResourceInformation = new ResourceInformation([]);
            let envreqs: EnvironmentVariableInformation[] = [];
            while(this.testToken(KW_status) || this.testToken(KW_resource) || this.testToken(KW_env) || this.testToken(KW_configs)) {
                if(this.testToken(KW_configs)) {
                    if(configs.priority !== undefined || configs.retry !== undefined || configs.timeout !== undefined) {
                        this.recordErrorGeneral(sinfo, "Cannot have multiple config sections");
                    }

                    this.consumeToken();
                    this.ensureAndConsumeTokenAlways(SYM_lbrace, "task configs section");

                    this.parseTaskConfigs(configs);

                    this.ensureAndConsumeTokenAlways(SYM_rbrace, "task configs section");
                }
                else if(this.testToken(KW_status)) {
                    if(statusinfo.length !== 0) {
                        this.recordErrorGeneral(sinfo, "Cannot have multiple status sections");
                    }

                    this.parseStatusInfo(statusinfo);
                }
                else if(this.testToken(KW_resource)) {
                    if(resourcereqs.pathglobs.length !== 0) {
                        this.recordErrorGeneral(sinfo, "Cannot have multiple resource sections");
                    }

                    this.parseResourceInfo(resourcereqs);
                }
                else {
                    if(envreqs.length !== 0) {
                        this.recordErrorGeneral(sinfo, "Cannot have multiple env sections");
                    }

                    this.parseEnvInfo(envreqs);
                }
            }

            this.env.pushStandardFunctionScope(cargs, boundtemplates, resultInfo);
            const body = this.parseBody(attributes, false, false);
            this.env.popStandardFunctionScope();
            
            const agent = new AgentDecl(this.env.currentFile, sinfo, attributes, agentname, params, resultInfo, eventType, preconds, postconds, configs, statusinfo, envreqs, resourcereqs, body);
            this.env.currentNamespace.agents.push(agent);
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

    private static eatDeadTextAtFileStart(contents: string): [string, number] {
        let cccontents = contents;

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
                const nlcount = [...cccontents.slice(0, cccontents.length - contents.length).matchAll(/\n/g)].length;
                return [contents, nlcount];
            }
        }
    }

    private static _s_nsre = /^(declare[ ]+)?namespace[ ]+[A-Z][_a-zA-Z0-9]*/;
    private static parseCompilationUnit(iscore: boolean, phase: ParsePhase, file: string, contents: string, macrodefs: string[], assembly: Assembly): {ns: string, isdecl: boolean, errors: ParserError[]} {
        const [tcontents, lstart] = Parser.eatDeadTextAtFileStart(contents);
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

        const ll = new Lexer(iscore, file, tcontents, lstart, macrodefs);
        const toks = ll.lex();
        
        const pp = new Parser(file, ns, toks, assembly, phase);

        pp.testAndConsumeTokenIf(KW_declare);
        pp.ensureAndConsumeTokenAlways(KW_namespace, "namespace declaration");
        pp.ensureAndConsumeTokenAlways(TokenStrings.IdentifierName, "namespace declaration");

        if(pp.testToken(SYM_lbrace)) {
            pp.parseListOf<boolean>("namespace", SYM_lbrace, SYM_rbrace, SYM_semicolon, () => {
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

        pp.parseNamespaceMembers();

        return {ns: ns, isdecl: isdeclared, errors: [...ll.errors, ...pp.currentState().errors]};
    }

    ////
    //Public methods

    static parsefiles(iscore: boolean, code: CodeFileInfo[], macrodefs: string[], assembly: Assembly, registeredNamespaces: Set<string>): ParserError[] {
        let errors: ParserError[] = [];
        let pass1errors: Set<string> = new Set<string>();

        //load all the names and make sure every top-level namespace is declared
        for(let i = 0; i < code.length; ++i) {
            const cunit = Parser.parseCompilationUnit(iscore, ParsePhase_RegisterNames, code[i].srcpath, code[i].contents, macrodefs, assembly);
            if(cunit.errors.length !== 0) {
                pass1errors.add(code[i].srcpath);
            }

            if(cunit.isdecl) {
                if(registeredNamespaces.has(cunit.ns)) {
                    errors.push(new ParserError(code[i].srcpath, SourceInfo.implicitSourceInfo(), `Duplicate namespace declaration -- ${cunit.ns}`));
                }
                registeredNamespaces.add(cunit.ns);
            }

            errors.push(...cunit.errors);
        }

        //parse the code
        for(let i = 0; i < code.length; ++i) {
            if(!pass1errors.has(code[i].srcpath)) {
                const cunit = Parser.parseCompilationUnit(iscore, ParsePhase_CompleteParsing, code[i].srcpath, code[i].contents, macrodefs, assembly);
                errors.push(...cunit.errors);
            }
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
