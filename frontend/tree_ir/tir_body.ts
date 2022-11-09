import { SourceInfo } from "../ast/parser";
import { BSQRegex } from "../bsqregex";
import { ResolvedFunctionType, ResolvedType, ResolvedValidatorEntityAtomType } from "./tir_type";

enum TIRExpressionTag {
    Clear = "[CLEAR]",
    InvalidExpresion = "[INVALID]",

    LiteralNoneExpression = "LiteralNoneExpression",
    LiteralNothingExpression = "LiteralNothingExpression",
    LiteralBoolExpression = "LiteralBoolExpression",
    LiteralIntegralExpression = "LiteralIntegralExpression",
    LiteralRationalExpression = "LiteralRationalExpression",
    LiteralFloatPointExpression = "LiteralFloatExpression",
    LiteralRegexExpression = "LiteralRegexExpression",

    LiteralStringExpression = "LiteralStringExpression",
    LiteralASCIIStringExpression = "LiteralASCIIStringExpression",
    
    LiteralTypedStringExpression = "LiteralTypedStringExpression",
    LiteralASCIITypedStringExpression = "LiteralASCIITypedStringExpression",
    
    LiteralTemplateStringExpression = "LiteralTemplateStringExpression",
    LiteralASCIITemplateStringExpression = "LiteralASCIITemplateStringExpression",
    
    LiteralTypedPrimitiveConstructorExpression = "LiteralTypedPrimitiveConstructorExpression",

    AccessFormatInfo = "AccessFormatInfo",
    AccessEnvValue = "AccessEnvValue",
    HasEnvValue = "HasEnvValue",

    AccessNamespaceConstantExpression = "AccessNamespaceConstantExpression",
    AccessStaticFieldExpression = " AccessStaticFieldExpression",
    AccessVariableExpression = "AccessVariableExpression",

    ConstructorPrimaryExpression = "ConstructorPrimaryExpression",
    ConstructorTupleExpression = "ConstructorTupleExpression",
    ConstructorRecordExpression = "ConstructorRecordExpression",
    ConstructorEphemeralValueList = "ConstructorEphemeralValueList",

    PCodeInvokeExpression = "PCodeInvokeExpression",
    SpecialConstructorExpression = "SpecialConstructorExpression",
    CallNamespaceFunctionExpression = "CallNamespaceFunctionExpression",
    CallNamespaceOperatorExpression = "CallNamespaceOperatorExpression",
    CallStaticFunctionExpression = "CallStaticFunctionExpression",

    LogicActionAndExpression = "LogicActionAndExpression",
    LogicActionOrExpression = "LogicActionOrExpression",

    PostfixOpExpression = "PostfixOpExpression",

    PrefixNotOpExpression = "PrefixNotOpExpression",
    PrefixNegateOpExpression = "PrefixNegateOpExpression",

    BinAddExpression = "BinAddExpression",
    BinSubExpression = "BinSubExpression",
    BinMultExpression = "BinMultExpression",
    BinDivExpression = "BinDivExpression",

    BinKeyEqExpression = "BinKeyEqExpression",
    BinKeyNeqExpression = "BinKeyNeqExpression",

    NumericEqExpression = "NumericEqExpression",
    NumericNeqExpression = "NumericNeqExpression",
    NumericLessExpression = "NumericLessExpression",
    NumericLessEqExpression = "NumericLessEqExpression",
    NumericGreaterExpression = "NumericGreaterExpression",
    NumericGreaterEqExpression = "NumericGreaterEqExpression",

    BinLogicAndExpression = "BinLogicAndExpression",
    BinLogicOrExpression = "BinLogicOrExpression",
    BinLogicImpliesExpression = "BinLogicImpliesExpression",

    MapEntryConstructorExpression = "MapEntryConstructorExpression",

    IfExpression = "IfExpression",
    SwitchExpression = "SwitchExpression",
    MatchExpression = "MatchExpression",

    TaskSelfFieldExpression = "TaskSelfFieldExpression",
    TaskSelfActionExpression = "TaskSelfActionExpression",
    TaskGetIDExpression = "TaskGetIDExpression",
    TaskIsCancelRequestedExpression = "TaskIsCancelRequestedExpression",

    AbortExpression = "AbortExpression",
    CoerceTypeWidenExpression = "CoerceTypeWidenExpression",
    CoerceTypeNarrowExpression = "CoerceTypeNarrowExpression",
    InjectExpression = "InjectExpression",
    ExtractExpression = "ExtractExpression",
    CreateCodePackExpression = "CreateCodePackExpression"
}

class TIRCodePack {
    readonly code: TIRInvokeDecl;
    readonly ftype: ResolvedFunctionType;

    readonly capturedValues: {cname: string, ctype: ResolvedType}[];
    readonly capturedCodePacks: {cpname: string, cpval: TIRCodePack}[];

    constructor(code: TIRInvokeDecl, ftype: ResolvedFunctionType, capturedValues: {cname: string, ctype: ResolvedType}[], capturedCodePacks: {cpname: string, cpval: TIRCodePack}[]) {
        this.code = code;
        this.ftype = ftype;
        this.capturedValues = capturedValues;
        this.capturedCodePacks = capturedCodePacks;
    }
}

abstract class TIRExpression {
    readonly tag: TIRExpressionTag;
    readonly sinfo: SourceInfo;

    readonly tlayout: ResolvedType;
    readonly tinfer: ResolvedType;
    readonly expstr: string;

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, tlayout: ResolvedType, tinfer: ResolvedType, expstr: string) {
        this.tag = tag;
        this.sinfo = sinfo;

        this.tlayout = tlayout;
        this.tinfer = tinfer;
        this.expstr = expstr;
    }

    isTaskOperation(): boolean {
        return false;
    }

    getUsedVars(): string[] {
        return [];
    }

    static joinUsedVarInfo(...vars: string[][]): string[] {
        const vflat = ([] as string[]).concat(...vars);
        return [...new Set<string>(vflat)];
    }
}

class TIRInvalidExpression extends TIRExpression {
    constructor(sinfo: SourceInfo, etype: ResolvedType) {
        super(TIRExpressionTag.InvalidExpresion, sinfo, etype, etype, "[INVALID]");
    }
}

class TIRLiteralNoneExpression extends TIRExpression {
    constructor(sinfo: SourceInfo, etype: ResolvedType) {
        super(TIRExpressionTag.LiteralNoneExpression, sinfo, etype, etype, "none");
    }
}

class TIRLiteralNothingExpression extends TIRExpression {
    constructor(sinfo: SourceInfo, etype: ResolvedType) {
        super(TIRExpressionTag.LiteralNothingExpression, sinfo, etype, etype, "nothing");
    }
}

class TIRLiteralBoolExpression extends TIRExpression {
    readonly value: boolean;

    constructor(sinfo: SourceInfo, etype: ResolvedType, value: boolean) {
        super(TIRExpressionTag.LiteralBoolExpression, sinfo, etype, etype, value ? "true" : "false");
        this.value = value;
    }
}

class TIRLiteralIntegralExpression extends TIRExpression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string, itype: ResolvedType) {
        super(TIRExpressionTag.LiteralIntegralExpression, sinfo, itype, itype, value);
        this.value = value;
    }
}

class TIRLiteralRationalExpression extends TIRExpression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string, rtype: ResolvedType) {
        super(TIRExpressionTag.LiteralRationalExpression, sinfo, rtype, rtype, value);
        this.value = value;
    }
}

class TIRLiteralFloatPointExpression extends TIRExpression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string, fptype: ResolvedType) {
        super(TIRExpressionTag.LiteralFloatPointExpression, sinfo, fptype, fptype, value);
        this.value = value;
    }
}

class TIRLiteralStringExpression extends TIRExpression {
    constructor(sinfo: SourceInfo, value: string, etype: ResolvedType) {
        super(TIRExpressionTag.LiteralStringExpression, sinfo, etype, etype, value);
    }
}

class TIRLiteralRegexExpression extends TIRExpression {
    readonly value: BSQRegex;

    constructor(sinfo: SourceInfo, value: BSQRegex, etype: ResolvedType) {
        super(TIRExpressionTag.LiteralRegexExpression, sinfo, etype, etype, value.restr);
        this.value = value;
    }
}

class TIRLiteralASCIIStringExpression extends TIRExpression {
    constructor(sinfo: SourceInfo, value: string, etype: ResolvedType) {
        super(TIRExpressionTag.LiteralASCIIStringExpression, sinfo, etype, etype, value);
    }
}

class TIRLiteralTypedStringExpression extends TIRExpression {
    readonly oftype: ResolvedValidatorEntityAtomType;

    constructor(sinfo: SourceInfo, value: string, stype: ResolvedType, oftype: ResolvedValidatorEntityAtomType) {
        super(TIRExpressionTag.LiteralTypedStringExpression, sinfo, stype, stype, `${value}_${oftype.typeID}`);
        this.oftype = oftype;
    }
}

class TIRLiteralASCIITypedStringExpression extends TIRExpression {
    readonly oftype: ResolvedValidatorEntityAtomType;

    constructor(sinfo: SourceInfo, value: string, stype: ResolvedType, oftype: ResolvedValidatorEntityAtomType) {
        super(TIRExpressionTag.LiteralASCIITypedStringExpression, sinfo, stype, stype, `${value}_${oftype.typeID}`);
        this.oftype = oftype;
    }
}

class TIRLiteralTemplateStringExpression extends TIRExpression {
    constructor(sinfo: SourceInfo, value: string, etype: ResolvedType) {
        super(TIRExpressionTag.LiteralTemplateStringExpression, sinfo, etype, etype, value);
    }
}

class TIRLiteralASCIITemplateStringExpression extends TIRExpression {
    constructor(sinfo: SourceInfo, value: string, etype: ResolvedType) {
        super(TIRExpressionTag.LiteralASCIITemplateStringExpression, sinfo, etype, etype, value);
    }
}

class TIRLiteralTypedPrimitiveConstructorExpression extends TIRExpression {
    readonly value: TIRExpression;
    readonly vtype: ResolvedType;

    readonly constype: ResolvedType;
    readonly reprtype: ResolvedType;

    readonly isSafeConstructor: boolean;

    constructor(sinfo: SourceInfo, value: TIRExpression, vtype: ResolvedType, constype: ResolvedType, reprtype: ResolvedType, isSafeConstructor: boolean) {
        super(TIRExpressionTag.LiteralTypedPrimitiveConstructorExpression, sinfo, constype, constype, `${value.expstr}_${constype.typeID}`);
        this.value = value;
        this.vtype = vtype;

        this.constype = constype;
        this.reprtype = reprtype;

        this.isSafeConstructor = isSafeConstructor;
    }
}

xxxx;

class TIRLiteralValue {
    readonly exp: TIRExpression;
    readonly ltype: ResolvedType;
    readonly lidstr: string;
    
    constructor(exp: TIRExpression, ltype: ResolvedType, lidstr: string) {
        this.exp = exp
        this.ltype = ltype;
        this.lidstr = lidstr;
    }
}

export {
    TIRCodePack,
    TIRExpression, TIRInvalidExpression,
    TIRLiteralNoneExpression, TIRLiteralNothingExpression, TIRLiteralBoolExpression, TIRLiteralIntegralExpression, TIRLiteralRationalExpression, TIRLiteralFloatPointExpression, 
    TIRLiteralStringExpression, TIRLiteralASCIIStringExpression, TIRLiteralRegexExpression, TIRLiteralTypedStringExpression, TIRLiteralASCIITypedStringExpression, TIRLiteralTemplateStringExpression, TIRLiteralASCIITemplateStringExpression,
    TIRLiteralTypedPrimitiveConstructorExpression,
    xxxx,
    TIRLiteralValue
};
