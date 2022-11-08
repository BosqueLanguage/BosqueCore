import { SourceInfo } from "../ast/parser";
import { BSQRegex } from "../bsqregex";
import { ResolvedType, ResolvedValidatorEntityAtomType } from "./tir_type";

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

    CoerceTypeWidenExpression = "CoerceTypeWidenExpression",
    CoerceTypeNarrowExpression = "CoerceTypeNarrowExpression",
    InjectExpression = "InjectExpression",
    ExtractExpression = "ExtractExpression",
}

abstract class TIRExpression {
    readonly tag: TIRExpressionTag;
    readonly sinfo: SourceInfo;

    readonly etype: ResolvedType;
    readonly expstr: string;

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, etype: ResolvedType, expstr: string) {
        this.tag = tag;
        this.sinfo = sinfo;

        this.etype = etype;
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
        super(TIRExpressionTag.InvalidExpresion, sinfo, etype, "[INVALID]");
    }
}

class TIRLiteralNoneExpression extends TIRExpression {
    constructor(sinfo: SourceInfo, etype: ResolvedType) {
        super(TIRExpressionTag.LiteralNoneExpression, sinfo, etype, "none");
    }
}

class TIRLiteralNothingExpression extends TIRExpression {
    constructor(sinfo: SourceInfo, etype: ResolvedType) {
        super(TIRExpressionTag.LiteralNothingExpression, sinfo, etype, "nothing");
    }
}

class TIRLiteralBoolExpression extends TIRExpression {
    readonly value: boolean;

    constructor(sinfo: SourceInfo, etype: ResolvedType, value: boolean) {
        super(TIRExpressionTag.LiteralBoolExpression, sinfo, etype, value ? "true" : "false");
        this.value = value;
    }
}

class TIRLiteralIntegralExpression extends TIRExpression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string, itype: ResolvedType) {
        super(TIRExpressionTag.LiteralIntegralExpression, sinfo, itype, value);
        this.value = value;
    }
}

class TIRLiteralRationalExpression extends TIRExpression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string, rtype: ResolvedType) {
        super(TIRExpressionTag.LiteralRationalExpression, sinfo, rtype, value);
        this.value = value;
    }
}

class TIRLiteralFloatPointExpression extends TIRExpression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string, fptype: ResolvedType) {
        super(TIRExpressionTag.LiteralFloatPointExpression, sinfo, fptype, value);
        this.value = value;
    }
}

class TIRLiteralStringExpression extends TIRExpression {
    constructor(sinfo: SourceInfo, value: string, etype: ResolvedType) {
        super(TIRExpressionTag.LiteralStringExpression, sinfo, etype, value);
    }
}

class TIRLiteralRegexExpression extends TIRExpression {
    readonly value: BSQRegex;

    constructor(sinfo: SourceInfo, value: BSQRegex, etype: ResolvedType) {
        super(TIRExpressionTag.LiteralRegexExpression, sinfo, etype, value.restr);
        this.value = value;
    }
}

class TIRLiteralASCIIStringExpression extends TIRExpression {
    constructor(sinfo: SourceInfo, value: string, etype: ResolvedType) {
        super(TIRExpressionTag.LiteralASCIIStringExpression, sinfo, etype, value);
    }
}

class TIRLiteralTypedStringExpression extends TIRExpression {
    readonly oftype: ResolvedValidatorEntityAtomType;

    constructor(sinfo: SourceInfo, value: string, stype: ResolvedType, oftype: ResolvedValidatorEntityAtomType) {
        super(TIRExpressionTag.LiteralTypedStringExpression, sinfo, stype, `${value}_${oftype.typeID}`);
        this.oftype = oftype;
    }
}

class TIRLiteralASCIITypedStringExpression extends TIRExpression {
    readonly oftype: ResolvedValidatorEntityAtomType;

    constructor(sinfo: SourceInfo, value: string, stype: ResolvedType, oftype: ResolvedValidatorEntityAtomType) {
        super(TIRExpressionTag.LiteralASCIITypedStringExpression, sinfo, stype, `${value}_${oftype.typeID}`);
        this.oftype = oftype;
    }
}

class TIRLiteralTemplateStringExpression extends TIRExpression {
    constructor(sinfo: SourceInfo, value: string, etype: ResolvedType) {
        super(TIRExpressionTag.LiteralTemplateStringExpression, sinfo, etype, value);
    }
}

class TIRLiteralASCIITemplateStringExpression extends TIRExpression {
    constructor(sinfo: SourceInfo, value: string, etype: ResolvedType) {
        super(TIRExpressionTag.LiteralASCIITemplateStringExpression, sinfo, etype, value);
    }
}

class TIRLiteralTypedPrimitiveConstructorExpression extends TIRExpression {
    readonly value: TIRExpression;
    readonly vtype: ResolvedType;

    readonly constype: ResolvedType;
    readonly reprtype: ResolvedType;

    constructor(sinfo: SourceInfo, value: TIRExpression, vtype: ResolvedType, constype: ResolvedType, reprtype: ResolvedType) {
        super(TIRExpressionTag.LiteralTypedPrimitiveConstructorExpression, sinfo, constype, `${value.expstr}_${constype.typeID}`);
        this.value = value;
        this.vtype = vtype;

        this.constype = constype;
        this.reprtype = reprtype;
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
    TIRExpression, TIRInvalidExpression,
    TIRLiteralNoneExpression, TIRLiteralNothingExpression, TIRLiteralBoolExpression, TIRLiteralIntegralExpression, TIRLiteralRationalExpression, TIRLiteralFloatPointExpression, 
    TIRLiteralStringExpression, TIRLiteralASCIIStringExpression, TIRLiteralRegexExpression, TIRLiteralTypedStringExpression, TIRLiteralASCIITypedStringExpression, TIRLiteralTemplateStringExpression, TIRLiteralASCIITemplateStringExpression,
    TIRLiteralTypedPrimitiveConstructorExpression,
    xxxx,
    TIRLiteralValue
};
