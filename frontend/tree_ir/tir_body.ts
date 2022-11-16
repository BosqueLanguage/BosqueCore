import { SourceInfo } from "../ast/parser";
import { BSQRegex } from "../bsqregex";
import { PathValidator } from "../path_validator";
import { TIRTypeKey } from "./tir_assembly";
import { ResolvedFunctionType, ResolvedType, ResolvedValidatorEntityAtomType, TIRInvokeID, TIRPropertyID, TIRTupleIndex } from "./tir_type";

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
    
    LiteralTypedPrimitiveDirectExpression = "LiteralTypedPrimitiveDirectExpression",
    LiteralTypedPrimitiveConstructorExpression = "LiteralTypedPrimitiveConstructorExpression",

    AccessFormatInfo = "AccessFormatInfo",
    AccessEnvValue = "AccessEnvValue",

    AccessNamespaceConstantExpression = "AccessNamespaceConstantExpression",
    AccessStaticFieldExpression = " AccessStaticFieldExpression",
    AccessVariableExpression = "AccessVariableExpression",

    LoadIndexExpression = "LoadIndexExpression",
    LoadPropertyExpression = "LoadPropertyExpression",
    LoadFieldExpression = "LoadFieldExpression",

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

    PrefixNotOpExpression = "PrefixNotOpExpression",
    PrefixNegateOpExpression = "PrefixNegateOpExpression",

    BinAddExpression = "BinAddExpression",
    BinSubExpression = "BinSubExpression",
    BinMultExpression = "BinMultExpression",
    BinDivExpression = "BinDivExpression",

    BinKeyEqExpression = "BinKeyEqExpression",
    BinKeyNeqExpression = "BinKeyNeqExpression",
    BinKeyLessExpression = "BinKeyLessExpression",

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
    CoerceSafeTypeNarrowExpression = "CoerceSafeTypeNarrowExpression",
    InjectExpression = "InjectExpression",
    ExtractExpression = "ExtractExpression",
    CreateCodePackExpression = "CreateCodePackExpression",

    IsNoneExpression = "IsNoneExpression",
    IsNotNoneExpresson = "IsNotNoneExpression",
    IsNothingExpression = "IsNothingExpression",
    IsNotNothingExpression = "IsNotNothingExpression",
    IsTypeExpression = "IsTypeExpression",
    IsSubTypeExpression = "IsSubTypeExpression",

    CallMemberFunctionExpression = "CallMemberFunctionExpression",
    CallMemberFunctionDynamicExpression = "CallMemberFunctionDynamicExpression",
    CallMemberFunctionSelfRefExpression = "CallMemberFunctionSelfRefExpression",
    CallMemberFunctionDynamicSelfRefExpression = "CallMemberFunctionDynamicSelfRefExpression"
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
    readonly tflow: ResolvedType;
    readonly expstr: string;

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, tlayout: ResolvedType, tflow: ResolvedType, expstr: string) {
        this.tag = tag;
        this.sinfo = sinfo;

        this.tlayout = tlayout;
        this.tflow = tflow;
        this.expstr = expstr;
    }

    isTaskOperation(): boolean {
        return false;
    }

    isSafeOperation(): boolean {
        return true;
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

class TIRLiteralTypedPrimitiveDirectExpression extends TIRExpression {
    readonly value: TIRExpression;

    readonly constype: ResolvedType;
    readonly reprtype: ResolvedType;
    readonly basetype: ResolvedType;

    constructor(sinfo: SourceInfo, value: TIRExpression, constype: ResolvedType, reprtype: ResolvedType, basetype: ResolvedType) {
        super(TIRExpressionTag.LiteralTypedPrimitiveDirectExpression, sinfo, constype, constype, `${value.expstr}_${constype.typeID}`);
        this.value = value;

        this.constype = constype;
        this.reprtype = reprtype;
        this.basetype = basetype;
    }
}

class TIRLiteralTypedPrimitiveConstructorExpression extends TIRExpression {
    readonly value: TIRExpression;

    readonly constype: ResolvedType;
    readonly reprtype: ResolvedType;
    readonly basetype: ResolvedType;

    readonly chkinvs: TIRInvokeID[];

    constructor(sinfo: SourceInfo, value: TIRExpression, constype: ResolvedType, reprtype: ResolvedType, basetype: ResolvedType, chkinvs: TIRInvokeID[]) {
        super(TIRExpressionTag.LiteralTypedPrimitiveConstructorExpression, sinfo, constype, constype, `${value.expstr}_${constype.typeID}`);
        this.value = value;

        this.constype = constype;
        this.reprtype = reprtype;
        this.basetype = basetype;

        this.chkinvs = chkinvs;
    }

    isSafeOperation(): boolean {
        return false;
    }

    //
    //TODO: compiler may want to treat this like a constant and precompute with a reference for any uses
    //
}

class TIRAccessEnvValue extends TIRExpression {
    readonly keyname: string;
    readonly orNoneMode: boolean;

    constructor(sinfo: SourceInfo, keyname: string, valtype: ResolvedType, orNoneMode: boolean) {
        super(TIRExpressionTag.AccessEnvValue, sinfo, valtype, valtype, `environment${orNoneMode ? "?" : ""}["${keyname}"]`);
        this.keyname = keyname;
        this.orNoneMode = orNoneMode;
    }
}


class TIRAccessNamespaceConstantExpression extends TIRExpression {
    readonly ns: string;
    readonly name: string;

    constructor(sinfo: SourceInfo, ns: string, name: string, decltype: ResolvedType) {
        super(TIRExpressionTag.AccessNamespaceConstantExpression, sinfo, decltype, decltype, `${ns}::${name}`);
        this.ns = ns;
        this.name = name;
    }
}

class TIRAccessStaticFieldExpression extends TIRExpression {
    readonly stype: ResolvedType;
    readonly name: string;

    constructor(sinfo: SourceInfo, stype: ResolvedType, name: string, decltype: ResolvedType) {
        super(TIRExpressionTag.AccessStaticFieldExpression, sinfo, decltype, decltype, `${stype.typeID}::${name}`);
        this.stype = stype;
        this.name = name;
    }
}

class TIRAccessVariableExpression extends TIRExpression {
    readonly name: string;

    constructor(sinfo: SourceInfo, name: string, tlayout: ResolvedType, tinfer: ResolvedType) {
        super(TIRExpressionTag.AccessVariableExpression, sinfo, tlayout, tinfer, name);
        this.name = name;
    }
}

class TIRLoadIndexExpression extends TIRExpression {
    readonly exp: TIRExpression;
    readonly index: TIRTupleIndex;

    constructor(sinfo: SourceInfo, exp: TIRExpression, index: TIRTupleIndex, resultType: ResolvedType) {
        super(TIRExpressionTag.LoadIndexExpression, sinfo, resultType, resultType, `${exp.expstr}.${index}`);
        this.exp = exp;
        this.index = index;
    }
} 

class TIRLoadPropertyExpression extends TIRExpression {
    readonly exp: TIRExpression;
    readonly property: TIRPropertyID;

    constructor(sinfo: SourceInfo, exp: TIRExpression, property: TIRPropertyID, resultType: ResolvedType) {
        super(TIRExpressionTag.LoadIndexExpression, sinfo, resultType, resultType, `${exp.expstr}.${property}`);
        this.exp = exp;
        this.property = property;
    }
}

class TIRLoadFieldExpression extends TIRExpression {

}

/*
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
*/


class TIRPrefixNotOp extends TIRExpression {
    readonly exp: TIRExpression;

    constructor(sinfo: SourceInfo, exp: TIRExpression, booltype: ResolvedType) {
        super(TIRExpressionTag.PrefixNotOpExpression, sinfo, booltype, booltype, `!(${exp.expstr})`);
        this.exp = exp;
    }
}

class TIRPrefixNegateOp extends TIRExpression {
    readonly optype: ResolvedType;
    readonly exp: TIRExpression;

    constructor(sinfo: SourceInfo, exp: TIRExpression, ntype: ResolvedType) {
        super(TIRExpressionTag.PrefixNegateOpExpression, sinfo, ntype, ntype, `-(${exp.expstr})`);
        this.optype = ntype;
        this.exp = exp;
    }

    isSafeOperation(): boolean {
        return this.optype.typeID !== "Nat" && this.optype.typeID !== "BigNat";
    }
}

class TIRBinAddExpression extends TIRExpression {
    readonly optype: ResolvedType;
    readonly lhs: TIRExpression;
    readonly rhs: TIRExpression;

    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, ntype: ResolvedType) {
        super(TIRExpressionTag.BinAddExpression, sinfo, ntype, ntype, `(${lhs.expstr} + ${rhs.expstr})`);
        this.optype = ntype;
        this.lhs = lhs;
        this.rhs = rhs;
    }

    isSafeOperation(): boolean {
        return false;
    }
}

class TIRBinSubExpression extends TIRExpression {
    readonly optype: ResolvedType;
    readonly lhs: TIRExpression;
    readonly rhs: TIRExpression;

    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, ntype: ResolvedType) {
        super(TIRExpressionTag.BinSubExpression, sinfo, ntype, ntype, `(${lhs.expstr} - ${rhs.expstr})`);
        this.optype = ntype;
        this.lhs = lhs;
        this.rhs = rhs;
    }

    isSafeOperation(): boolean {
        return false;
    }
}

class TIRBinMultExpression extends TIRExpression {
    readonly optype: ResolvedType;
    readonly lhs: TIRExpression;
    readonly rhs: TIRExpression;

    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, ntype: ResolvedType) {
        super(TIRExpressionTag.BinMultExpression, sinfo, ntype, ntype, `(${lhs.expstr} * ${rhs.expstr})`);
        this.optype = ntype;
        this.lhs = lhs;
        this.rhs = rhs;
    }

    isSafeOperation(): boolean {
        return false;
    }
}

class TIRBinDivExpression extends TIRExpression {
    readonly optype: ResolvedType;
    readonly lhs: TIRExpression;
    readonly rhs: TIRExpression;

    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, ntype: ResolvedType) {
        super(TIRExpressionTag.BinDivExpression, sinfo, ntype, ntype, `(${lhs.expstr} / ${rhs.expstr})`);
        this.optype = ntype;
        this.lhs = lhs;
        this.rhs = rhs;
    }

    isSafeOperation(): boolean {
        return false;
    }
}

class TIRBinKeyEqExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinKeyEqExpression, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

class TIRBinKeyNeqExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinKeyNeqExpression, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

class TIRNumericEqExpression extends TIRExpression {
    readonly lhs: TIRExpression;
    readonly rhs: TIRExpression;

    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(TIRExpressionTag.NumericEqExpression, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

class TIRNumericNeqExpression extends TIRExpression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(TIRExpressionTag.NumericNeqExpression, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

class NumericLessExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.NumericLessExpression, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

class NumericLessEqExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.NumericLessEqExpression, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

class NumericGreaterExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.NumericGreaterExpression, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

class NumericGreaterEqExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.NumericGreaterEqExpression, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

class BinLogicAndxpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinLogicAndExpression, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

class BinLogicOrExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinLogicOrExpression, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

class BinLogicImpliesExpression extends Expression {
    readonly lhs: Expression;
    readonly rhs: Expression;

    constructor(sinfo: SourceInfo, lhs: Expression, rhs: Expression) {
        super(ExpressionTag.BinLogicImpliesExpression, sinfo);
        this.lhs = lhs;
        this.rhs = rhs;
    }
}

/*
    MapEntryConstructorExpression = "MapEntryConstructorExpression",

    IfExpression = "IfExpression",
    SwitchExpression = "SwitchExpression",
    MatchExpression = "MatchExpression",

    TaskSelfFieldExpression = "TaskSelfFieldExpression",
    TaskSelfActionExpression = "TaskSelfActionExpression",
    TaskGetIDExpression = "TaskGetIDExpression",
    TaskIsCancelRequestedExpression = "TaskIsCancelRequestedExpression",
*/

    AbortExpression = "AbortExpression",
    CoerceTypeWidenExpression = "CoerceTypeWidenExpression",
    CoerceTypeNarrowExpression = "CoerceTypeNarrowExpression",
    InjectExpression = "InjectExpression",
    ExtractExpression = "ExtractExpression",

/*
    CreateCodePackExpression = "CreateCodePackExpression"
*/

class TIRLiteralValue {
    readonly exp: TIRExpression;
    readonly ltype: TIRTypeKey;
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
    TIRLiteralTypedPrimitiveDirectExpression, TIRLiteralTypedPrimitiveConstructorExpression,
    TIRAccessEnvValue, TIRAccessNamespaceConstantExpression, TIRAccessStaticFieldExpression, TIRAccessVariableExpression,
    qqqq,
    TIRPrefixNotOp, TIRPrefixNegateOp,
    TIRBinAddExpression, TIRBinSubExpression, TIRBinMultExpression, TIRBinDivExpression,
    TIRLiteralValue
};
