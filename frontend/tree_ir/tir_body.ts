
import { TIRCodePackType, TIRInvokeDecl, TIRInvokeKey, TIRMemberConstKey, TIRNamespaceConstKey, TIRNamespaceMemberName, TIRTypeKey, TIRTypeMemberName, TIRTypeName } from "./tir_assembly";

import { SourceInfo } from "../build_decls";
import { BSQRegex } from "../bsqregex";
import { PathValidator } from "../path_validator";

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
    TIRAccessConstMemberFieldExpression = " TIRAccessConstMemberFieldExpression",
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
    readonly ftype: TIRCodePackType;

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

    readonly etype: TIRTypeKey;
    readonly expstr: string;

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, etype: TIRTypeKey, expstr: string) {
        this.tag = tag;
        this.sinfo = sinfo;

        this.etype = etype;
        this.expstr = expstr;
    }

    isTaskOperation(): boolean {
        return false;
    }

    isFailableOperation(): boolean {
        return false;
    }

    isOverflowableOperation(): boolean {
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
    constructor(sinfo: SourceInfo, etype: TIRTypeKey) {
        super(TIRExpressionTag.InvalidExpresion, sinfo, etype, "[INVALID]");
    }
}

class TIRLiteralNoneExpression extends TIRExpression {
    constructor(sinfo: SourceInfo) {
        super(TIRExpressionTag.LiteralNoneExpression, sinfo, "None", "none");
    }
}

class TIRLiteralNothingExpression extends TIRExpression {
    constructor(sinfo: SourceInfo) {
        super(TIRExpressionTag.LiteralNothingExpression, sinfo, "Nothing", "nothing");
    }
}

class TIRLiteralBoolExpression extends TIRExpression {
    readonly value: boolean;

    constructor(sinfo: SourceInfo, value: boolean) {
        super(TIRExpressionTag.LiteralBoolExpression, sinfo, "Bool", value ? "true" : "false");
        this.value = value;
    }
}

class TIRLiteralIntegralExpression extends TIRExpression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string, itype: TIRTypeKey) {
        super(TIRExpressionTag.LiteralIntegralExpression, sinfo, itype, value);
        this.value = value;
    }
}

class TIRLiteralRationalExpression extends TIRExpression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string) {
        super(TIRExpressionTag.LiteralRationalExpression, sinfo, "Rational", value);
        this.value = value;
    }
}

class TIRLiteralFloatPointExpression extends TIRExpression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string, fptype: TIRTypeKey) {
        super(TIRExpressionTag.LiteralFloatPointExpression, sinfo, fptype, value);
        this.value = value;
    }
}

class TIRLiteralStringExpression extends TIRExpression {
    constructor(sinfo: SourceInfo, value: string) {
        super(TIRExpressionTag.LiteralStringExpression, sinfo, "String", value);
    }
}

class TIRLiteralRegexExpression extends TIRExpression {
    readonly value: BSQRegex;

    constructor(sinfo: SourceInfo, value: BSQRegex) {
        super(TIRExpressionTag.LiteralRegexExpression, sinfo, "Regex", value.restr);
        this.value = value;
    }
}

class TIRLiteralASCIIStringExpression extends TIRExpression {
    constructor(sinfo: SourceInfo, value: string) {
        super(TIRExpressionTag.LiteralASCIIStringExpression, sinfo, "ASCIIString", value);
    }
}

class TIRLiteralTypedStringExpression extends TIRExpression {
    readonly oftype: TIRTypeKey;

    constructor(sinfo: SourceInfo, value: string, stringoftype: TIRTypeKey, oftype: TIRTypeKey) {
        super(TIRExpressionTag.LiteralTypedStringExpression, sinfo, stringoftype, `${value}_${oftype}`);
        this.oftype = oftype;
    }
}

class TIRLiteralASCIITypedStringExpression extends TIRExpression {
    readonly oftype: TIRTypeKey;

    constructor(sinfo: SourceInfo, value: string, astringoftype: TIRTypeKey, oftype: TIRTypeKey) {
        super(TIRExpressionTag.LiteralASCIITypedStringExpression, sinfo, astringoftype, `${value}_${oftype}`);
        this.oftype = oftype;
    }
}

class TIRLiteralTemplateStringExpression extends TIRExpression {
    constructor(sinfo: SourceInfo, value: string, etype: TIRTypeKey) {
        super(TIRExpressionTag.LiteralTemplateStringExpression, sinfo, etype, value);
    }
}

class TIRLiteralASCIITemplateStringExpression extends TIRExpression {
    constructor(sinfo: SourceInfo, value: string, etype: TIRTypeKey) {
        super(TIRExpressionTag.LiteralASCIITemplateStringExpression, sinfo, etype, value);
    }
}

class TIRLiteralTypedPrimitiveDirectExpression extends TIRExpression {
    readonly value: TIRExpression;

    readonly constype: TIRTypeKey; //The type that is constructed
    readonly reprtype: TIRTypeKey; //The repr type that this is declared to be isomorphic to
    readonly basetype: TIRTypeKey; //The base representation of this (Bool, Int, String, ...) -- should be type of value expression

    constructor(sinfo: SourceInfo, value: TIRExpression, constype: TIRTypeKey, reprtype: TIRTypeKey, basetype: TIRTypeKey) {
        super(TIRExpressionTag.LiteralTypedPrimitiveDirectExpression, sinfo, constype, `${value.expstr}_${constype}`);
        this.value = value;

        this.constype = constype;
        this.reprtype = reprtype;
        this.basetype = basetype;
    }
}

class TIRLiteralTypedPrimitiveConstructorExpression extends TIRExpression {
    readonly value: TIRExpression;

    readonly constype: TIRTypeKey; //The type that is constructed
    readonly reprtype: TIRTypeKey; //The repr type that this is declared to be isomorphic to
    readonly basetype: TIRTypeKey; //The base representation of this (Bool, Int, String, ...) -- should be type of value expression

    constructor(sinfo: SourceInfo, value: TIRExpression, constype: TIRTypeKey, reprtype: TIRTypeKey, basetype: TIRTypeKey) {
        super(TIRExpressionTag.LiteralTypedPrimitiveConstructorExpression, sinfo, constype, `${value.expstr}_${constype}`);
        this.value = value;

        this.constype = constype;
        this.reprtype = reprtype;
        this.basetype = basetype;
    }

    isFailableOperation(): boolean {
        return true;
    }

    //
    //TODO: compiler may want to treat this like a constant and precompute with a reference for any uses
    //
}

class TIRAccessEnvValue extends TIRExpression {
    readonly keyname: string;
    readonly valtype: TIRTypeKey;
    readonly orNoneMode: boolean;

    constructor(sinfo: SourceInfo, keyname: string, valtype: TIRTypeKey, etype: TIRTypeKey, orNoneMode: boolean) {
        super(TIRExpressionTag.AccessEnvValue, sinfo, etype, `environment${orNoneMode ? "?" : ""}["${keyname}"]`);
        this.keyname = keyname;
        this.valtype = valtype;
        this.orNoneMode = orNoneMode;
    }
}

class TIRAccessNamespaceConstantExpression extends TIRExpression {
    readonly ckey: TIRNamespaceConstKey;
    readonly cname: TIRNamespaceMemberName;

    constructor(sinfo: SourceInfo, ckey: TIRNamespaceConstKey, cname: TIRNamespaceMemberName, decltype: TIRTypeKey) {
        super(TIRExpressionTag.AccessNamespaceConstantExpression, sinfo, decltype, ckey);
        this.ckey = ckey;
        this.cname = cname;
    }
}

class TIRAccessConstMemberFieldExpression extends TIRExpression {
    readonly ckey: TIRMemberConstKey;
    readonly cname: TIRTypeMemberName;

    constructor(sinfo: SourceInfo, ckey: TIRMemberConstKey, cname: TIRTypeMemberName, decltype: TIRTypeKey) {
        super(TIRExpressionTag.TIRAccessConstMemberFieldExpression, sinfo, decltype, ckey);
        this.ckey = ckey;
        this.cname = cname;
    }
}

class TIRAccessVariableExpression extends TIRExpression {
    readonly name: string;

    constructor(sinfo: SourceInfo, name: string, etype: TIRTypeKey) {
        super(TIRExpressionTag.AccessVariableExpression, sinfo, etype, name);
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
    readonly ltype: TIRTypeKey; //type of the expression -- e.g. "ok" is type String
    readonly litstr: string;
    
    constructor(exp: TIRExpression, ltype: TIRTypeKey, litstr: string) {
        this.exp = exp
        this.ltype = ltype;
        this.litstr = litstr;
    }
}

export {
    TIRCodePack,
    TIRExpression, TIRInvalidExpression,
    TIRLiteralNoneExpression, TIRLiteralNothingExpression, TIRLiteralBoolExpression, TIRLiteralIntegralExpression, TIRLiteralRationalExpression, TIRLiteralFloatPointExpression, 
    TIRLiteralStringExpression, TIRLiteralASCIIStringExpression, TIRLiteralRegexExpression, TIRLiteralTypedStringExpression, TIRLiteralASCIITypedStringExpression, TIRLiteralTemplateStringExpression, TIRLiteralASCIITemplateStringExpression,
    TIRLiteralTypedPrimitiveDirectExpression, TIRLiteralTypedPrimitiveConstructorExpression,
    TIRAccessEnvValue, TIRAccessNamespaceConstantExpression, TIRAccessConstMemberFieldExpression, TIRAccessVariableExpression,
    qqqq,
    TIRPrefixNotOp, TIRPrefixNegateOp,
    TIRBinAddExpression, TIRBinSubExpression, TIRBinMultExpression, TIRBinDivExpression,
    TIRLiteralValue
};
