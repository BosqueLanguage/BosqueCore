
import { TIRCodePackType, TIRFieldKey, TIRInvokeKey, TIRMemberConstKey, TIRNamespaceConstKey, TIRNamespaceMemberName, TIRPropertyKey, TIRTupleIndex, TIRTypeKey, TIRTypeMemberName } from "./tir_assembly";

import { SourceInfo } from "../build_decls";
import { BSQRegex } from "../bsqregex";

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

    AccessFormatInfoExpression = "AccessFormatInfoExpression",
    AccessEnvValueExpression = "AccessEnvValueExpression",

    AccessNamespaceConstantExpression = "AccessNamespaceConstantExpression",
    TIRAccessConstMemberFieldExpression = " TIRAccessConstMemberFieldExpression",
    AccessVariableExpression = "AccessVariableExpression",

    LoadIndexExpression = "LoadIndexExpression",
    LoadPropertyExpression = "LoadPropertyExpression",
    LoadFieldExpression = "LoadFieldExpression",
    LoadFieldVirtualExpression = "LoadFieldVirtualExpression",

    ConstructorPrimaryDirectExpression = "ConstructorPrimaryDirectExpression",
    ConstructorPrimaryCheckExpression = "ConstructorPrimaryCheckExpression",
    ConstructorTupleExpression = "ConstructorTupleExpression",
    ConstructorRecordExpression = "ConstructorRecordExpression",
    ConstructorEphemeralValueList = "ConstructorEphemeralValueList",

    ConstructorListExpression = "ConstructorListExpression",
    ConstructorMapExpression = "ConstructorMapExpression",

    CodePackInvokeExpression = "CodePackInvokeExpression",
    ResultOkConstructorExpression = "ResultOkConstructorExpression",
    ResultErrConstructorExpression = "ResultErrConstructorExpression",
    SomethingConstructorExpression = "SomethingConstructorExpression",
    TypedeclDirectExpression = "TypedeclDirectExpression",
    TypedeclConstructorExpression = "TypedeclConstructorExpression",

    CallNamespaceFunctionExpression = "CallNamespaceFunctionExpression",
    CallNamespaceOperatorExpression = "CallNamespaceOperatorExpression",
    CallStaticFunctionExpression = "CallStaticFunctionExpression",
    CallNamespaceFunctionWithChecksExpression = "CallNamespaceFunctionWithChecksExpression",
    CallNamespaceOperatorWithChecksExpression = "CallNamespaceOperatorWithChecksExpression",
    CallStaticFunctionWithChecksExpression = "CallStaticFunctionWithChecksExpression",

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
    TaskGetIDExpression = "TaskGetIDExpression",

    AbortExpression = "AbortExpression",
    CoerceExpression = "CoerceExpression",
    CoerceSafeExpression = "CoerceSafeExpression",
    InjectExpression = "InjectExpression",
    ExtractExpression = "ExtractExpression",
    CreateCodePackExpression = "CreateCodePackExpression",

    IsNoneExpression = "IsNoneExpression",
    IsNotNoneExpression = "IsNotNoneExpression",
    IsNothingExpression = "IsNothingExpression",
    IsTypeExpression = "IsTypeExpression",
    IsSubTypeExpression = "IsSubTypeExpression",

    AsNoneExpression = "AsNoneExpression",
    AsNotNoneExpression = "AsNotNoneExpression",
    AsNothingExpression = "AsNothingExpression",
    AsTypeExpression = "AsTypeExpression",
    AsSubTypeExpression = "AsSubTypeExpression",

    CallMemberFunctionExpression = "CallMemberFunctionExpression",
    CallMemberFunctionDynamicExpression = "CallMemberFunctionDynamicExpression",
    CallMemberFunctionSelfRefExpression = "CallMemberFunctionSelfRefExpression",
    CallMemberFunctionDynamicSelfRefExpression = "CallMemberFunctionDynamicSelfRefExpression",

    CallMemberFunctionWithChecksExpression = "CallMemberFunctionWithChecksExpression",
    CallMemberFunctionDynamicWithChecksExpression = "CallMemberFunctionDynamicWithChecksExpression",
    CallMemberFunctionSelfRefWithChecksExpression = "CallMemberFunctionSelfRefWithChecksExpression",
    CallMemberFunctionDynamicSelfRefWithChecksExpression = "CallMemberFunctionDynamicSelfRefWithChecksExpression"
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
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string) {
        super(TIRExpressionTag.LiteralStringExpression, sinfo, "String", value);
        this.value = value;
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
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string) {
        super(TIRExpressionTag.LiteralASCIIStringExpression, sinfo, "ASCIIString", value);
        this.value = value;
    }
}

class TIRLiteralTypedStringExpression extends TIRExpression {
    readonly oftype: TIRTypeKey;
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string, stringoftype: TIRTypeKey, oftype: TIRTypeKey) {
        super(TIRExpressionTag.LiteralTypedStringExpression, sinfo, stringoftype, `${value}_${oftype}`);
        this.oftype = oftype;
        this.value = value;
    }
}

class TIRLiteralASCIITypedStringExpression extends TIRExpression {
    readonly oftype: TIRTypeKey;
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string, astringoftype: TIRTypeKey, oftype: TIRTypeKey) {
        super(TIRExpressionTag.LiteralASCIITypedStringExpression, sinfo, astringoftype, `${value}_${oftype}`);
        this.oftype = oftype;
        this.value = value;
    }
}

class TIRLiteralTemplateStringExpression extends TIRExpression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string, etype: TIRTypeKey) {
        super(TIRExpressionTag.LiteralTemplateStringExpression, sinfo, etype, value);
        this.value = value;
    }
}

class TIRLiteralASCIITemplateStringExpression extends TIRExpression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string, etype: TIRTypeKey) {
        super(TIRExpressionTag.LiteralASCIITemplateStringExpression, sinfo, etype, value);
        this.value = value;
    }
}

class TIRLiteralTypedPrimitiveDirectExpression extends TIRExpression {
    readonly value: TIRExpression;

    readonly constype: TIRTypeKey; //The type that is constructed
    readonly basetype: TIRTypeKey; //The base representation of this (Bool, Int, String, ...) -- should be type of value expression

    constructor(sinfo: SourceInfo, value: TIRExpression, constype: TIRTypeKey, basetype: TIRTypeKey) {
        super(TIRExpressionTag.LiteralTypedPrimitiveDirectExpression, sinfo, constype, `${value.expstr}_${constype}`);
        this.value = value;

        this.constype = constype;
        this.basetype = basetype;
    }

    isFailableOperation(): boolean {
        return this.value.isFailableOperation();
    }

    getUsedVars(): string[] {
        return this.value.getUsedVars();
    }
}

class TIRLiteralTypedPrimitiveConstructorExpression extends TIRExpression {
    readonly value: TIRExpression;

    readonly constype: TIRTypeKey; //The type that is constructed
    readonly basetype: TIRTypeKey; //The base representation of this (Bool, Int, String, ...) -- should be type of value expression

    constructor(sinfo: SourceInfo, value: TIRExpression, constype: TIRTypeKey, basetype: TIRTypeKey) {
        super(TIRExpressionTag.LiteralTypedPrimitiveConstructorExpression, sinfo, constype, `${value.expstr}_${constype}`);
        this.value = value;

        this.constype = constype;
        this.basetype = basetype;
    }

    isFailableOperation(): boolean {
        return true;
    }

    getUsedVars(): string[] {
        return this.value.getUsedVars();
    }

    //
    //TODO: compiler may want to treat this like a constant and precompute with a reference for any uses
    //
}

class TIRAccessEnvValueExpression extends TIRExpression {
    readonly keyname: string;
    readonly valtype: TIRTypeKey;
    readonly restype: TIRTypeKey;
    readonly orNoneMode: boolean;

    constructor(sinfo: SourceInfo, keyname: string, valtype: TIRTypeKey, restype: TIRTypeKey, orNoneMode: boolean) {
        super(TIRExpressionTag.AccessEnvValueExpression, sinfo, restype, `environment${orNoneMode ? "?" : ""}["${keyname}"]`);
        this.keyname = keyname;
        this.valtype = valtype;
        this.restype = restype;
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

    getUsedVars(): string[] {
        return [this.name];
    }
}

class TIRLoadIndexExpression extends TIRExpression {
    readonly exp: TIRExpression;
    readonly index: TIRTupleIndex;

    constructor(sinfo: SourceInfo, exp: TIRExpression, index: TIRTupleIndex, resultType: TIRTypeKey) {
        super(TIRExpressionTag.LoadIndexExpression, sinfo, resultType, `${exp.expstr}.${index}`);
        this.exp = exp;
        this.index = index;
    }

    isFailableOperation(): boolean {
        return this.exp.isFailableOperation();
    }

    getUsedVars(): string[] {
        return this.exp.getUsedVars();
    }
} 

class TIRLoadPropertyExpression extends TIRExpression {
    readonly exp: TIRExpression;
    readonly property: TIRPropertyKey;

    constructor(sinfo: SourceInfo, exp: TIRExpression, property: TIRPropertyKey, resultType: TIRTypeKey) {
        super(TIRExpressionTag.LoadPropertyExpression, sinfo, resultType, `${exp.expstr}.${property}`);
        this.exp = exp;
        this.property = property;
    }

    isFailableOperation(): boolean {
        return this.exp.isFailableOperation();
    }

    getUsedVars(): string[] {
        return this.exp.getUsedVars();
    }
}

class TIRLoadFieldExpression extends TIRExpression {
    readonly exp: TIRExpression;
    readonly field: TIRFieldKey;

    constructor(sinfo: SourceInfo, exp: TIRExpression, field: TIRFieldKey, resultType: TIRTypeKey) {
        super(TIRExpressionTag.LoadFieldExpression, sinfo, resultType, `${exp.expstr}.${field}`);
        this.exp = exp;
        this.field = field;
    }

    isFailableOperation(): boolean {
        return this.exp.isFailableOperation();
    }

    getUsedVars(): string[] {
        return this.exp.getUsedVars();
    }
}

class TIRLoadFieldVirtualExpression extends TIRExpression {
    readonly exp: TIRExpression;
    readonly field: TIRFieldKey;

    constructor(sinfo: SourceInfo, exp: TIRExpression, field: TIRFieldKey, resultType: TIRTypeKey) {
        super(TIRExpressionTag.LoadFieldVirtualExpression, sinfo, resultType, `${exp.expstr}.${field}`);
        this.exp = exp;
        this.field = field;
    }

    isFailableOperation(): boolean {
        return this.exp.isFailableOperation();
    }

    getUsedVars(): string[] {
        return this.exp.getUsedVars();
    }
}

class TIRConstructorPrimaryDirectExpression extends TIRExpression {
    readonly oftype: TIRTypeKey;
    readonly args: TIRExpression[];

    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.ConstructorPrimaryDirectExpression, sinfo, oftype, `${oftype}{${args.map((arg) => arg.expstr).join(", ")}`);
        this.oftype = oftype;
        this.args = args;
    }

    isFailableOperation(): boolean {
        return this.args.some((arg) => arg.isFailableOperation());
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(...this.args.map((arg) => arg.getUsedVars()));
    }
}

class TIRConstructorPrimaryCheckExpression extends TIRExpression {
    readonly oftype: TIRTypeKey;
    readonly args: TIRExpression[];

    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.ConstructorPrimaryCheckExpression, sinfo, oftype, `${oftype}{${args.map((arg) => arg.expstr).join(", ")}`);
        this.oftype = oftype;
        this.args = args;
    }

    isFailableOperation(): boolean {
        return true;
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(...this.args.map((arg) => arg.getUsedVars()));
    }
}

class TIRConstructorTupleExpression extends TIRExpression {
    readonly oftype: TIRTypeKey;
    readonly args: TIRExpression[];

    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.ConstructorTupleExpression, sinfo, oftype, `[${args.map((arg) => arg.expstr).join(", ")}]`);
        this.oftype = oftype;
        this.args = args;
    }

    isFailableOperation(): boolean {
        return this.args.some((arg) => arg.isFailableOperation());
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(...this.args.map((arg) => arg.getUsedVars()));
    }
}

class TIRConstructorRecordExpression extends TIRExpression {
    readonly oftype: TIRTypeKey;
    readonly args: TIRExpression[];

    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.ConstructorRecordExpression, sinfo, oftype, `{${args.map((arg) => arg.expstr).join(", ")}}`);
        this.oftype = oftype;
        this.args = args;
    }

    isFailableOperation(): boolean {
        return this.args.some((arg) => arg.isFailableOperation());
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(...this.args.map((arg) => arg.getUsedVars()));
    }
}

class TIRConstructorEphemeralValueList extends TIRExpression {
    readonly oftype: TIRTypeKey;
    readonly args: TIRExpression[];

    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.ConstructorTupleExpression, sinfo, oftype, `elist -- ${args.map((arg) => arg.expstr).join(", ")}`);
        this.oftype = oftype;
        this.args = args;
    }

    isFailableOperation(): boolean {
        return this.args.some((arg) => arg.isFailableOperation());
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(...this.args.map((arg) => arg.getUsedVars()));
    }
}

class TIRConstructorListExpression  extends TIRExpression {
    readonly oftype: TIRTypeKey;
    readonly args: TIRExpression[];

    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.ConstructorListExpression, sinfo, oftype, `List{${args.map((arg) => arg.expstr).join(", ")}}`);
        this.oftype = oftype;
        this.args = args;
    }

    isFailableOperation(): boolean {
        return this.args.some((arg) => arg.isFailableOperation());
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(...this.args.map((arg) => arg.getUsedVars()));
    }
}
    
class TIRConstructorMapExpression extends TIRExpression {
    readonly oftype: TIRTypeKey;
    readonly args: TIRExpression[];

    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.ConstructorMapExpression, sinfo, oftype, `Map{${args.map((arg) => arg.expstr).join(", ")}}`);
        this.oftype = oftype;
        this.args = args;
    }

    isFailableOperation(): boolean {
        return true;
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(...this.args.map((arg) => arg.getUsedVars()));
    }
}

/*
    CodePackInvokeExpression = "CodePackInvokeExpression",
*/

class TIRResultOkConstructorExpression extends TIRExpression {
    readonly oftype: TIRTypeKey;
    readonly arg: TIRExpression;

    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, arg: TIRExpression) {
        super(TIRExpressionTag.ResultOkConstructorExpression, sinfo, oftype, `cons_ok<${oftype}>{${arg.expstr}}`);
        this.oftype = oftype;
        this.arg = arg;
    }

    isFailableOperation(): boolean {
        return this.arg.isFailableOperation();
    }

    getUsedVars(): string[] {
        return this.arg.getUsedVars();
    }
}


class TIRResultErrConstructorExpression extends TIRExpression {
    readonly oftype: TIRTypeKey;
    readonly arg: TIRExpression;

    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, arg: TIRExpression) {
        super(TIRExpressionTag.ResultErrConstructorExpression, sinfo, oftype, `cons_err<${oftype}>{${arg.expstr}}`);
        this.oftype = oftype;
        this.arg = arg;
    }

    isFailableOperation(): boolean {
        return this.arg.isFailableOperation();
    }

    getUsedVars(): string[] {
        return this.arg.getUsedVars();
    }
}


class TIRSomethingConstructorExpression extends TIRExpression {
    readonly oftype: TIRTypeKey;
    readonly arg: TIRExpression;

    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, arg: TIRExpression) {
        super(TIRExpressionTag.SomethingConstructorExpression, sinfo, oftype, `cons_something<${oftype}>{${arg.expstr}}`);
        this.oftype = oftype;
        this.arg = arg;
    }

    isFailableOperation(): boolean {
        return this.arg.isFailableOperation();
    }

    getUsedVars(): string[] {
        return this.arg.getUsedVars();
    }
}

class TIRTypedeclDirectExpression extends TIRExpression {
    readonly oftype: TIRTypeKey;
    readonly arg: TIRExpression;

    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, arg: TIRExpression) {
        super(TIRExpressionTag.TypedeclDirectExpression, sinfo, oftype, `cons_typedecl<${oftype}>{${arg.expstr}}`);
        this.oftype = oftype;
        this.arg = arg;
    }

    isFailableOperation(): boolean {
        return this.arg.isFailableOperation();
    }

    getUsedVars(): string[] {
        return this.arg.getUsedVars();
    }
}
class TIRTypedeclConstructorExpression extends TIRExpression {
    readonly oftype: TIRTypeKey;
    readonly arg: TIRExpression;

    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, arg: TIRExpression) {
        super(TIRExpressionTag.TypedeclConstructorExpression, sinfo, oftype, `cons_typedecl<${oftype}>{${arg.expstr}}`);
        this.oftype = oftype;
        this.arg = arg;
    }

    isFailableOperation(): boolean {
        return true;
    }

    getUsedVars(): string[] {
        return this.arg.getUsedVars();
    }
}

class TIRCallNamespaceFunctionExpression extends TIRExpression {
    readonly fkey: TIRInvokeKey;
    readonly args: TIRExpression[]; 

    constructor(sinfo: SourceInfo, fkey: TIRInvokeKey, rtype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.CallNamespaceFunctionExpression, sinfo, rtype, `${fkey}(${args.map((arg) => arg.expstr).join(", ")})`);
        this.fkey = fkey;
        this.args = args;
    }

    isFailableOperation(): boolean {
        return this.args.some((arg) => arg.isFailableOperation());
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(...this.args.map((arg) => arg.getUsedVars()));
    }
}

class TIRCallNamespaceOperatorExpression extends TIRExpression {
    readonly declkey: TIRInvokeKey; //to the abstract declaration
    readonly args: TIRExpression[]; 

    constructor(sinfo: SourceInfo, declkey: TIRInvokeKey, rtype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.CallNamespaceOperatorExpression, sinfo, rtype, `${declkey}(${args.map((arg) => arg.expstr).join(", ")})`);
        this.declkey = declkey;
        this.args = args;
    }

    isFailableOperation(): boolean {
        return this.args.some((arg) => arg.isFailableOperation());
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(...this.args.map((arg) => arg.getUsedVars()));
    }
}

class TIRCallStaticFunctionExpression extends TIRExpression {
    readonly fkey: TIRInvokeKey;
    readonly args: TIRExpression[]; 

    constructor(sinfo: SourceInfo, fkey: TIRInvokeKey, rtype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.CallStaticFunctionExpression, sinfo, rtype, `${fkey}(${args.map((arg) => arg.expstr).join(", ")})`);
        this.fkey = fkey;
        this.args = args;
    }

    isFailableOperation(): boolean {
        return this.args.some((arg) => arg.isFailableOperation());
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(...this.args.map((arg) => arg.getUsedVars()));
    }
}

class TIRCallNamespaceFunctionWithChecksExpression extends TIRExpression {
    readonly fkey: TIRInvokeKey;
    readonly args: TIRExpression[]; 

    constructor(sinfo: SourceInfo, fkey: TIRInvokeKey, rtype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.CallNamespaceFunctionWithChecksExpression, sinfo, rtype, `${fkey}(${args.map((arg) => arg.expstr).join(", ")})`);
        this.fkey = fkey;
        this.args = args;
    }

    isFailableOperation(): boolean {
        return true;
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(...this.args.map((arg) => arg.getUsedVars()));
    }
}

class TIRCallNamespaceOperatorWithChecksExpression extends TIRExpression {
    readonly declkey: TIRInvokeKey; //to the abstract declaration
    readonly args: TIRExpression[]; 

    constructor(sinfo: SourceInfo, declkey: TIRInvokeKey, rtype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.CallNamespaceOperatorWithChecksExpression, sinfo, rtype, `${declkey}(${args.map((arg) => arg.expstr).join(", ")})`);
        this.declkey = declkey;
        this.args = args;
    }

    isFailableOperation(): boolean {
        return true;
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(...this.args.map((arg) => arg.getUsedVars()));
    }
}

class TIRCallStaticFunctionWithChecksExpression extends TIRExpression {
    readonly fkey: TIRInvokeKey;
    readonly args: TIRExpression[]; 

    constructor(sinfo: SourceInfo, fkey: TIRInvokeKey, rtype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.CallStaticFunctionWithChecksExpression, sinfo, rtype, `${fkey}(${args.map((arg) => arg.expstr).join(", ")})`);
        this.fkey = fkey;
        this.args = args;
    }

    isFailableOperation(): boolean {
        return true;
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(...this.args.map((arg) => arg.getUsedVars()));
    }
}

class TIRLogicActionAndExpression extends TIRExpression {
    readonly args: TIRExpression[]; 

    constructor(sinfo: SourceInfo, args: TIRExpression[]) {
        super(TIRExpressionTag.CallStaticFunctionWithChecksExpression, sinfo, "Bool", `/\\(${args.map((arg) => arg.expstr).join(", ")})`);
        this.args = args;
    }

    isFailableOperation(): boolean {
        return this.args.some((arg) => arg.isFailableOperation());
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(...this.args.map((arg) => arg.getUsedVars()));
    }
}

class TIRLogicActionOrExpression extends TIRExpression {
    readonly args: TIRExpression[]; 

    constructor(sinfo: SourceInfo, args: TIRExpression[]) {
        super(TIRExpressionTag.CallStaticFunctionWithChecksExpression, sinfo, "Bool", `\\/(${args.map((arg) => arg.expstr).join(", ")})`);
        this.args = args;
    }

    isFailableOperation(): boolean {
        return this.args.some((arg) => arg.isFailableOperation());
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(...this.args.map((arg) => arg.getUsedVars()));
    }
}

class TIRPrefixNotOp extends TIRExpression {
    readonly exp: TIRExpression;

    constructor(sinfo: SourceInfo, exp: TIRExpression) {
        super(TIRExpressionTag.PrefixNotOpExpression, sinfo, "Bool", `!(${exp.expstr})`);
        this.exp = exp;
    }

    isFailableOperation(): boolean {
        return this.exp.isFailableOperation();
    }

    getUsedVars(): string[] {
        return this.exp.getUsedVars();
    }
}

class TIRPrefixNegateOp extends TIRExpression {
    readonly optype: TIRTypeKey;
    readonly exp: TIRExpression;

    constructor(sinfo: SourceInfo, exp: TIRExpression, ntype: TIRTypeKey) {
        super(TIRExpressionTag.PrefixNegateOpExpression, sinfo, ntype, `-(${exp.expstr})`);
        this.optype = ntype;
        this.exp = exp;
    }

    isFailableOperation(): boolean {
        return this.isFailableOperation();
    }

    getUsedVars(): string[] {
        return this.exp.getUsedVars();
    }
}

class TIRBinAddExpression extends TIRExpression {
    readonly optype: TIRTypeKey;
    readonly lhs: TIRExpression;
    readonly rhs: TIRExpression;

    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, ntype: TIRTypeKey) {
        super(TIRExpressionTag.BinAddExpression, sinfo, ntype, `(${lhs.expstr} + ${rhs.expstr})`);
        this.optype = ntype;
        this.lhs = lhs;
        this.rhs = rhs;
    }
    
    isFailableOperation(): boolean {
        return this.lhs.isFailableOperation() || this.rhs.isFailableOperation();
    }

    isOverflowableOperation(): boolean {
        return this.optype === "Nat" || this.optype === "Int";
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(this.lhs.getUsedVars(), this.rhs.getUsedVars());
    }
}

class TIRBinSubExpression extends TIRExpression {
    readonly optype: TIRTypeKey;
    readonly lhs: TIRExpression;
    readonly rhs: TIRExpression;

    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, ntype: TIRTypeKey) {
        super(TIRExpressionTag.BinSubExpression, sinfo, ntype, `(${lhs.expstr} - ${rhs.expstr})`);
        this.optype = ntype;
        this.lhs = lhs;
        this.rhs = rhs;
    }

    isFailableOperation(): boolean {
        //unsigned underflow is a more dangerous issue that just overflows
        return (this.optype === "Nat" || this.optype === "BigNat") || (this.lhs.isFailableOperation() || this.rhs.isFailableOperation());
    }

    isOverflowableOperation(): boolean {
        return this.optype === "Nat" || this.optype === "Int";
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(this.lhs.getUsedVars(), this.rhs.getUsedVars());
    }
}

class TIRBinMultExpression extends TIRExpression {
    readonly optype: TIRTypeKey;
    readonly lhs: TIRExpression;
    readonly rhs: TIRExpression;

    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, ntype: TIRTypeKey) {
        super(TIRExpressionTag.BinMultExpression, sinfo, ntype, `(${lhs.expstr} * ${rhs.expstr})`);
        this.optype = ntype;
        this.lhs = lhs;
        this.rhs = rhs;
    }

    isFailableOperation(): boolean {
        return this.lhs.isFailableOperation() || this.rhs.isFailableOperation();
    }

    isOverflowableOperation(): boolean {
        return this.optype === "Nat" || this.optype === "Int";
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(this.lhs.getUsedVars(), this.rhs.getUsedVars());
    }
}

class TIRBinDivExpression extends TIRExpression {
    readonly optype: TIRTypeKey;
    readonly lhs: TIRExpression;
    readonly rhs: TIRExpression;

    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, ntype: TIRTypeKey) {
        super(TIRExpressionTag.BinDivExpression, sinfo, ntype, `(${lhs.expstr} / ${rhs.expstr})`);
        this.optype = ntype;
        this.lhs = lhs;
        this.rhs = rhs;
    }

    isFailableOperation(): boolean {
        return true; //div 0
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(this.lhs.getUsedVars(), this.rhs.getUsedVars());
    }
}

class TIRBinKeyEqExpression extends TIRExpression {
    readonly optype: TIRTypeKey;
    readonly lhs: TIRExpression;
    readonly rhs: TIRExpression;

    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, optype: TIRTypeKey) {
        super(TIRExpressionTag.BinKeyEqExpression, sinfo, "Bool", `KeyType::eq<${optype}>(${lhs.expstr}, ${rhs.expstr})`);
        this.optype = optype;
        this.lhs = lhs;
        this.rhs = rhs;
    }

    isFailableOperation(): boolean {
        return this.lhs.isFailableOperation() || this.rhs.isFailableOperation();
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(this.lhs.getUsedVars(), this.rhs.getUsedVars());
    }
}

class TIRBinKeyNeqExpression extends TIRExpression {
    readonly optype: TIRTypeKey;
    readonly lhs: TIRExpression;
    readonly rhs: TIRExpression;

    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, optype: TIRTypeKey) {
        super(TIRExpressionTag.BinKeyNeqExpression, sinfo, "Bool", `KeyType::neq<${optype}>(${lhs.expstr}, ${rhs.expstr})`);
        this.optype = optype;
        this.lhs = lhs;
        this.rhs = rhs;
    }

    isFailableOperation(): boolean {
        return this.lhs.isFailableOperation() || this.rhs.isFailableOperation();
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(this.lhs.getUsedVars(), this.rhs.getUsedVars());
    }
}

class TIRBinKeyLessExpression extends TIRExpression {
    readonly optype: TIRTypeKey;
    readonly lhs: TIRExpression;
    readonly rhs: TIRExpression;

    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, optype: TIRTypeKey) {
        super(TIRExpressionTag.BinKeyLessExpression, sinfo, "Bool", `KeyType::less<${optype}>(${lhs.expstr}, ${rhs.expstr})`);
        this.optype = optype;
        this.lhs = lhs;
        this.rhs = rhs;
    }

    isFailableOperation(): boolean {
        return this.lhs.isFailableOperation() || this.rhs.isFailableOperation();
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(this.lhs.getUsedVars(), this.rhs.getUsedVars());
    }
}

class TIRNumericEqExpression extends TIRExpression {
    readonly optype: TIRTypeKey;
    readonly lhs: TIRExpression;
    readonly rhs: TIRExpression;

    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, ntype: TIRTypeKey) {
        super(TIRExpressionTag.NumericEqExpression, sinfo, "Bool", `(${lhs.expstr} == ${rhs.expstr})`);
        this.optype = ntype;
        this.lhs = lhs;
        this.rhs = rhs;
    }

    isFailableOperation(): boolean {
        return this.lhs.isFailableOperation() || this.rhs.isFailableOperation();
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(this.lhs.getUsedVars(), this.rhs.getUsedVars());
    }
}

class TIRNumericNeqExpression extends TIRExpression {
    readonly optype: TIRTypeKey;
    readonly lhs: TIRExpression;
    readonly rhs: TIRExpression;

    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, ntype: TIRTypeKey) {
        super(TIRExpressionTag.NumericNeqExpression, sinfo, "Bool", `(${lhs.expstr} != ${rhs.expstr})`);
        this.optype = ntype;
        this.lhs = lhs;
        this.rhs = rhs;
    }

    isFailableOperation(): boolean {
        return this.lhs.isFailableOperation() || this.rhs.isFailableOperation();
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(this.lhs.getUsedVars(), this.rhs.getUsedVars());
    }
}

class TIRNumericLessExpression extends TIRExpression {
    readonly optype: TIRTypeKey;
    readonly lhs: TIRExpression;
    readonly rhs: TIRExpression;

    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, ntype: TIRTypeKey) {
        super(TIRExpressionTag.NumericLessExpression, sinfo, "Bool", `(${lhs.expstr} < ${rhs.expstr})`);
        this.optype = ntype;
        this.lhs = lhs;
        this.rhs = rhs;
    }

    isFailableOperation(): boolean {
        return this.lhs.isFailableOperation() || this.rhs.isFailableOperation();
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(this.lhs.getUsedVars(), this.rhs.getUsedVars());
    }
}

class TIRNumericLessEqExpression extends TIRExpression {
    readonly optype: TIRTypeKey;
    readonly lhs: TIRExpression;
    readonly rhs: TIRExpression;

    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, ntype: TIRTypeKey) {
        super(TIRExpressionTag.NumericLessEqExpression, sinfo, "Bool", `(${lhs.expstr} <= ${rhs.expstr})`);
        this.optype = ntype;
        this.lhs = lhs;
        this.rhs = rhs;
    }

    isFailableOperation(): boolean {
        return this.lhs.isFailableOperation() || this.rhs.isFailableOperation();
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(this.lhs.getUsedVars(), this.rhs.getUsedVars());
    }
}

class TIRNumericGreaterExpression extends TIRExpression {
    readonly optype: TIRTypeKey;
    readonly lhs: TIRExpression;
    readonly rhs: TIRExpression;

    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, ntype: TIRTypeKey) {
        super(TIRExpressionTag.NumericGreaterExpression, sinfo, "Bool", `(${lhs.expstr} > ${rhs.expstr})`);
        this.optype = ntype;
        this.lhs = lhs;
        this.rhs = rhs;
    }

    isFailableOperation(): boolean {
        return this.lhs.isFailableOperation() || this.rhs.isFailableOperation();
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(this.lhs.getUsedVars(), this.rhs.getUsedVars());
    }
}

class TIRNumericGreaterEqExpression extends TIRExpression {
    readonly optype: TIRTypeKey;
    readonly lhs: TIRExpression;
    readonly rhs: TIRExpression;

    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, ntype: TIRTypeKey) {
        super(TIRExpressionTag.NumericGreaterEqExpression, sinfo, "Bool", `(${lhs.expstr} >= ${rhs.expstr})`);
        this.optype = ntype;
        this.lhs = lhs;
        this.rhs = rhs;
    }

    isFailableOperation(): boolean {
        return this.lhs.isFailableOperation() || this.rhs.isFailableOperation();
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(this.lhs.getUsedVars(), this.rhs.getUsedVars());
    }
}

class TIRBinLogicAndxpression extends TIRExpression {
    readonly lhs: TIRExpression;
    readonly rhs: TIRExpression;

    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression) {
        super(TIRExpressionTag.BinLogicAndExpression, sinfo, "Bool", `(${lhs.expstr} && ${rhs.expstr})`);
        this.lhs = lhs;
        this.rhs = rhs;
    }

    isFailableOperation(): boolean {
        return this.lhs.isFailableOperation() || this.rhs.isFailableOperation();
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(this.lhs.getUsedVars(), this.rhs.getUsedVars());
    }
}

class TIRBinLogicOrExpression extends TIRExpression {
    readonly lhs: TIRExpression;
    readonly rhs: TIRExpression;

    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression) {
        super(TIRExpressionTag.BinLogicOrExpression, sinfo, "Bool", `(${lhs.expstr} || ${rhs.expstr})`);
        this.lhs = lhs;
        this.rhs = rhs;
    }

    isFailableOperation(): boolean {
        return this.lhs.isFailableOperation() || this.rhs.isFailableOperation();
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(this.lhs.getUsedVars(), this.rhs.getUsedVars());
    }
}

class TIRBinLogicImpliesExpression extends TIRExpression {
    readonly lhs: TIRExpression;
    readonly rhs: TIRExpression;

    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression) {
        super(TIRExpressionTag.BinLogicImpliesExpression, sinfo, "Bool", `(${lhs.expstr} ==> ${rhs.expstr})`);
        this.lhs = lhs;
        this.rhs = rhs;
    }

    isFailableOperation(): boolean {
        return this.lhs.isFailableOperation() || this.rhs.isFailableOperation();
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(this.lhs.getUsedVars(), this.rhs.getUsedVars());
    }
}

class TIRMapEntryConstructorExpression extends TIRExpression {
    readonly ktype: TIRTypeKey;
    readonly vtype: TIRTypeKey;
    readonly oftype: TIRTypeKey;

    readonly kexp: TIRExpression;
    readonly vexp: TIRExpression;
    
    constructor(sinfo: SourceInfo, kexp: TIRExpression, vexp: TIRExpression, ktype: TIRTypeKey, vtype: TIRTypeKey, oftype: TIRTypeKey) {
        super(TIRExpressionTag.MapEntryConstructorExpression, sinfo, oftype, `(${kexp.expstr} => ${vexp.expstr})`);
        this.ktype = ktype;
        this.vtype = vtype;
        this.oftype = oftype;

        this.kexp = kexp;
        this.vexp = vexp;
    }

    isFailableOperation(): boolean {
        return this.kexp.isFailableOperation() || this.vexp.isFailableOperation();
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(this.kexp.getUsedVars(), this.vexp.getUsedVars());
    }
}

class TIRIfExpression extends TIRExpression {
    readonly ifentry: {test: TIRExpression, value: TIRExpression};
    readonly elifentries: {test: TIRExpression, value: TIRExpression}[];
    readonly elseentry: TIRExpression;

    constructor(sinfo: SourceInfo, etype: TIRTypeKey, ifentry: {test: TIRExpression, value: TIRExpression}, elifentries: {test: TIRExpression, value: TIRExpression}[], elseentry: TIRExpression) {
        super(TIRExpressionTag.IfExpression, sinfo, etype, `if(${ifentry.test.expstr}) then ${ifentry.value.expstr} ${elifentries.map((efi) => `elif(${efi.test.expstr}) then ${efi.value.expstr}`)} else ${elseentry.expstr}`);
        this.ifentry = ifentry;
        this.elifentries = elifentries;
        this.elseentry = elseentry;
    }

    isFailableOperation(): boolean {
        return this.ifentry.test.isFailableOperation() || this.ifentry.value.isFailableOperation() ||
            this.elifentries.some((ee) => ee.test.isFailableOperation() || ee.value.isFailableOperation()) ||
            this.elseentry.isFailableOperation();
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(
            this.ifentry.test.getUsedVars(), this.ifentry.value.getUsedVars(),
            ...this.elifentries.map((efi) => efi.test.getUsedVars()), ...this.elifentries.map((efi) => efi.value.getUsedVars()),
            this.elseentry.getUsedVars()
        );
    }
}

class TIRSwitchExpression extends TIRExpression {
    readonly exp: TIRExpression;
    readonly clauses: {match: TIRLiteralValue, value: TIRExpression}[];
    readonly edefault: TIRExpression | undefined;
    readonly isexhaustive: boolean;

    constructor(sinfo: SourceInfo, etype: TIRTypeKey, exp: TIRExpression, clauses: {match: TIRLiteralValue, value: TIRExpression}[], edefault: TIRExpression | undefined, isexhaustive: boolean) {
        super(TIRExpressionTag.SwitchExpression, sinfo, etype, `switch(${exp.expstr}) ${clauses.map((ci) => `(${ci.match.litstr} => ${ci.value.expstr})`)}${edefault !== undefined ? "(_ => " + edefault.expstr : ""}`);
        this.exp = exp;
        this.clauses = clauses;
        this.edefault = edefault;
        this.isexhaustive = isexhaustive;
    }

    isFailableOperation(): boolean {
        return this.exp.isFailableOperation() || 
            this.clauses.some((cc) => cc.match.exp.isFailableOperation() || cc.value.isFailableOperation()) ||
            (this.edefault !== undefined && this.edefault.isFailableOperation()) ||
            !this.isexhaustive;
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(
            this.exp.getUsedVars(),
            ...this.clauses.map((ci) => ci.match.exp.getUsedVars()), ...this.clauses.map((ci) => ci.value.getUsedVars()),
            (this.edefault !== undefined ? this.edefault.getUsedVars() : [])
        );
    }
}

class TIRMatchExpression extends TIRExpression {
    readonly exp: TIRExpression;
    readonly clauses: {match: TIRTypeKey, value: TIRExpression}[];
    readonly edefault: TIRExpression | undefined;
    readonly isexhaustive: boolean;

    constructor(sinfo: SourceInfo, etype: TIRTypeKey, exp: TIRExpression, clauses: {match: TIRTypeKey, value: TIRExpression}[], edefault: TIRExpression | undefined, isexhaustive: boolean) {
        super(TIRExpressionTag.MatchExpression, sinfo, etype, `match(${exp.expstr}) ${clauses.map((ci) => `(${ci.match} => ${ci.value.expstr})`)}${edefault !== undefined ? "(_ => " + edefault.expstr : ""}`);
        this.exp = exp;
        this.clauses = clauses;
        this.edefault = edefault;
        this.isexhaustive = isexhaustive;
    }

    isFailableOperation(): boolean {
        return this.exp.isFailableOperation() || 
            this.clauses.some((cc) => cc.value.isFailableOperation()) ||
            (this.edefault !== undefined && this.edefault.isFailableOperation()) ||
            !this.isexhaustive;
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(
            this.exp.getUsedVars(),
            ...this.clauses.map((ci) => ci.value.getUsedVars()),
            (this.edefault !== undefined ? this.edefault.getUsedVars() : [])
        );
    }
}

class TIRTaskSelfFieldExpression extends TIRExpression {
    readonly field: string;

    constructor(sinfo: SourceInfo, field: string, resultType: TIRTypeKey) {
        super(TIRExpressionTag.TaskSelfFieldExpression, sinfo, resultType, `self.${field}`);
        this.field = field;
    }

    getUsedVars(): string[] {
        return [`self.${this.field}`];
    }
}

class TIRTaskGetIDExpression extends TIRExpression {
    constructor(sinfo: SourceInfo, resultType: TIRTypeKey) {
        super(TIRExpressionTag.TaskGetIDExpression, sinfo, resultType, `getTaskID`);
    }

    getUsedVars(): string[] {
        return [];
    }
}

class TIRAbortExpression extends TIRExpression {
    readonly msg: string;

    constructor(sinfo: SourceInfo, etype: TIRTypeKey, msg: string) {
        super(TIRExpressionTag.AbortExpression, sinfo, etype, `abort<${etype}>("${msg}")`);
        this.msg = msg;
    }

    isFailableOperation(): boolean {
        return true;
    }

    getUsedVars(): string[] {
        return [];
    }
}

class TIRCoerceExpression extends TIRExpression {
    readonly exp: TIRExpression;
    readonly totype: TIRTypeKey;

    constructor(sinfo: SourceInfo, exp: TIRExpression, totype: TIRTypeKey) {
        super(TIRExpressionTag.CoerceExpression, sinfo, totype, `coerce<${totype}>(${exp.expstr})`);
        this.exp = exp;
        this.totype = totype;
    }

    isFailableOperation(): boolean {
        return true;
    }

    getUsedVars(): string[] {
        return this.exp.getUsedVars();
    }
}

class TIRCoerceSafeExpression extends TIRExpression {
    readonly exp: TIRExpression;
    readonly totype: TIRTypeKey;
    
    constructor(sinfo: SourceInfo, exp: TIRExpression, totype: TIRTypeKey) {
        super(TIRExpressionTag.CoerceSafeExpression, sinfo, totype, `coerce_safe<${totype}>(${exp.expstr})`);
        this.exp = exp;
        this.totype = totype;
    }

    isFailableOperation(): boolean {
        return this.exp.isFailableOperation();
    }
    
    getUsedVars(): string[] {
        return this.exp.getUsedVars();
    }
}

class TIRInjectExpression extends TIRExpression {
    readonly exp: TIRExpression;
    readonly totype: TIRTypeKey;
    
    constructor(sinfo: SourceInfo, exp: TIRExpression, totype: TIRTypeKey) {
        super(TIRExpressionTag.InjectExpression, sinfo, totype, `inject<${totype}>(${exp.expstr})`);
        this.exp = exp;
        this.totype = totype;
    }
    
    isFailableOperation(): boolean {
        return this.exp.isFailableOperation();
    }

    getUsedVars(): string[] {
        return this.exp.getUsedVars();
    }
}

class TIRExtractExpression extends TIRExpression {
    readonly exp: TIRExpression;
    readonly totype: TIRTypeKey;
    
    constructor(sinfo: SourceInfo, exp: TIRExpression, totype: TIRTypeKey) {
        super(TIRExpressionTag.ExtractExpression, sinfo, totype, `extract<${totype}>(${exp.expstr})`);
        this.exp = exp;
        this.totype = totype;
    }
    
    isFailableOperation(): boolean {
        return this.exp.isFailableOperation();
    }

    getUsedVars(): string[] {
        return this.exp.getUsedVars();
    }
}

/*
class TIRCreateCodePackExpression = "CreateCodePackExpression",
*/

class TIRIsNoneExpression extends TIRExpression {
    readonly exp: TIRExpression;
    
    constructor(sinfo: SourceInfo, exp: TIRExpression) {
        super(TIRExpressionTag.IsNoneExpression, sinfo, "Bool", `isnone(${exp.expstr})`);
        this.exp = exp;
    }
    
    isFailableOperation(): boolean {
        return this.exp.isFailableOperation();
    }

    getUsedVars(): string[] {
        return this.exp.getUsedVars();
    }
}

class TIRIsNotNoneExpression extends TIRExpression {
    readonly exp: TIRExpression;
    
    constructor(sinfo: SourceInfo, exp: TIRExpression) {
        super(TIRExpressionTag.IsNotNoneExpression, sinfo, "Bool", `!isnone(${exp.expstr})`);
        this.exp = exp;
    }
    
    isFailableOperation(): boolean {
        return this.exp.isFailableOperation();
    }

    getUsedVars(): string[] {
        return this.exp.getUsedVars();
    }
}

class TIRIsNothingExpression extends TIRExpression {
    readonly exp: TIRExpression;
    
    constructor(sinfo: SourceInfo, exp: TIRExpression) {
        super(TIRExpressionTag.IsNothingExpression, sinfo, "Bool", `isnothing(${exp.expstr})`);
        this.exp = exp;
    }
    
    isFailableOperation(): boolean {
        return this.exp.isFailableOperation();
    }

    getUsedVars(): string[] {
        return this.exp.getUsedVars();
    }
}

class TIRIsTypeExpression extends TIRExpression {
    readonly exp: TIRExpression;
    readonly oftype: TIRTypeKey;
    
    constructor(sinfo: SourceInfo, exp: TIRExpression, oftype: TIRTypeKey) {
        super(TIRExpressionTag.IsTypeExpression, sinfo, "Bool", `istype<${oftype}>(${exp.expstr})`);
        this.exp = exp;
        this.oftype = oftype;
    }
    
    isFailableOperation(): boolean {
        return this.exp.isFailableOperation();
    }

    getUsedVars(): string[] {
        return this.exp.getUsedVars();
    }
}

class TIRIsSubTypeExpression extends TIRExpression {
    readonly exp: TIRExpression;
    readonly oftype: TIRTypeKey;
    
    constructor(sinfo: SourceInfo, exp: TIRExpression, oftype: TIRTypeKey) {
        super(TIRExpressionTag.IsSubTypeExpression, sinfo, "Bool", `issubtype<${oftype}>(${exp.expstr})`);
        this.exp = exp;
        this.oftype = oftype;
    }
    
    isFailableOperation(): boolean {
        return this.exp.isFailableOperation();
    }

    getUsedVars(): string[] {
        return this.exp.getUsedVars();
    }
}

class TIRAsNoneExpression extends TIRExpression {
    readonly exp: TIRExpression;
    
    constructor(sinfo: SourceInfo, exp: TIRExpression) {
        super(TIRExpressionTag.AsNoneExpression, sinfo, "None", `asnone(${exp.expstr})`);
        this.exp = exp;
    }
    
    isFailableOperation(): boolean {
        return true;
    }

    getUsedVars(): string[] {
        return this.exp.getUsedVars();
    }
}

class TIRAsNotNoneExpression extends TIRExpression {
    readonly exp: TIRExpression;
    
    constructor(sinfo: SourceInfo, exp: TIRExpression) {
        super(TIRExpressionTag.AsNotNoneExpression, sinfo, "Some", `assome(${exp.expstr})`);
        this.exp = exp;
    }
    
    isFailableOperation(): boolean {
        return true;
    }

    getUsedVars(): string[] {
        return this.exp.getUsedVars();
    }
}

class TIRAsNothingExpression extends TIRExpression {
    readonly exp: TIRExpression;
    
    constructor(sinfo: SourceInfo, exp: TIRExpression) {
        super(TIRExpressionTag.AsNothingExpression, sinfo, "Nothing", `asnothing(${exp.expstr})`);
        this.exp = exp;
    }
    
    isFailableOperation(): boolean {
        return true;
    }

    getUsedVars(): string[] {
        return this.exp.getUsedVars();
    }
}

class TIRAsTypeExpression extends TIRExpression {
    readonly exp: TIRExpression;
    readonly oftype: TIRTypeKey;
    
    constructor(sinfo: SourceInfo, exp: TIRExpression, oftype: TIRTypeKey) {
        super(TIRExpressionTag.AsTypeExpression, sinfo, oftype, `astype<${oftype}>(${exp.expstr})`);
        this.exp = exp;
        this.oftype = oftype;
    }
    
    isFailableOperation(): boolean {
        return true;
    }

    getUsedVars(): string[] {
        return this.exp.getUsedVars();
    }
}

class TIRAsSubTypeExpression extends TIRExpression {
    readonly exp: TIRExpression;
    readonly oftype: TIRTypeKey;
    
    constructor(sinfo: SourceInfo, exp: TIRExpression, oftype: TIRTypeKey) {
        super(TIRExpressionTag.AsSubTypeExpression, sinfo, oftype, `assubtype<${oftype}>(${exp.expstr})`);
        this.exp = exp;
        this.oftype = oftype;
    }
    
    isFailableOperation(): boolean {
        return true;
    }

    getUsedVars(): string[] {
        return this.exp.getUsedVars();
    }
}

class TIRCallMemberFunctionExpression extends TIRExpression {
    readonly fkey: TIRInvokeKey;
    readonly thisarg: TIRExpression;
    readonly args: TIRExpression[]; 

    constructor(sinfo: SourceInfo, fkey: TIRInvokeKey, rtype: TIRTypeKey, thisarg: TIRExpression, args: TIRExpression[]) {
        super(TIRExpressionTag.CallMemberFunctionExpression, sinfo, rtype, `${thisarg.expstr}.${fkey}(${args.map((arg) => arg.expstr).join(", ")})`);
        this.fkey = fkey;
        this.thisarg = thisarg;
        this.args = args;
    }

    isFailableOperation(): boolean {
        return this.thisarg.isFailableOperation() || this.args.some((arg) => arg.isFailableOperation());
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(this.thisarg.getUsedVars(), ...this.args.map((arg) => arg.getUsedVars()));
    }
}

class TIRCallMemberFunctionDynamicExpression extends TIRExpression {
    readonly declkey: TIRInvokeKey; //to the abstract declaration
    readonly inferthistype: TIRTypeKey;
    readonly inferfkey: TIRInvokeKey | undefined;
    readonly thisarg: TIRExpression;
    readonly args: TIRExpression[]; 

    constructor(sinfo: SourceInfo, declkey: TIRInvokeKey, inferthistype: TIRTypeKey, inferfkey: TIRInvokeKey | undefined, rtype: TIRTypeKey, thisarg: TIRExpression, args: TIRExpression[]) {
        super(TIRExpressionTag.CallMemberFunctionDynamicExpression, sinfo, rtype, `${thisarg.expstr}.${declkey}(${args.map((arg) => arg.expstr).join(", ")})`);
        this.declkey = declkey;
        this.inferthistype = inferthistype;
        this.inferfkey = inferfkey;
        this.thisarg = thisarg;
        this.args = args;
    }

    isFailableOperation(): boolean {
        return this.thisarg.isFailableOperation() || this.args.some((arg) => arg.isFailableOperation());
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(this.thisarg.getUsedVars(), ...this.args.map((arg) => arg.getUsedVars()));
    }
}

class TIRCallMemberFunctionSelfRefExpression extends TIRExpression {
    readonly fkey: TIRInvokeKey;
    readonly thisref: string;
    readonly args: TIRExpression[]; 

    constructor(sinfo: SourceInfo, fkey: TIRInvokeKey, rtype: TIRTypeKey, thisref: string, args: TIRExpression[]) {
        super(TIRExpressionTag.CallMemberFunctionSelfRefExpression, sinfo, rtype, `ref ${thisref}.${fkey}(${args.map((arg) => arg.expstr).join(", ")})`);
        this.fkey = fkey;
        this.thisref = thisref;
        this.args = args;
    }

    isFailableOperation(): boolean {
        return this.args.some((arg) => arg.isFailableOperation());
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo([this.thisref], ...this.args.map((arg) => arg.getUsedVars()));
    }
}

class TIRCallMemberFunctionDynamicSelfRefExpression extends TIRExpression {
    readonly declkey: TIRInvokeKey; //to the abstract declaration
    readonly inferthistype: TIRTypeKey;
    readonly inferfkey: TIRInvokeKey | undefined;
    readonly thisref: string;
    readonly args: TIRExpression[]; 

    constructor(sinfo: SourceInfo, declkey: TIRInvokeKey, inferthistype: TIRTypeKey, inferfkey: TIRInvokeKey | undefined, rtype: TIRTypeKey, thisref: string, args: TIRExpression[]) {
        super(TIRExpressionTag.CallMemberFunctionDynamicSelfRefExpression, sinfo, rtype, `ref ${thisref}.${declkey}(${args.map((arg) => arg.expstr).join(", ")})`);
        this.declkey = declkey;
        this.inferthistype = inferthistype;
        this.inferfkey = inferfkey;
        this.thisref = thisref;
        this.args = args;
    }

    isFailableOperation(): boolean {
        return this.args.some((arg) => arg.isFailableOperation());
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo([this.thisref], ...this.args.map((arg) => arg.getUsedVars()));
    }
}

class TIRCallMemberFunctionWithChecksExpression extends TIRExpression {
    readonly fkey: TIRInvokeKey;
    readonly thisarg: TIRExpression;
    readonly args: TIRExpression[]; 

    constructor(sinfo: SourceInfo, fkey: TIRInvokeKey, rtype: TIRTypeKey, thisarg: TIRExpression, args: TIRExpression[]) {
        super(TIRExpressionTag.CallMemberFunctionWithChecksExpression, sinfo, rtype, `${thisarg.expstr}.${fkey}(${args.map((arg) => arg.expstr).join(", ")})`);
        this.fkey = fkey;
        this.thisarg = thisarg;
        this.args = args;
    }

    isFailableOperation(): boolean {
        return true;
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(this.thisarg.getUsedVars(), ...this.args.map((arg) => arg.getUsedVars()));
    }
}

class TIRCallMemberFunctionDynamicWithChecksExpression extends TIRExpression {
    readonly declkey: TIRInvokeKey; //to the abstract declaration
    readonly inferthistype: TIRTypeKey;
    readonly inferfkey: TIRInvokeKey | undefined;
    readonly thisarg: TIRExpression;
    readonly args: TIRExpression[]; 

    constructor(sinfo: SourceInfo, declkey: TIRInvokeKey, inferthistype: TIRTypeKey, inferfkey: TIRInvokeKey | undefined, rtype: TIRTypeKey, thisarg: TIRExpression, args: TIRExpression[]) {
        super(TIRExpressionTag.CallMemberFunctionDynamicWithChecksExpression, sinfo, rtype, `${thisarg.expstr}.${declkey}(${args.map((arg) => arg.expstr).join(", ")})`);
        this.declkey = declkey;
        this.inferthistype = inferthistype;
        this.inferfkey = inferfkey;
        this.thisarg = thisarg;
        this.args = args;
    }

    isFailableOperation(): boolean {
        return true;
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(this.thisarg.getUsedVars(), ...this.args.map((arg) => arg.getUsedVars()));
    }
}

class TIRCallMemberFunctionSelfRefWithChecksExpression extends TIRExpression {
    readonly fkey: TIRInvokeKey;
    readonly thisref: string;
    readonly args: TIRExpression[]; 

    constructor(sinfo: SourceInfo, fkey: TIRInvokeKey, rtype: TIRTypeKey, thisref: string, args: TIRExpression[]) {
        super(TIRExpressionTag.CallMemberFunctionSelfRefWithChecksExpression, sinfo, rtype, `ref ${thisref}.${fkey}(${args.map((arg) => arg.expstr).join(", ")})`);
        this.fkey = fkey;
        this.thisref = thisref;
        this.args = args;
    }

    isFailableOperation(): boolean {
        return true;
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo([this.thisref], ...this.args.map((arg) => arg.getUsedVars()));
    }
}

class TIRCallMemberFunctionDynamicSelfRefWithChecksExpression extends TIRExpression {
    readonly declkey: TIRInvokeKey; //to the abstract declaration
    readonly inferthistype: TIRTypeKey;
    readonly inferfkey: TIRInvokeKey | undefined;
    readonly thisref: string;
    readonly args: TIRExpression[]; 

    constructor(sinfo: SourceInfo, declkey: TIRInvokeKey, inferthistype: TIRTypeKey, inferfkey: TIRInvokeKey | undefined, rtype: TIRTypeKey, thisref: string, args: TIRExpression[]) {
        super(TIRExpressionTag.CallMemberFunctionDynamicSelfRefWithChecksExpression, sinfo, rtype, `ref ${thisref}.${declkey}(${args.map((arg) => arg.expstr).join(", ")})`);
        this.declkey = declkey;
        this.inferthistype = inferthistype;
        this.inferfkey = inferfkey;
        this.thisref = thisref;
        this.args = args;
    }

    isFailableOperation(): boolean {
        return true;
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo([this.thisref], ...this.args.map((arg) => arg.getUsedVars()));
    }
}

class TIRLiteralValue {
    readonly exp: TIRExpression;
    readonly litstr: string;
    
    constructor(exp: TIRExpression, litstr: string) {
        this.exp = exp
        this.litstr = litstr;
    }
}

enum TIRStatementTag {
    NopStatement = "NopStatement",
    AbortStatement = "AbortStatement",
    AssertCheckStatement = "AssertCheckStatement",
    DebugStatement = "DebugStatement",

    VarDeclareStatement = "VarDeclareStatement",
    VarDeclareAndAssignStatement = "VarDeclareAndAssignStatement",
    VarAssignStatement = "VarAssignStatement"
}

abstract class TIRStatement {
    readonly tag: TIRStatementTag;
    readonly sinfo: SourceInfo;
    readonly stmtstr: string;

    constructor(tag: TIRStatementTag, sinfo: SourceInfo, stmtstr: string) {
        this.tag = tag;
        this.sinfo = sinfo;
        this.stmtstr = stmtstr;
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

    getModVars(): string[] {
        return [];
    }
}

class TIRNopStatement extends TIRStatement {
    constructor(sinfo: SourceInfo) {
        super(TIRStatementTag.NopStatement, sinfo, "nop;");
    }
}

class TIRAbortStatement extends TIRStatement {
    readonly msg: string;

    constructor(sinfo: SourceInfo, msg: string) {
        super(TIRStatementTag.AbortStatement, sinfo, `abort("${msg}");`);
        this.msg = msg;
    }

    isFailableOperation(): boolean {
        return true;
    }
}

class TIRAssertCheckStatement extends TIRStatement {
    readonly cond: TIRExpression;
    readonly msg: string;

    constructor(sinfo: SourceInfo, cond: TIRExpression, msg: string) {
        super(TIRStatementTag.AssertCheckStatement, sinfo, `assert(${cond.expstr}, "${msg}");`);
        this.cond = cond;
        this.msg = msg;
    }

    isFailableOperation(): boolean {
        return false;
    }

    getUsedVars(): string[] {
        return this.cond.getUsedVars();
    }
}

class TIRDebugStatement extends TIRStatement {
    readonly value: TIRExpression;

    constructor(sinfo: SourceInfo, value: TIRExpression) {
        super(TIRStatementTag.DebugStatement, sinfo, `__debug(${value.expstr});`);
        this.value = value;
    }

    getUsedVars(): string[] {
        return this.value.getUsedVars();
    }
}

class TIRVarDeclareStatement extends TIRStatement {
    readonly vname: string;
    readonly vtype: TIRTypeKey;

    constructor(sinfo: SourceInfo, vname: string, vtype: TIRTypeKey) {
        super(TIRStatementTag.VarDeclareStatement, sinfo, `let ${vname}: ${vtype};`);
        this.vname = vname;
        this.vtype = vtype;
    }

    getModVars(): string[] {
        return [this.vname];
    }
}

class TIRVarDeclareAndAssignStatement extends TIRStatement {
    readonly vname: string;
    readonly vtype: TIRTypeKey;
    readonly vexp: TIRExpression;
    readonly isConst: boolean;

    constructor(sinfo: SourceInfo, vname: string, vtype: TIRTypeKey, vexp: TIRExpression, isConst: boolean) {
        super(TIRStatementTag.VarDeclareAndAssignStatement, sinfo, `${isConst ? "const" : "let"} ${vname}: ${vtype} = ${vexp.expstr};`);
        this.vname = vname;
        this.vtype = vtype;
        this.vexp = vexp;
        this.isConst = isConst;
    }

    getUsedVars(): string[] {
        return this.vexp.getUsedVars();
    }

    getModVars(): string[] {
        return [this.vname];
    }
}

class TIRVarAssignStatement extends TIRStatement {
    readonly vname: string;
    readonly vtype: TIRTypeKey;
    readonly vexp: TIRExpression;
    readonly isConst: boolean;

    constructor(sinfo: SourceInfo, vname: string, vtype: TIRTypeKey, vexp: TIRExpression, isConst: boolean) {
        super(TIRStatementTag.VarAssignStatement, sinfo, `${vname} = ${vexp.expstr};`);
        this.vname = vname;
        this.vtype = vtype;
        this.vexp = vexp;
        this.isConst = isConst;
    }

    getUsedVars(): string[] {
        return this.vexp.getUsedVars();
    }

    getModVars(): string[] {
        return [this.vname];
    }
}

export {
    TIRCodePack,
    TIRExpressionTag, TIRExpression, TIRInvalidExpression,
    TIRLiteralNoneExpression, TIRLiteralNothingExpression, TIRLiteralBoolExpression, TIRLiteralIntegralExpression, TIRLiteralRationalExpression, TIRLiteralFloatPointExpression, 
    TIRLiteralStringExpression, TIRLiteralASCIIStringExpression, TIRLiteralRegexExpression, TIRLiteralTypedStringExpression, TIRLiteralASCIITypedStringExpression, TIRLiteralTemplateStringExpression, TIRLiteralASCIITemplateStringExpression,
    TIRLiteralTypedPrimitiveDirectExpression, TIRLiteralTypedPrimitiveConstructorExpression,
    TIRAccessEnvValueExpression, TIRAccessNamespaceConstantExpression, TIRAccessConstMemberFieldExpression, TIRAccessVariableExpression,
    TIRLoadIndexExpression, TIRLoadPropertyExpression, TIRLoadFieldExpression, TIRLoadFieldVirtualExpression,
    TIRConstructorPrimaryDirectExpression, TIRConstructorPrimaryCheckExpression, TIRConstructorTupleExpression, TIRConstructorRecordExpression, TIRConstructorEphemeralValueList, TIRConstructorListExpression, TIRConstructorMapExpression, 
    qqq,
    TIRResultOkConstructorExpression, TIRResultErrConstructorExpression, TIRSomethingConstructorExpression, TIRTypedeclDirectExpression, TIRTypedeclConstructorExpression,
    TIRCallNamespaceFunctionExpression, TIRCallNamespaceOperatorExpression, TIRCallStaticFunctionExpression, TIRCallNamespaceFunctionWithChecksExpression, TIRCallNamespaceOperatorWithChecksExpression, TIRCallStaticFunctionWithChecksExpression,
    TIRLogicActionAndExpression, TIRLogicActionOrExpression,
    TIRPrefixNotOp, TIRPrefixNegateOp,
    TIRBinAddExpression, TIRBinSubExpression, TIRBinMultExpression, TIRBinDivExpression,
    TIRBinKeyEqExpression, TIRBinKeyNeqExpression, TIRBinKeyLessExpression,
    TIRNumericEqExpression, TIRNumericNeqExpression, TIRNumericLessExpression, TIRNumericLessEqExpression, TIRNumericGreaterExpression, TIRNumericGreaterEqExpression,
    TIRBinLogicAndxpression, TIRBinLogicOrExpression, TIRBinLogicImpliesExpression,
    TIRMapEntryConstructorExpression, TIRIfExpression, TIRSwitchExpression, TIRMatchExpression,
    TIRTaskSelfFieldExpression, TIRTaskGetIDExpression,
    TIRAbortExpression, TIRCoerceExpression, TIRCoerceSafeExpression, TIRInjectExpression, TIRExtractExpression,
    jjjj,
    TIRIsNoneExpression, TIRIsNotNoneExpression, TIRIsNothingExpression, TIRIsTypeExpression, TIRIsSubTypeExpression,
    TIRAsNoneExpression, TIRAsNotNoneExpression, TIRAsNothingExpression, TIRAsTypeExpression, TIRAsSubTypeExpression,
    TIRCallMemberFunctionExpression, TIRCallMemberFunctionDynamicExpression, TIRCallMemberFunctionSelfRefExpression, TIRCallMemberFunctionDynamicSelfRefExpression, 
    TIRCallMemberFunctionWithChecksExpression, TIRCallMemberFunctionDynamicWithChecksExpression, TIRCallMemberFunctionSelfRefWithChecksExpression, TIRCallMemberFunctionDynamicSelfRefWithChecksExpression,
    TIRLiteralValue,
    TIRStatementTag,
    TIRStatement,
    TIRNopStatement, TIRAbortStatement, TIRAssertCheckStatement, TIRDebugStatement,
    TIRVarDeclareStatement, TIRVarDeclareAndAssignStatement, TIRVarAssignStatement
};
