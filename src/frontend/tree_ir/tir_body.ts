
import { TIRCodePack, TIRFieldKey, TIRInvokeKey, TIRTypeKey } from "./tir_assembly";

import { LoggerLevel, SourceInfo } from "../build_decls";
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
    AccessConstMemberFieldExpression = " AccessConstMemberFieldExpression",
    AccessVariableExpression = "AccessVariableExpression",
    AccessCapturedVariableExpression = "AccessCapturedVariableExpression",

    AccessScratchSingleValueExpression = "AccessScratchSingleValueExpression",
    AccessScratchIndexExpression = "AccessScratchIndexExpression",

    LoadIndexExpression = "LoadIndexExpression",
    LoadPropertyExpression = "LoadPropertyExpression",
    LoadFieldExpression = "LoadFieldExpression",
    LoadFieldVirtualExpression = "LoadFieldVirtualExpression",

    ConstructorPrimaryDirectExpression = "ConstructorPrimaryDirectExpression",
    ConstructorPrimaryCheckExpression = "ConstructorPrimaryCheckExpression",
    ConstructorTupleExpression = "ConstructorTupleExpression",
    ConstructorRecordExpression = "ConstructorRecordExpression",

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

    LogicActionAndExpression = "LogicActionAndExpression",
    LogicActionOrExpression = "LogicActionOrExpression",

    PrefixNotExpression = "PrefixNotExpression",
    PrefixNegateExpression = "PrefixNegateExpression",

    BinAddExpression = "BinAddExpression",
    BinSubExpression = "BinSubExpression",
    BinMultExpression = "BinMultExpression",
    BinDivExpression = "BinDivExpression",

    BinKeyEqBothUniqueExpression = "BinKeyEqBothUniqueExpression",
    BinKeyEqOneUniqueExpression = "BinKeyEqOneUniqueExpression",
    BinKeyEqGeneralExpression = "BinKeyEqGeneralExpression",

    BinKeyNeqBothUniqueExpression = "BinKeyNeqBothUniqueExpression",
    BinKeyNeqOneUniqueExpression = "BinKeyNeqOneUniqueExpression",
    BinKeyNeqGeneralExpression = "BinKeyNeqGeneralExpression",

    BinKeyUniqueLessExpression = "BinKeyUniqueLessExpression",
    BinKeyGeneralLessExpression = "BinKeyGeneralLessExpression",

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
    TaskSelfControlExpression = "TaskSelfControlExpression",
    TaskGetIDExpression = "TaskGetIDExpression",

    CoerceSafeExpression = "CoerceSafeExpression",

    InjectExpression = "InjectExpression",
    ExtractExpression = "ExtractExpression",
    CreateCodePackExpression = "CreateCodePackExpression",

    IsNoneSpecialExpression = "IsNoneSpecialExpression",
    IsSomeSpecialExpression = "IsSomeSpecialExpression",
    IsNothingSpecialExpression = "IsNothingSpecialExpression",
    IsSomethingSpecialExpression = "IsSomethingSpecialExpression",
    IsOkSpecialExpression = "IsOkSpecialExpression",
    IsErrSpecialExpression = "IsErrSpecialExpression",

    IsEqualToLiteralExpression = "IsEqualToLiteralExpression",
    IsNotEqualToLiteralExpression = "IsNotEqualToLiteralExpression",
    IsTypeExpression = "IsTypeExpression",
    IsNotTypeExpression = "IsNotTypeExpression",
    IsSubTypeExpression = "IsSubTypeExpression",
    IsNotSubTypeExpression = "IsNotSubTypeExpression",

    AsNoneSpecialExpression = "AsNoneSpecialExpression",
    AsSomeSpecialExpression = "AsSomeSpecialExpression",
    AsNothingSpecialExpression = "AsNothingSpecialExpression",
    AsSomethingSpecialExpression = "AsSomethingSpecialExpression",
    AsOkSpecialExpression = "AsOkSpecialExpression",
    AsErrSpecialExpression = "AsErrSpecialExpression",

    AsEqualToLiteralExpression = "AsEqualToLiteralExpression",
    AsNotEqualToLiteralExpression = "AsNotEqualToLiteralExpression",
    AsTypeExpression = "AsTypeExpression",
    AsNotTypeExpression = "AsNotTypeExpression",
    AsSubTypeExpression = "AsSubTypeExpression",
    AsNotSubTypeExpression = "AsNotSubTypeExpression",

    CallMemberFunctionExpression = "CallMemberFunctionExpression",
    CallMemberFunctionDynamicExpression = "CallMemberFunctionDynamicExpression",
    CallMemberFunctionSelfRefExpression = "CallMemberFunctionSelfRefExpression",

    CallMemberFunctionTaskExpression = "CallMemberFunctionTaskExpression",
    CallMemberFunctionTaskSelfRefExpression = "CallMemberFunctionTaskSelfRefExpression",
    CallMemberActionExpression = "CallMemberActionExpression"
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

    static OverflowIsFailure: boolean = false;

    isFailableOperation(): boolean {
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
        super(TIRExpressionTag.LiteralRegexExpression, sinfo, "Regex", value.regexstr);
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

    isTaskOperation(): boolean {
        return true;
    }

    isFailableOperation(): boolean {
        return !this.orNoneMode;
    }
}

class TIRAccessNamespaceConstantExpression extends TIRExpression {
    readonly ns: string;
    readonly cname: string;

    constructor(sinfo: SourceInfo, ns: string, cname: string, decltype: TIRTypeKey) {
        super(TIRExpressionTag.AccessNamespaceConstantExpression, sinfo, decltype, `${ns}::${cname}`);
        this.ns = ns;
        this.cname = cname;
    }
}

class TIRAccessConstMemberFieldExpression extends TIRExpression {
    readonly tkey: TIRTypeKey;
    readonly cname: string;

    constructor(sinfo: SourceInfo, tkey: TIRTypeKey, cname: string, decltype: TIRTypeKey) {
        super(TIRExpressionTag.AccessConstMemberFieldExpression, sinfo, decltype, `${tkey}::${cname}`);
        this.tkey = tkey;
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

class TIRAccessCapturedVariableExpression extends TIRExpression {
    readonly name: string;

    constructor(sinfo: SourceInfo, name: string, etype: TIRTypeKey) {
        super(TIRExpressionTag.AccessCapturedVariableExpression, sinfo, etype, name);
        this.name = name;
    }

    getUsedVars(): string[] {
        return [this.name];
    }
}

class TIRAccessScratchSingleValueExpression extends TIRExpression {
    readonly sidx: number;

    constructor(sinfo: SourceInfo, etype: TIRTypeKey, sidx: number) {
        super(TIRExpressionTag.AccessScratchSingleValueExpression, sinfo, etype, `$$scratch<${sidx}, ${etype}>[]`);
        this.sidx = sidx;
    }
}

class TIRAccessScratchIndexExpression extends TIRExpression {
    readonly index: number;
    readonly sidx: number;

    constructor(sinfo: SourceInfo, index: number, etype: TIRTypeKey, sidx: number) {
        super(TIRExpressionTag.AccessScratchIndexExpression, sinfo, etype, `$$scratch<${sidx}, ${etype}>[${index}]`);
        this.index = index;
        this.sidx = sidx;
    }
}

//abstract class for load index/property/field/fieldvirtual
abstract class TIRLoadSingleExpression extends TIRExpression {
    readonly tkey: TIRTypeKey;
    readonly exp: TIRExpression;

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, tkey: TIRTypeKey, exp: TIRExpression, resultType: TIRTypeKey, exprstr: string) {
        super(tag, sinfo, resultType, exprstr);
        this.tkey = tkey;
        this.exp = exp;
    }

    isFailableOperation(): boolean {
        return this.exp.isFailableOperation();
    }

    getUsedVars(): string[] {
        return this.exp.getUsedVars();
    }
}

class TIRLoadIndexExpression extends TIRLoadSingleExpression {
    readonly index: number;

    constructor(sinfo: SourceInfo, exp: TIRExpression, tkey: TIRTypeKey, index: number, resultType: TIRTypeKey) {
        super(TIRExpressionTag.LoadIndexExpression, sinfo, tkey, exp, resultType, `${exp.expstr}.${index}`);
        this.index = index;
    }
} 

class TIRLoadPropertyExpression extends TIRLoadSingleExpression {
    readonly property: string;

    constructor(sinfo: SourceInfo, exp: TIRExpression, tkey: TIRTypeKey, property: string, resultType: TIRTypeKey) {
        super(TIRExpressionTag.LoadPropertyExpression, sinfo, tkey, exp, resultType, `${exp.expstr}.${property}`);
        this.property = property;
    }
}

class TIRLoadFieldExpression extends TIRLoadSingleExpression {
    readonly field: TIRFieldKey;

    constructor(sinfo: SourceInfo, tkey: TIRTypeKey, exp: TIRExpression, field: TIRFieldKey, resultType: TIRTypeKey) {
        super(TIRExpressionTag.LoadFieldExpression, sinfo, tkey, exp, resultType, `${exp.expstr}.${field}`);
        this.field = field;
    }
}

class TIRLoadFieldVirtualExpression extends TIRLoadSingleExpression {
    readonly field: TIRFieldKey;

    constructor(sinfo: SourceInfo, tkey: TIRTypeKey, exp: TIRExpression, field: TIRFieldKey, resultType: TIRTypeKey) {
        super(TIRExpressionTag.LoadFieldVirtualExpression, sinfo, tkey, exp, resultType, `${exp.expstr}.${field}`);
        this.field = field;
    }
}

//abstract class for constructor ops
abstract class TIRConstructorExpression extends TIRExpression {
    readonly oftype: TIRTypeKey;
    readonly args: TIRExpression[];

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, oftype: TIRTypeKey, args: TIRExpression[], exprstr: string) {
        super(tag, sinfo, oftype, exprstr);
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

class TIRConstructorPrimaryDirectExpression extends TIRConstructorExpression {
    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.ConstructorPrimaryDirectExpression, sinfo, oftype, args, `${oftype}{${args.map((arg) => arg.expstr).join(", ")}`);
    }
}

class TIRConstructorPrimaryCheckExpression extends TIRConstructorExpression {
    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.ConstructorPrimaryCheckExpression, sinfo, oftype, args, `${oftype}{${args.map((arg) => arg.expstr).join(", ")}`);
    }

    isFailableOperation(): boolean {
        return true;
    }
}

class TIRConstructorTupleExpression extends TIRConstructorExpression {
    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.ConstructorTupleExpression, sinfo, oftype, args, `[${args.map((arg) => arg.expstr).join(", ")}]`);
    }
}

class TIRConstructorRecordExpression extends TIRConstructorExpression {
    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.ConstructorRecordExpression, sinfo, oftype, args, `{${args.map((arg) => arg.expstr).join(", ")}}`);
    }
}

class TIRConstructorListExpression  extends TIRConstructorExpression {
    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.ConstructorListExpression, sinfo, oftype, args, `List{${args.map((arg) => arg.expstr).join(", ")}}`);
    }
}
    
class TIRConstructorMapExpression extends TIRConstructorExpression {
    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.ConstructorMapExpression, sinfo, oftype, args, `Map{${args.map((arg) => arg.expstr).join(", ")}}`);
    }

    isFailableOperation(): boolean {
        return true;
    }
}

class TIRCodePackInvokeExpression extends TIRExpression {
    readonly cpack: TIRCodePack;
    readonly packarg: {argn: string, iscapture: boolean};
    readonly args: TIRExpression[];

    constructor(sinfo: SourceInfo, etype: TIRTypeKey, cpack: TIRCodePack, packarg: {argn: string, iscapture: boolean}, args: TIRExpression[]) {
        super(TIRExpressionTag.CodePackInvokeExpression, sinfo, etype, `${cpack.invk}(${[packarg.argn, ...args.map((arg) => arg.expstr)].join(", ")})`);
        this.cpack = cpack;
        this.packarg = packarg;
        this.args = args;
    }

    isFailableOperation(): boolean {
        return this.args.some((arg) => arg.isFailableOperation());
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(...this.args.map((arg) => arg.getUsedVars()));
    }
}

//abstract class for single argument constructors
abstract class TIRConstructorOfExpression extends TIRExpression {
    readonly oftype: TIRTypeKey;
    readonly arg: TIRExpression;

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, oftype: TIRTypeKey, arg: TIRExpression, exprstr: string) {
        super(tag, sinfo, oftype, exprstr);
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

class TIRResultOkConstructorExpression extends TIRConstructorOfExpression {
    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, arg: TIRExpression) {
        super(TIRExpressionTag.ResultOkConstructorExpression, sinfo, oftype, arg, `cons_ok<${oftype}>{${arg.expstr}}`);
    }
}

class TIRResultErrConstructorExpression extends TIRConstructorOfExpression {
    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, arg: TIRExpression) {
        super(TIRExpressionTag.ResultErrConstructorExpression, sinfo, oftype, arg, `cons_err<${oftype}>{${arg.expstr}}`);
    }
}

class TIRSomethingConstructorExpression extends TIRConstructorOfExpression {
    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, arg: TIRExpression) {
        super(TIRExpressionTag.SomethingConstructorExpression, sinfo, oftype, arg, `cons_something<${oftype}>{${arg.expstr}}`);
    }
}

class TIRTypedeclDirectExpression extends TIRConstructorOfExpression {
    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, arg: TIRExpression) {
        super(TIRExpressionTag.TypedeclDirectExpression, sinfo, oftype, arg, `cons_typedecl<${oftype}>{${arg.expstr}}`);
    }
}

class TIRTypedeclConstructorExpression extends TIRConstructorOfExpression {
    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, arg: TIRExpression) {
        super(TIRExpressionTag.TypedeclConstructorExpression, sinfo, oftype, arg, `cons_typedecl<${oftype}>{${arg.expstr}}`);
    }

    isFailableOperation(): boolean {
        return true;
    }
}

//abstract for call to a static function with args
abstract class TIRCallFunctionExpression extends TIRExpression {
    readonly fkey: TIRInvokeKey;
    readonly args: TIRExpression[]; 

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, fkey: TIRInvokeKey, rtype: TIRTypeKey, args: TIRExpression[], exprstr: string) {
        super(tag, sinfo, rtype, exprstr);
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

class TIRCallNamespaceFunctionExpression extends TIRCallFunctionExpression {
    readonly ns: string;
    readonly fname: string;

    constructor(sinfo: SourceInfo, ns: string, fname: string, fkey: TIRInvokeKey, rtype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.CallNamespaceFunctionExpression, sinfo, fkey, rtype, args, `${fkey}(${args.map((arg) => arg.expstr).join(", ")})`);
        this.ns = ns;
        this.fname = fname;
    }
}

class TIRCallNamespaceOperatorExpression extends TIRCallFunctionExpression {
    readonly ns: string;
    readonly oname: string;

    constructor(sinfo: SourceInfo, ns: string, oname: string, declkey: TIRInvokeKey, rtype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.CallNamespaceOperatorExpression, sinfo, declkey, rtype, args, `${declkey}(${args.map((arg) => arg.expstr).join(", ")})`);
        this.ns = ns;
        this.oname = oname;
    }
}

class TIRCallStaticFunctionExpression extends TIRCallFunctionExpression {
    readonly tkey: TIRTypeKey;
    readonly fname: string;

    constructor(sinfo: SourceInfo, tkey: TIRTypeKey, fname: string, fkey: TIRInvokeKey, rtype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.CallStaticFunctionExpression, sinfo, fkey, rtype, args, `${fkey}(${args.map((arg) => arg.expstr).join(", ")})`);
        this.tkey = tkey;
        this.fname = fname;
    }
}

//abstract class for logic actions
abstract class TIRLogicActionExpression extends TIRExpression {
    readonly args: TIRExpression[]; 

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, args: TIRExpression[], exprstr: string) {
        super(tag, sinfo, "Bool", exprstr);
        this.args = args;
    }

    isFailableOperation(): boolean {
        return this.args.some((arg) => arg.isFailableOperation());
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(...this.args.map((arg) => arg.getUsedVars()));
    }
}

class TIRLogicActionAndExpression extends TIRLogicActionExpression {
    constructor(sinfo: SourceInfo, args: TIRExpression[]) {
        super(TIRExpressionTag.LogicActionAndExpression, sinfo, args, `/\\(${args.map((arg) => arg.expstr).join(", ")})`);
    }
}

class TIRLogicActionOrExpression extends TIRLogicActionExpression {
    constructor(sinfo: SourceInfo, args: TIRExpression[]) {
        super(TIRExpressionTag.LogicActionOrExpression, sinfo, args, `\\/(${args.map((arg) => arg.expstr).join(", ")})`);
    }
}

//abstract class for unary expressions
abstract class TIRUnaryExpression extends TIRExpression {
    readonly exp: TIRExpression;

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, rtype: TIRTypeKey, exp: TIRExpression, exprstr: string) {
        super(tag, sinfo, rtype, exprstr);
        this.exp = exp;
    }

    isFailableOperation(): boolean {
        return this.exp.isFailableOperation();
    }

    getUsedVars(): string[] {
        return this.exp.getUsedVars();
    }
}

class TIRPrefixNotExpression extends TIRUnaryExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression) {
        super(TIRExpressionTag.PrefixNotExpression, sinfo, "Bool", exp, `!(${exp.expstr})`);
    }
}

class TIRPrefixNegateExpression extends TIRUnaryExpression {
    readonly optype: TIRTypeKey;

    constructor(sinfo: SourceInfo, exp: TIRExpression, exptype: TIRTypeKey, ntype: TIRTypeKey) {
        super(TIRExpressionTag.PrefixNegateExpression, sinfo, exptype, exp, `-(${exp.expstr})`);
        this.optype = ntype;
    }
}

//abstract class for binary operations
abstract class TIRBinOpExpression extends TIRExpression {
    readonly optype: TIRTypeKey;
    readonly lhs: TIRExpression;
    readonly rhs: TIRExpression;

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, exptype: TIRTypeKey, ntype: TIRTypeKey, exprstr: string) {
        super(tag, sinfo, exptype, exprstr);
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

class TIRBinAddExpression extends TIRBinOpExpression {
    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, exptype: TIRTypeKey, ntype: TIRTypeKey) {
        super(TIRExpressionTag.BinAddExpression, sinfo, lhs, rhs, exptype, ntype, `(${lhs.expstr} + ${rhs.expstr})`);
    }

    isFailableOperation(): boolean {
        if (TIRExpression.OverflowIsFailure && (this.optype === "Nat" || this.optype === "Int")) {
            return true;
        }
        
        return (this.lhs.isFailableOperation() || this.rhs.isFailableOperation());
    }
}

class TIRBinSubExpression extends TIRBinOpExpression {
    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, exptype: TIRTypeKey, ntype: TIRTypeKey) {
        super(TIRExpressionTag.BinSubExpression, sinfo, lhs, rhs, exptype, ntype, `(${lhs.expstr} - ${rhs.expstr})`);
    }

    isFailableOperation(): boolean {
        if(TIRExpression.OverflowIsFailure && (this.optype === "Nat" || this.optype === "Int")) {
            return true;
        }

        //unsigned underflow is a more dangerous issue that just overflows
        if(this.optype === "Nat" || this.optype === "BigNat") {
            return true;
        }

        return (this.lhs.isFailableOperation() || this.rhs.isFailableOperation());
    }
}

class TIRBinMultExpression extends TIRBinOpExpression {
    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, exptype: TIRTypeKey, ntype: TIRTypeKey) {
        super(TIRExpressionTag.BinMultExpression, sinfo, lhs, rhs, exptype, ntype, `(${lhs.expstr} * ${rhs.expstr})`);
    }

    isFailableOperation(): boolean {
        if(TIRExpression.OverflowIsFailure && (this.optype === "Nat" || this.optype === "Int")) {
            return true;
        }

        return (this.lhs.isFailableOperation() || this.rhs.isFailableOperation());
    }
}

class TIRBinDivExpression extends TIRBinOpExpression {
    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, exptype: TIRTypeKey, ntype: TIRTypeKey) {
        super(TIRExpressionTag.BinDivExpression, sinfo, lhs, rhs, exptype, ntype, `(${lhs.expstr} / ${rhs.expstr})`);
    }

    isFailableOperation(): boolean {
        return true; //div 0
    }
}

class TIRBinKeyEqBothUniqueExpression extends TIRExpression {
    readonly optype: TIRTypeKey; //both must be the same unique key type
    readonly lhs: TIRExpression;
    readonly rhs: TIRExpression;

    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, optype: TIRTypeKey) {
        super(TIRExpressionTag.BinKeyEqBothUniqueExpression, sinfo, "Bool", `KeyType::ueq<${optype}>(${lhs.expstr}, ${rhs.expstr})`);
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

class TIRBinKeyEqOneUniqueExpression extends TIRExpression {
    readonly oftype: TIRTypeKey; //the unique key type
    readonly uarg: TIRExpression; //the value that has the unique type

    readonly gtype: TIRTypeKey; //The type of the non-unique value
    readonly garg: TIRExpression; //The arg that has the non-unique type

    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, uarg: TIRExpression, gtype: TIRTypeKey, garg: TIRExpression) {
        super(TIRExpressionTag.BinKeyEqOneUniqueExpression, sinfo, "Bool", `KeyType::seq<${oftype}, ${gtype}>(${uarg.expstr}, ${garg.expstr})`);
        this.oftype = oftype;
        this.uarg = uarg;

        this.gtype = gtype;
        this.garg = garg;
    }

    isFailableOperation(): boolean {
        return this.uarg.isFailableOperation() || this.garg.isFailableOperation();
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(this.uarg.getUsedVars(), this.garg.getUsedVars());
    }
}

class TIRBinKeyEqGeneralExpression extends TIRExpression {
    readonly lhstype: TIRTypeKey;
    readonly lhs: TIRExpression;

    readonly rhstype: TIRTypeKey;
    readonly rhs: TIRExpression;

    constructor(sinfo: SourceInfo, lhstype: TIRTypeKey, lhs: TIRExpression, rhstype: TIRTypeKey, rhs: TIRExpression) {
        super(TIRExpressionTag.BinKeyEqGeneralExpression, sinfo, "Bool", `KeyType::geq<${lhstype}, ${rhstype}>(${lhs.expstr}, ${rhs.expstr})`);
        this.lhstype = lhstype;
        this.lhs = lhs;

        this.rhstype = rhstype;
        this.rhs = rhs;
    }

    isFailableOperation(): boolean {
        return this.lhs.isFailableOperation() || this.rhs.isFailableOperation();
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(this.lhs.getUsedVars(), this.rhs.getUsedVars());
    }
}

class TIRBinKeyNeqBothUniqueExpression extends TIRExpression {
    readonly optype: TIRTypeKey; //both must be the same unique key type
    readonly lhs: TIRExpression;
    readonly rhs: TIRExpression;

    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, optype: TIRTypeKey) {
        super(TIRExpressionTag.BinKeyNeqBothUniqueExpression, sinfo, "Bool", `KeyType::uneq<${optype}>(${lhs.expstr}, ${rhs.expstr})`);
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

class TIRBinKeyNeqOneUniqueExpression extends TIRExpression {
    readonly oftype: TIRTypeKey; //the unique key type
    readonly uarg: TIRExpression; //the value that has the unique type

    readonly gtype: TIRTypeKey; //The type of the non-unique value
    readonly garg: TIRExpression; //The arg that has the non-unique type

    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, uarg: TIRExpression, gtype: TIRTypeKey, garg: TIRExpression) {
        super(TIRExpressionTag.BinKeyNeqOneUniqueExpression, sinfo, "Bool", `KeyType::sneq<${oftype}, ${gtype}>(${uarg.expstr}, ${garg.expstr})`);
        this.oftype = oftype;
        this.uarg = uarg;

        this.gtype = gtype;
        this.garg = garg;
    }

    isFailableOperation(): boolean {
        return this.uarg.isFailableOperation() || this.garg.isFailableOperation();
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(this.uarg.getUsedVars(), this.garg.getUsedVars());
    }
}

class TIRBinKeyNeqGeneralExpression extends TIRExpression {
    readonly lhstype: TIRTypeKey;
    readonly lhs: TIRExpression;

    readonly rhstype: TIRTypeKey;
    readonly rhs: TIRExpression;

    constructor(sinfo: SourceInfo, lhstype: TIRTypeKey, lhs: TIRExpression, rhstype: TIRTypeKey, rhs: TIRExpression) {
        super(TIRExpressionTag.BinKeyNeqGeneralExpression, sinfo, "Bool", `KeyType::gneq<${lhstype}, ${rhstype}>(${lhs.expstr}, ${rhs.expstr})`);
        this.lhstype = lhstype;
        this.lhs = lhs;

        this.rhstype = rhstype;
        this.rhs = rhs;
    }

    isFailableOperation(): boolean {
        return this.lhs.isFailableOperation() || this.rhs.isFailableOperation();
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(this.lhs.getUsedVars(), this.rhs.getUsedVars());
    }
}

class TIRBinKeyUniqueLessExpression extends TIRExpression {
    readonly optype: TIRTypeKey;
    readonly lhs: TIRExpression;
    readonly rhs: TIRExpression;

    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, optype: TIRTypeKey) {
        super(TIRExpressionTag.BinKeyUniqueLessExpression, sinfo, "Bool", `KeyType::uless<${optype}>(${lhs.expstr}, ${rhs.expstr})`);
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

class TIRBinKeyGeneralLessExpression extends TIRExpression {
    readonly optype: TIRTypeKey;
    readonly lhs: TIRExpression;
    readonly rhs: TIRExpression;

    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, optype: TIRTypeKey) {
        super(TIRExpressionTag.BinKeyGeneralLessExpression, sinfo, "Bool", `KeyType::gless<${optype}>(${lhs.expstr}, ${rhs.expstr})`);
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

//abstract class for numeric compare ops
abstract class TIRNumericBinCmpExpression extends TIRExpression {
    readonly optype: TIRTypeKey;
    readonly lhs: TIRExpression;
    readonly rhs: TIRExpression;

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, ntype: TIRTypeKey, exprstr: string) {
        super(tag, sinfo, "Bool", exprstr);
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

class TIRNumericEqExpression extends TIRNumericBinCmpExpression {
    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, ntype: TIRTypeKey) {
        super(TIRExpressionTag.NumericEqExpression, sinfo, lhs, rhs, ntype, `(${lhs.expstr} == ${rhs.expstr})`);
    }
}

class TIRNumericNeqExpression extends TIRNumericBinCmpExpression {
    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, ntype: TIRTypeKey) {
        super(TIRExpressionTag.NumericNeqExpression, sinfo, lhs, rhs, ntype, `(${lhs.expstr} != ${rhs.expstr})`);
    }
}

class TIRNumericLessExpression extends TIRNumericBinCmpExpression {
    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, ntype: TIRTypeKey) {
        super(TIRExpressionTag.NumericLessExpression, sinfo, lhs, rhs, ntype, `(${lhs.expstr} < ${rhs.expstr})`);
    }
}

class TIRNumericLessEqExpression extends TIRNumericBinCmpExpression {
    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, ntype: TIRTypeKey) {
        super(TIRExpressionTag.NumericLessEqExpression, sinfo, lhs, rhs, ntype, `(${lhs.expstr} <= ${rhs.expstr})`);
    }
}

class TIRNumericGreaterExpression extends TIRNumericBinCmpExpression {
    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, ntype: TIRTypeKey) {
        super(TIRExpressionTag.NumericGreaterExpression, sinfo, lhs, rhs, ntype, `(${lhs.expstr} > ${rhs.expstr})`);
    }
}

class TIRNumericGreaterEqExpression extends TIRNumericBinCmpExpression {
    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, ntype: TIRTypeKey) {
        super(TIRExpressionTag.NumericGreaterEqExpression, sinfo, lhs, rhs, ntype, `(${lhs.expstr} >= ${rhs.expstr})`);
    }
}

//abstract binlogic ops
abstract class TIRBinLogicExpression extends TIRExpression {
    readonly lhs: TIRExpression;
    readonly rhs: TIRExpression;

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, exprstr: string) {
        super(tag, sinfo, "Bool", exprstr);
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

class TIRBinLogicAndExpression extends TIRBinLogicExpression {
    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression) {
        super(TIRExpressionTag.BinLogicAndExpression, sinfo, lhs, rhs, `(${lhs.expstr} && ${rhs.expstr})`);
    }
}

class TIRBinLogicOrExpression extends TIRBinLogicExpression {
    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression) {
        super(TIRExpressionTag.BinLogicOrExpression, sinfo, lhs, rhs, `(${lhs.expstr} || ${rhs.expstr})`);
    }
}

class TIRBinLogicImpliesExpression extends TIRBinLogicExpression {
    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression) {
        super(TIRExpressionTag.BinLogicImpliesExpression, sinfo, lhs, rhs, `(${lhs.expstr} ==> ${rhs.expstr})`);
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
    readonly clauses: {match: TIRExpression, litval: TIRLiteralValue, value: TIRExpression}[];
    readonly edefault: TIRExpression | undefined;
    readonly isexhaustive: boolean;

    constructor(sinfo: SourceInfo, etype: TIRTypeKey, exp: TIRExpression, clauses: {match: TIRExpression, litval: TIRLiteralValue, value: TIRExpression}[], edefault: TIRExpression | undefined, isexhaustive: boolean) {
        super(TIRExpressionTag.SwitchExpression, sinfo, etype, `switch(${exp.expstr}) ${clauses.map((ci) => `(${ci.litval.litstr} => ${ci.value.expstr})`)}${edefault !== undefined ? "(_ => " + edefault.expstr : ""}`);
        this.exp = exp;
        this.clauses = clauses;
        this.edefault = edefault;
        this.isexhaustive = isexhaustive;
    }

    isFailableOperation(): boolean {
        return this.exp.isFailableOperation() || 
            this.clauses.some((cc) => cc.match.isFailableOperation() || cc.value.isFailableOperation()) ||
            (this.edefault !== undefined && this.edefault.isFailableOperation()) ||
            !this.isexhaustive;
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(
            this.exp.getUsedVars(),
            ...this.clauses.map((ci) => ci.match.getUsedVars()), ...this.clauses.map((ci) => ci.value.getUsedVars()),
            (this.edefault !== undefined ? this.edefault.getUsedVars() : [])
        );
    }
}

class TIRMatchExpression extends TIRExpression {
    readonly exp: TIRExpression;
    readonly clauses: {match: TIRExpression, mtype: TIRTypeKey, value: TIRExpression}[];
    readonly edefault: TIRExpression | undefined;
    readonly isexhaustive: boolean;

    constructor(sinfo: SourceInfo, etype: TIRTypeKey, exp: TIRExpression, clauses: {match: TIRExpression, mtype: TIRTypeKey, value: TIRExpression}[], edefault: TIRExpression | undefined, isexhaustive: boolean) {
        super(TIRExpressionTag.MatchExpression, sinfo, etype, `match(${exp.expstr}) ${clauses.map((ci) => `(${ci.mtype} => ${ci.value.expstr})`)}${edefault !== undefined ? "(_ => " + edefault.expstr : ""}`);
        this.exp = exp;
        this.clauses = clauses;
        this.edefault = edefault;
        this.isexhaustive = isexhaustive;
    }

    isFailableOperation(): boolean {
        return this.exp.isFailableOperation() || 
            this.clauses.some((cc) => cc.match.isFailableOperation()) ||
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
    readonly tasktype: TIRTypeKey;
    readonly field: TIRFieldKey;
    readonly fname: string;

    constructor(sinfo: SourceInfo, tasktype: TIRTypeKey, field: TIRFieldKey, fname: string, resultType: TIRTypeKey) {
        super(TIRExpressionTag.TaskSelfFieldExpression, sinfo, resultType, `self.${fname}`);
        this.tasktype = tasktype;
        this.field = field;
        this.fname = fname;
    }

    getUsedVars(): string[] {
        return [`self`];
    }
}

class TIRTaskSelfControlExpression extends TIRExpression {
    readonly tasktype: TIRTypeKey;

    constructor(sinfo: SourceInfo, tasktype: TIRTypeKey, resultType: TIRTypeKey) {
        super(TIRExpressionTag.TaskSelfControlExpression, sinfo, resultType, `self.cntl`);
        this.tasktype = tasktype;
    }

    getUsedVars(): string[] {
        return [`self`];
    }
}

class TIRTaskGetIDExpression extends TIRExpression {
    readonly tasktype: TIRTypeKey;

    constructor(sinfo: SourceInfo, tasktype: TIRTypeKey, resultType: TIRTypeKey) {
        super(TIRExpressionTag.TaskGetIDExpression, sinfo, resultType, `getTaskID`);
        this.tasktype = tasktype;
    }

    getUsedVars(): string[] {
        return ["self"];
    }
}

//abstract class for coerce ops that do a single value (maybe a ref or task return too)
abstract class TIRCoerceSafeSingleExpression extends TIRExpression {
    readonly exp: TIRExpression;
    readonly fromtype: TIRTypeKey
    readonly totype: TIRTypeKey;
    
    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, exp: TIRExpression, fromtype: TIRTypeKey, totype: TIRTypeKey, exprstr: string) {
        super(tag, sinfo, totype, exprstr);
        this.exp = exp;
        this.fromtype = fromtype;
        this.totype = totype;
    }

    isFailableOperation(): boolean {
        return this.exp.isFailableOperation();
    }
    
    getUsedVars(): string[] {
        return this.exp.getUsedVars();
    }
}

class TIRCoerceSafeExpression extends TIRCoerceSafeSingleExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, fromtype: TIRTypeKey, totype: TIRTypeKey) {
        super(TIRExpressionTag.CoerceSafeExpression, sinfo, exp, fromtype, totype, `coerce_safe<${totype}>(${exp.expstr})`);
    }
}

//abstract inject/extract op
abstract class TIRInjectExtractExpression extends TIRExpression {
    readonly exp: TIRExpression;
    readonly totype: TIRTypeKey;
    
    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, exp: TIRExpression, totype: TIRTypeKey, exprstr: string) {
        super(tag, sinfo, totype, exprstr);
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

class TIRInjectExpression extends TIRInjectExtractExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, totype: TIRTypeKey) {
        super(TIRExpressionTag.InjectExpression, sinfo, exp, totype, `inject<${totype}>(${exp.expstr})`);
    }
}

class TIRExtractExpression extends TIRInjectExtractExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, totype: TIRTypeKey) {
        super(TIRExpressionTag.ExtractExpression, sinfo, exp, totype, `extract<${totype}>(${exp.expstr})`);
    }
}

class TIRCreateCodePackExpression extends TIRExpression {
    readonly pcodepack: TIRCodePack;

    readonly capturedirect: string[];
    readonly captureindirect: string[];
    readonly capturepackdirect: string[];
    readonly capturepackindirect: string[];

    constructor(sinfo: SourceInfo, pcodepack: TIRCodePack, cptype: TIRTypeKey, capturedirect: string[], captureindirect: string[], capturepackdirect: string[], capturepackindirect: string[]) {
        super(TIRExpressionTag.CreateCodePackExpression, sinfo, cptype, `create_pack<${cptype}>(${[...capturedirect, ...captureindirect, ...capturepackdirect, ...capturepackindirect].join(", ")})`);
        this.pcodepack = pcodepack;
        this.capturedirect = capturedirect;
        this.captureindirect = captureindirect;
        this.capturepackdirect = capturepackdirect;
        this.capturepackindirect = capturepackindirect;
    }
}

//abstract class for is test operations
abstract class TIRTestIsExpression extends TIRExpression {
    readonly exp: TIRExpression;

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, exp: TIRExpression, exprstr: string) {
        super(tag, sinfo, "Bool", exprstr);
        this.exp = exp;
    }

    isFailableOperation(): boolean {
        return this.exp.isFailableOperation();
    }

    getUsedVars(): string[] {
        return this.exp.getUsedVars();
    }
}

//abstract class for is special test operations
abstract class TIRITestIsSpecialExpression extends TIRTestIsExpression {
    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, exp: TIRExpression, exprstr: string) {
        super(tag, sinfo, exp, exprstr);
    }
}

class TIRIsNoneSpecialExpression extends TIRITestIsSpecialExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression) {
        super(TIRExpressionTag.IsNoneSpecialExpression, sinfo, exp, `${exp.expstr}?none`);
    }
} 

class TIRIsSomeSpecialExpression extends TIRITestIsSpecialExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression) {
        super(TIRExpressionTag.IsSomeSpecialExpression, sinfo, exp, `${exp.expstr}?!none`);
    }
}

class TIRIsNothingSpecialExpression extends TIRITestIsSpecialExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression) {
        super(TIRExpressionTag.IsNothingSpecialExpression, sinfo, exp, `${exp.expstr}?nothing`);
    }
}

class TIRIsSomethingSpecialExpression extends TIRITestIsSpecialExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression) {
        super(TIRExpressionTag.IsSomethingSpecialExpression, sinfo, exp, `${exp.expstr}?something`);
    }
}

class TIRIsOkSpecialExpression  extends TIRITestIsSpecialExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression) {
        super(TIRExpressionTag.IsOkSpecialExpression, sinfo, exp, `${exp.expstr}?ok`);
    }
}

class TIRIsErrSpecialExpression extends TIRITestIsSpecialExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression) {
        super(TIRExpressionTag.IsErrSpecialExpression, sinfo, exp, `${exp.expstr}?err`);
    }
}

//abstract class for is literal compare operations
abstract class TIRITestIsLiteralEqExpression extends TIRTestIsExpression {
    readonly literal: TIRLiteralValue;

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, exp: TIRExpression, literal: TIRLiteralValue, exprstr: string) {
        super(tag, sinfo, exp, exprstr);
        this.literal = literal;
    }
}

class TIRIsEqualToLiteralExpression extends TIRITestIsLiteralEqExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, literal: TIRLiteralValue) {
        super(TIRExpressionTag.IsEqualToLiteralExpression, sinfo, exp, literal, `${exp.expstr}?[${literal.litstr}]`);
    }
}

class TIRIsNotEqualToLiteralExpression extends TIRITestIsLiteralEqExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, literal: TIRLiteralValue) {
        super(TIRExpressionTag.IsNotEqualToLiteralExpression, sinfo, exp, literal, `${exp.expstr}?[!${literal.litstr}]`);
    }
}

//abstract class for is type compare operations
abstract class TIRITestIsTypeExpression extends TIRTestIsExpression {
    readonly ttype: TIRTypeKey;

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, exp: TIRExpression, ttype: TIRTypeKey, exprstr: string) {
        super(tag, sinfo, exp, exprstr);
        this.ttype = ttype;
    }
}

class TIRIsTypeExpression extends TIRITestIsTypeExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, ttype: TIRTypeKey) {
        super(TIRExpressionTag.IsTypeExpression, sinfo, exp, ttype, `${exp.expstr}?<${ttype}>`);
    }
}

class TIRIsNotTypeExpression  extends TIRITestIsTypeExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, ttype: TIRTypeKey) {
        super(TIRExpressionTag.IsNotTypeExpression, sinfo, exp, ttype, `${exp.expstr}?<!${ttype}>`);
    }
}

class TIRIsSubTypeExpression  extends TIRITestIsTypeExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, ttype: TIRTypeKey) {
        super(TIRExpressionTag.IsSubTypeExpression, sinfo, exp, ttype, `${exp.expstr}?<<:${ttype}>`);
    }
}

class TIRIsNotSubTypeExpression  extends TIRITestIsTypeExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, ttype: TIRTypeKey) {
        super(TIRExpressionTag.IsNotSubTypeExpression, sinfo, exp, ttype, `${exp.expstr}?<!<:${ttype}>`);
    }
}

//abstract class for as expressions
abstract class TIRAsExpression extends TIRExpression {
    readonly exp: TIRExpression;
    
    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, exp: TIRExpression, oftype: TIRTypeKey, exprstr: string) {
        super(tag, sinfo, oftype, exprstr);
        this.exp = exp;
    }
    
    isFailableOperation(): boolean {
        return true;
    }

    getUsedVars(): string[] {
        return this.exp.getUsedVars();
    }
}

//abstract class for is special test operations
abstract class TIRAsSpecialExpression extends TIRAsExpression {
    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, exp: TIRExpression, oftype: TIRTypeKey, exprstr: string) {
        super(tag, sinfo, exp, oftype, exprstr);
    }
}

class TIRAsNoneSpecialExpression extends TIRAsSpecialExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression) {
        super(TIRExpressionTag.AsNoneSpecialExpression, sinfo, exp, "None", `${exp.expstr}@none`);
    }
}

class TIRAsSomeSpecialExpression extends TIRAsSpecialExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, oftype: TIRTypeKey) {
        super(TIRExpressionTag.AsSomeSpecialExpression, sinfo, exp, oftype, `${exp.expstr}@!none`);
    }
}

class TIRAsNothingSpecialExpression extends TIRAsSpecialExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression) {
        super(TIRExpressionTag.AsNothingSpecialExpression, sinfo, exp, "Nothing", `${exp.expstr}@nothing`);
    }
}

class TIRAsSomethingSpecialExpression extends TIRAsSpecialExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, oftype: TIRTypeKey) {
        super(TIRExpressionTag.AsSomethingSpecialExpression, sinfo, exp, oftype, `${exp.expstr}@something`);
    }
}

class TIRAsOkSpecialExpression extends TIRAsSpecialExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, oftype: TIRTypeKey) {
        super(TIRExpressionTag.AsOkSpecialExpression, sinfo, exp, oftype, `${exp.expstr}@ok`);
    }
}

class TIRAsErrSpecialExpression extends TIRAsSpecialExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, oftype: TIRTypeKey) {
        super(TIRExpressionTag.AsErrSpecialExpression, sinfo, exp, oftype, `${exp.expstr}@err`);
    }
}

//abstract class for is literal as operations
abstract class TIRIAsLiteralEqExpression extends TIRAsExpression {
    readonly literal: TIRLiteralValue;

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, exp: TIRExpression, literal: TIRLiteralValue, oftype: TIRTypeKey, exprstr: string) {
        super(tag, sinfo, exp, oftype, exprstr);
        this.literal = literal;
    }
}

class TIRAsEqualToLiteralExpression extends TIRIAsLiteralEqExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, literal: TIRLiteralValue, oftype: TIRTypeKey) {
        super(TIRExpressionTag.AsEqualToLiteralExpression, sinfo, exp, literal, oftype, `${exp.expstr}@[${literal.litstr}]`);
    }
}

class TIRAsNotEqualToLiteralExpression extends TIRIAsLiteralEqExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, literal: TIRLiteralValue, oftype: TIRTypeKey) {
        super(TIRExpressionTag.AsNotEqualToLiteralExpression, sinfo, exp, literal, oftype, `${exp.expstr}@[!${literal.litstr}]`);
    }
}

//abstract class for is type as operations
abstract class TIRITestAsTypeExpression extends TIRAsExpression {
    readonly ttype: TIRTypeKey;

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, exp: TIRExpression, ttype: TIRTypeKey, oftype: TIRTypeKey, exprstr: string) {
        super(tag, sinfo, exp, oftype, exprstr);
        this.ttype = ttype;
    }
}

class TIRAsTypeExpression extends TIRITestAsTypeExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, ttype: TIRTypeKey, oftype: TIRTypeKey) {
        super(TIRExpressionTag.AsTypeExpression, sinfo, exp, ttype, oftype, `${exp.expstr}@<${ttype}>`);
    }
}

class TIRAsNotTypeExpression extends TIRITestAsTypeExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, ttype: TIRTypeKey, oftype: TIRTypeKey) {
        super(TIRExpressionTag.AsNotTypeExpression, sinfo, exp, ttype, oftype, `${exp.expstr}@<!${ttype}>`);
    }
}

class TIRAsSubTypeExpression extends TIRITestAsTypeExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, ttype: TIRTypeKey, oftype: TIRTypeKey) {
        super(TIRExpressionTag.AsSubTypeExpression, sinfo, exp, ttype, oftype, `${exp.expstr}@<<:${ttype}>`);
    }
}

class TIRAsNotSubTypeExpression extends TIRITestAsTypeExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, ttype: TIRTypeKey, oftype: TIRTypeKey) {
        super(TIRExpressionTag.AsNotSubTypeExpression, sinfo, exp, ttype, oftype, `${exp.expstr}@<!<:${ttype}>`);
    }
}

//abstract class for member function calls
abstract class TIRIMemberFunctionExpression extends TIRExpression {
    readonly tkey: TIRTypeKey;
    readonly fname: string;
    readonly fkey: TIRInvokeKey;
    readonly thisarg: TIRExpression;
    readonly args: TIRExpression[]; 

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, tkey: TIRTypeKey, fname: string, fkey: TIRInvokeKey, rtype: TIRTypeKey, thisarg: TIRExpression, args: TIRExpression[], exprstr: string) {
        super(tag, sinfo, rtype, exprstr);
        this.tkey = tkey;
        this.fname = fname;
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

class TIRCallMemberFunctionExpression extends TIRIMemberFunctionExpression {
    constructor(sinfo: SourceInfo, tkey: TIRTypeKey, fname: string, fkey: TIRInvokeKey, rtype: TIRTypeKey, thisarg: TIRExpression, args: TIRExpression[]) {
        super(TIRExpressionTag.CallMemberFunctionExpression, sinfo, tkey, fname, fkey, rtype, thisarg, args, `${thisarg.expstr}.${fkey}(${args.map((arg) => arg.expstr).join(", ")})`);
    }
}

class TIRCallMemberFunctionDynamicExpression extends TIRIMemberFunctionExpression {
    readonly inferthistype: TIRTypeKey;
    readonly inferfkey: TIRInvokeKey | undefined;
    
    constructor(sinfo: SourceInfo, tkey: TIRTypeKey, fname: string, declkey: TIRInvokeKey, inferthistype: TIRTypeKey, inferfkey: TIRInvokeKey | undefined, rtype: TIRTypeKey, thisarg: TIRExpression, args: TIRExpression[]) {
        super(TIRExpressionTag.CallMemberFunctionDynamicExpression, sinfo, tkey, fname, declkey, rtype, thisarg, args, `${thisarg.expstr}.${declkey}(${args.map((arg) => arg.expstr).join(", ")})`);
        this.inferthistype = inferthistype;
        this.inferfkey = inferfkey;
    }
}

class TIRCallMemberFunctionSelfRefExpression extends TIRIMemberFunctionExpression {
    readonly thisref: string;

    constructor(sinfo: SourceInfo, tkey: TIRTypeKey, fname: string, fkey: TIRInvokeKey, rtype: TIRTypeKey, thisref: string, thisarg: TIRExpression, args: TIRExpression[]) {
        super(TIRExpressionTag.CallMemberFunctionSelfRefExpression, sinfo, tkey, fname, fkey, rtype, thisarg, args, `ref ${thisref}.${fkey}(${args.map((arg) => arg.expstr).join(", ")})`);
        this.thisref = thisref;
    }
}

//abstract class for task ops
abstract class TIRFunctionTaskExpression extends TIRExpression {
    readonly fname: string;
    readonly fkey: TIRInvokeKey;
    readonly tsktype: TIRTypeKey;
    readonly args: TIRExpression[]; 

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, fname: string, fkey: TIRInvokeKey, rtype: TIRTypeKey, tsktype: TIRTypeKey, args: TIRExpression[], exprstr: string) {
        super(tag, sinfo, rtype, exprstr);
        this.fname = fname;
        this.fkey = fkey;
        this.tsktype = tsktype;
        this.args = args;
    }

    isFailableOperation(): boolean {
        return this.args.some((arg) => arg.isFailableOperation());
    }

    getUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(["self"], ...this.args.map((arg) => arg.getUsedVars()));
    }
}

class TIRCallMemberFunctionTaskExpression extends TIRFunctionTaskExpression {
    constructor(sinfo: SourceInfo, fname: string, fkey: TIRInvokeKey, rtype: TIRTypeKey, tsktype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.CallMemberFunctionTaskExpression, sinfo, fname, fkey, rtype, tsktype, args, `self.${fkey}(${args.map((arg) => arg.expstr).join(", ")})`);
    }
}

class TIRCallMemberFunctionTaskSelfRefExpression extends TIRFunctionTaskExpression {
    constructor(sinfo: SourceInfo, fname: string, fkey: TIRInvokeKey, rtype: TIRTypeKey, tsktype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.CallMemberFunctionTaskSelfRefExpression, sinfo, fname, fkey, rtype, tsktype, args, `ref self.${fkey}(${args.map((arg) => arg.expstr).join(", ")})`);
    }
}

class TIRCallMemberActionExpression extends TIRFunctionTaskExpression {
    constructor(sinfo: SourceInfo, fname: string, fkey: TIRInvokeKey, rtype: TIRTypeKey, tsktype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.CallMemberActionExpression, sinfo, fname, fkey, rtype, tsktype, args, `self.${fkey}(${args.map((arg) => arg.expstr).join(", ")})`);
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
    VarAssignStatement = "VarAssignStatement",
    VarDeclareAndAssignStatement = "VarDeclareAndAssignStatement",

    CallWRefStatement = "CallWRefStatememt",

    VariableRetypeStatement = "VariableRetypeStatement",
    VariableSCRetypeStatement = "VariableSCRetypeStatement",
    ExpressionSCReturnDefineAndAssignStatement = "ExpressionSCReturnDefineAndAssignStatement",
    ExpressionSCReturnAssignStatement = "ExpressionSCReturnAssignStatement",

    ReturnStatement = "ReturnStatement",
    ReturnStatementWRef = "ReturnStatementWRef",
    ReturnStatementWTaskRef = "ReturnStatementWTaskRef",
    ReturnStatementWAction = "ReturnStatementWAction",

    IfStatement = "IfStatement",
    SwitchStatement = "SwitchStatement",
    MatchStatement = "MatchStatement",

    EnvironmentFreshStatement = "EnvironmentFreshStatement",
    EnvironmentSetStatement = "EnvironmentSetStatement",
    EnvironmentSetStatementBracket = "EnvironmentSetStatementBracket",

    TaskRunStatement = "TaskRunStatement", //run single task
    TaskMultiStatement = "TaskMultiStatement", //run multiple explicitly identified tasks -- complete all
    TaskDashStatement = "TaskDashStatement", //run multiple explicitly identified tasks -- first completion wins
    TaskAllStatement = "TaskAllStatement", //run the same task on all args in a list -- complete all
    TaskRaceStatement = "TaskRaceStatement", //run the same task on all args in a list -- first completion wins

    TaskSetSelfFieldStatement = "TaskSetSelfFieldStatement",

    LoggerEmitStatement = "LoggerEmitStatement",
    LoggerEmitConditionalStatement = "LoggerEmitConditionalStatement",
    LoggerSetPrefixStatement = "LoggerSetPrefixStatement"
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

    isFailableOperation(): boolean {
        return false;
    }

    getDirectlyUsedVars(): string[] {
        return [];
    }

    getDirectlyModVars(): string[] {
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
        return true;
    }

    getDirectlyUsedVars(): string[] {
        return this.cond.getUsedVars();
    }
}

class TIRDebugStatement extends TIRStatement {
    readonly value: TIRExpression;

    constructor(sinfo: SourceInfo, value: TIRExpression) {
        super(TIRStatementTag.DebugStatement, sinfo, `__debug(${value.expstr});`);
        this.value = value;
    }

    isFailableOperation(): boolean {
        return this.value.isFailableOperation();
    }

    getDirectlyUsedVars(): string[] {
        return this.value.getUsedVars();
    }
}

class TIRVarDeclareStatement extends TIRStatement {
    readonly vname: string;
    readonly vtype: TIRTypeKey;

    constructor(sinfo: SourceInfo, vname: string, vtype: TIRTypeKey) {
        super(TIRStatementTag.VarDeclareStatement, sinfo, `var ${vname}: ${vtype};`);
        this.vname = vname;
        this.vtype = vtype;
    }

    getDirectlyModVars(): string[] {
        return [this.vname];
    }
}

class TIRVarDeclareAndAssignStatement extends TIRStatement {
    readonly vname: string;
    readonly vtype: TIRTypeKey;
    readonly vexp: TIRExpression;
    readonly isConst: boolean;

    constructor(sinfo: SourceInfo, vname: string, vtype: TIRTypeKey, vexp: TIRExpression, isConst: boolean) {
        super(TIRStatementTag.VarAssignStatement, sinfo, `${isConst ? "let" : "var"} ${vname}: ${vtype} = ${vexp.expstr};`);
        this.vname = vname;
        this.vtype = vtype;
        this.vexp = vexp;
        this.isConst = isConst;
    }

    isFailableOperation(): boolean {
        return this.vexp.isFailableOperation();
    }

    getDirectlyUsedVars(): string[] {
        return this.vexp.getUsedVars();
    }

    getDirectlyModVars(): string[] {
        return [this.vname];
    }
}

class TIRVarAssignStatement extends TIRStatement {
    readonly vname: string;
    readonly vtype: TIRTypeKey;
    readonly vexp: TIRExpression;

    constructor(sinfo: SourceInfo, vname: string, vtype: TIRTypeKey, vexp: TIRExpression) {
        super(TIRStatementTag.VarDeclareAndAssignStatement, sinfo, `${vname} = ${vexp.expstr};`);
        this.vname = vname;
        this.vtype = vtype;
        this.vexp = vexp;
    }

    isFailableOperation(): boolean {
        return this.vexp.isFailableOperation();
    }

    getDirectlyUsedVars(): string[] {
        return this.vexp.getUsedVars();
    }

    getDirectlyModVars(): string[] {
        return [this.vname];
    }
}

class TIRCallWRefStatement extends TIRStatement {
    readonly vexp: TIRExpression;
    readonly restype: TIRTypeKey;
    readonly sidx: number;
    //always stores to scratch location as a EList

    constructor(sinfo: SourceInfo, vexp: TIRExpression, restype: TIRTypeKey, sidx: number) {
        super(TIRStatementTag.CallWRefStatement, sinfo, `${vexp.expstr};`);
        this.vexp = vexp;
        this.restype = restype;
        this.sidx = sidx;
    }

    isFailableOperation(): boolean {
        return this.vexp.isFailableOperation();
    }

    getDirectlyUsedVars(): string[] {
        return this.vexp.getUsedVars();
    }
}

class TIRVariableRetypeStatement extends TIRStatement {
    readonly vname: string;
    readonly origtype: TIRTypeKey;
    readonly newtype: TIRTypeKey;
    readonly asconv: TIRAsExpression

    constructor(sinfo: SourceInfo, vname: string, origtype: TIRTypeKey, newtype: TIRTypeKey, asconv: TIRAsExpression) {
        super(TIRStatementTag.VariableRetypeStatement, sinfo, `${vname} = ${asconv.expstr}`);
        this.vname = vname;
        this.origtype = origtype;
        this.newtype = newtype;
        this.asconv = asconv;
    }

    isFailableOperation(): boolean {
        return this.asconv.isFailableOperation();
    }

    getDirectlyModVars(): string[] {
        return [this.vname];
    }

    getDirectlyUsedVars(): string[] {
        return this.asconv.getUsedVars();
    }
}

class TIRVariableSCRetypeStatement extends TIRStatement {
    readonly vname: string;
    readonly origtype: TIRTypeKey;
    readonly test: TIRTestIsExpression;
    readonly asconv: TIRAsExpression;
    readonly resexp: TIRExpression;

    constructor(sinfo: SourceInfo, vname: string, origtype: TIRTypeKey, test: TIRTestIsExpression, asconv: TIRAsExpression, resexp: TIRExpression) {
        super(TIRStatementTag.VariableSCRetypeStatement, sinfo, `${vname} ?? ${test.expstr} -- ${vname} = safe ${asconv.expstr} : ${resexp.expstr}`);
        this.vname = vname;
        this.origtype = origtype;
        this.test = test;
        this.asconv = asconv;
        this.resexp = resexp;
    }

    isFailableOperation(): boolean {
        return this.test.isFailableOperation() || this.asconv.isFailableOperation() || this.resexp.isFailableOperation();
    }

    getDirectlyModVars(): string[] {
        return [this.vname];
    }

    getDirectlyUsedVars(): string[] {
        return TIRExpression.joinUsedVarInfo(this.asconv.getUsedVars(), this.asconv.getUsedVars(), this.resexp.getUsedVars());
    }
}

class TIRExpressionSCReturnDefineAndAssignStatement extends TIRStatement {
    //always implicitly reads from scratch location
    readonly vname: string;
    readonly vtype: TIRTypeKey;
    readonly isconst: boolean;
    
    readonly fromtype: TIRTypeKey;
    readonly test: TIRTestIsExpression | TIRExpression;
    readonly asconv: TIRExpression;
    readonly resexp: TIRExpression;

    readonly sidx: number;

    constructor(sinfo: SourceInfo, vname: string, vtype: TIRTypeKey, isconst: boolean, fromtype: TIRTypeKey, test: TIRTestIsExpression, asconv: TIRAsExpression, resexp: TIRExpression, sidx: number) {
        super(TIRStatementTag.ExpressionSCReturnDefineAndAssignStatement, sinfo, `${isconst ? "let" : "var"} ${vname}: ${vtype} = ${test.expstr} then safe ${asconv.expstr} : ${resexp.expstr}`);
        this.vname = vname;
        this.vtype = vtype;
        this.isconst = isconst;
        this.fromtype = fromtype;
        this.test = test;
        this.asconv = asconv;
        this.resexp = resexp;

        this.sidx = sidx;
    }
}

class TIRExpressionSCReturnAssignStatement extends TIRStatement {
    //always implicitly reads from scratch location
    readonly vname: string;
    readonly vtype: TIRTypeKey;
    
    readonly fromtype: TIRTypeKey;
    readonly test: TIRTestIsExpression | TIRExpression;
    readonly asconv: TIRExpression;
    readonly resexp: TIRExpression;

    readonly sidx: number;

    constructor(sinfo: SourceInfo, vname: string, vtype: TIRTypeKey, fromtype: TIRTypeKey, test: TIRTestIsExpression, asconv: TIRAsExpression, resexp: TIRExpression, sidx: number) {
        super(TIRStatementTag.ExpressionSCReturnAssignStatement, sinfo, `${vname} = ${test.expstr} then safe ${asconv.expstr} : ${resexp.expstr}`);
        this.vname = vname;
        this.vtype = vtype;
        this.fromtype = fromtype;
        this.test = test;
        this.asconv = asconv;
        this.resexp = resexp;

        this.sidx = sidx;
    }
}

class TIRReturnStatementGeneral extends TIRStatement {
    readonly value: TIRExpression;

    constructor(tag: TIRStatementTag, sinfo: SourceInfo, value: TIRExpression, stmtstr: string) {
        super(tag, sinfo, stmtstr);
        this.value = value;
    }

    isFailableOperation(): boolean {
        return this.value.isFailableOperation();
    }

    getDirectlyUsedVars(): string[] {
        return this.value.getUsedVars();
    }
}

class TIRReturnStatement extends TIRReturnStatementGeneral {
    constructor(sinfo: SourceInfo, value: TIRExpression) {
        super(TIRStatementTag.ReturnStatement, sinfo, value, `return ${value.expstr};`);
    }
}

class TIRReturnStatementWRef extends TIRReturnStatementGeneral {
    constructor(sinfo: SourceInfo, value: TIRExpression) {
        super(TIRStatementTag.ReturnStatementWRef, sinfo, value, `return ${value.expstr};`);
    }
}

class TIRReturnStatementWTaskRef extends TIRReturnStatementGeneral {
    constructor(sinfo: SourceInfo, value: TIRExpression) {
        super(TIRStatementTag.ReturnStatementWTaskRef, sinfo, value, `return ${value.expstr};`);
    }
}

class TIRReturnStatementWAction extends TIRReturnStatementGeneral {
    constructor(sinfo: SourceInfo, value: TIRExpression) {
        super(TIRStatementTag.ReturnStatementWAction, sinfo, value, `return ${value.expstr};`);
    }
}

class TIRIfStatement extends TIRStatement {
    readonly ifentry: {test: TIRExpression, value: TIRScopedBlockStatement};
    readonly elifentries: {test: TIRExpression, value: TIRScopedBlockStatement}[];
    readonly elseentry: TIRScopedBlockStatement;

    constructor(sinfo: SourceInfo, ifentry: {test: TIRExpression, value: TIRScopedBlockStatement}, elifentries: {test: TIRExpression, value: TIRScopedBlockStatement}[], elseentry: TIRScopedBlockStatement) {
        super(TIRStatementTag.IfStatement, sinfo, `if(${ifentry.test.expstr}) ${ifentry.value.stmtstr} ${elifentries.map((efi) => `elif(${efi.test.expstr}) ${efi.value.stmtstr}`)} else ${elseentry.stmtstr}`);
        this.ifentry = ifentry;
        this.elifentries = elifentries;
        this.elseentry = elseentry;
    }

    isFailableOperation(): boolean {
        return this.ifentry.test.isFailableOperation() || this.ifentry.value.isFailableOperation() ||
            this.elifentries.some((ee) => ee.test.isFailableOperation() || ee.value.isFailableOperation()) ||
            this.elseentry.isFailableOperation();
    }
}


class TIRSwitchStatement extends TIRStatement {
    readonly exp: TIRExpression;
    readonly clauses: {match: TIRExpression, litval: TIRLiteralValue, value: TIRScopedBlockStatement}[];
    readonly edefault: TIRScopedBlockStatement | undefined;
    readonly isexhaustive: boolean;

    constructor(sinfo: SourceInfo, exp: TIRExpression, clauses: {match: TIRExpression, litval: TIRLiteralValue, value: TIRScopedBlockStatement}[], edefault: TIRScopedBlockStatement | undefined, isexhaustive: boolean) {
        super(TIRStatementTag.SwitchStatement, sinfo, `switch(${exp.expstr}) ${clauses.map((ci) => `(${ci.litval.litstr} => ${ci.value.stmtstr})`)}${edefault !== undefined ? "(_ => " + edefault.stmtstr : ""}`);
        this.exp = exp;
        this.clauses = clauses;
        this.edefault = edefault;
        this.isexhaustive = isexhaustive;
    }

    isFailableOperation(): boolean {
        return this.exp.isFailableOperation() || 
            this.clauses.some((cc) => cc.match.isFailableOperation() || cc.value.isFailableOperation()) ||
            (this.edefault !== undefined && this.edefault.isFailableOperation()) ||
            !this.isexhaustive;
    }
}

class TIRMatchStatement extends TIRStatement {
    readonly exp: TIRExpression;
    readonly clauses: {match: TIRExpression, mtype: TIRTypeKey, value: TIRScopedBlockStatement}[];
    readonly edefault: TIRScopedBlockStatement | undefined;
    readonly isexhaustive: boolean;

    constructor(sinfo: SourceInfo, exp: TIRExpression, clauses: {match: TIRExpression, mtype: TIRTypeKey, value: TIRScopedBlockStatement}[], edefault: TIRScopedBlockStatement | undefined, isexhaustive: boolean) {
        super(TIRStatementTag.MatchStatement, sinfo, `match(${exp.expstr}) ${clauses.map((ci) => `(${ci.mtype} => ${ci.value.stmtstr})`)}${edefault !== undefined ? "(_ => " + edefault.stmtstr : ""}`);
        this.exp = exp;
        this.clauses = clauses;
        this.edefault = edefault;
        this.isexhaustive = isexhaustive;
    }

    isFailableOperation(): boolean {
        return this.exp.isFailableOperation() || 
            this.clauses.some((cc) => cc.match.isFailableOperation()) ||
            this.clauses.some((cc) => cc.value.isFailableOperation()) ||
            (this.edefault !== undefined && this.edefault.isFailableOperation()) ||
            !this.isexhaustive;
    }
}

class TIREnvironmentFreshStatement extends TIRStatement {
    readonly assigns: {keyname: string, valexp: [TIRTypeKey, TIRExpression]}[];

    constructor(sinfo: SourceInfo, assigns: {keyname: string, valexp: [TIRTypeKey, TIRExpression]}[]) {
        super(TIRStatementTag.EnvironmentFreshStatement, sinfo, `env{${assigns.map((asgn) => asgn.keyname + ": " + asgn.valexp[0] + "=" + asgn.valexp[1].expstr).join(", ")}};`);
        this.assigns = assigns;
    }

    isFailableOperation(): boolean {
        return this.assigns.some((asgn) => asgn.valexp[1].isFailableOperation());
    }
}

class TIREnvironmentSetStatement extends TIRStatement {
    readonly assigns: {keyname: string, valexp: [TIRTypeKey, TIRExpression] | undefined}[];

    constructor(sinfo: SourceInfo, assigns: {keyname: string, valexp: [TIRTypeKey, TIRExpression] | undefined}[]) {
        super(TIRStatementTag.EnvironmentFreshStatement, sinfo, `env[${assigns.map((asgn) => asgn.keyname + (asgn.valexp !== undefined ? (": " + asgn.valexp[0] + "=" + asgn.valexp[1].expstr) : "=_")).join(", ")}];`);
        this.assigns = assigns;
    }

    isFailableOperation(): boolean {
        return this.assigns.some((asgn) => (asgn.valexp !== undefined && asgn.valexp[1].isFailableOperation()));
    }
}

class TIREnvironmentSetStatementBracket extends TIRStatement {
    readonly assigns: {keyname: string, valexp: [TIRTypeKey, TIRExpression] | undefined}[];
    readonly block: TIRUnscopedBlockStatement | TIRScopedBlockStatement;
    readonly isFresh: boolean;

    constructor(sinfo: SourceInfo, assigns: {keyname: string, valexp: [TIRTypeKey, TIRExpression] | undefined}[], block: TIRUnscopedBlockStatement | TIRScopedBlockStatement, isFresh: boolean) {
        super(TIRStatementTag.EnvironmentFreshStatement, sinfo, `env${isFresh ? "{" : "["}${assigns.map((asgn) => asgn.keyname + (asgn.valexp !== undefined ? (": " + asgn.valexp[0] + "=" + asgn.valexp[1].expstr) : "=_")).join(", ")}${isFresh ? "}" : "]"} ${block.stmtstr}`);
        this.assigns = assigns;
        this.block = block;
        this.isFresh = isFresh;
    }

    isFailableOperation(): boolean {
        return this.assigns.some((asgn) => (asgn.valexp !== undefined && asgn.valexp[1].isFailableOperation())) || this.block.isFailableOperation();
    }
}

class TIRTaskExecStatment extends TIRStatement {
    readonly isdefine: boolean;
    readonly isconst: boolean;

    constructor(tag: TIRStatementTag, sinfo: SourceInfo, isdefine: boolean, isconst: boolean, stmtstr: string) {
        super(tag, sinfo, (isdefine ? (isconst ? "let " : "var ") : "") + stmtstr);
        this.isdefine= isdefine;
        this.isconst = isconst;
    }
}

class TIRTaskRunStatement extends TIRTaskExecStatment {
    readonly vtrgt: {name: string, vtype: TIRTypeKey};
    readonly task: TIRTypeKey;
    readonly taskargs: {argn: string, argv: TIRExpression}[];
    readonly consarg: {rarg: TIRExpression, rtype: TIRTypeKey};
    readonly args: TIRExpression[];

    constructor(sinfo: SourceInfo, isdefine: boolean, isconst: boolean, vtrgt: {name: string, vtype: TIRTypeKey}, task: TIRTypeKey, taskargs: {argn: string, argv: TIRExpression}[], consarg: {rarg: TIRExpression, rtype: TIRTypeKey}, args: TIRExpression[]) {
        super(TIRStatementTag.TaskRunStatement, sinfo, isdefine, isconst, `${vtrgt.name} = Task::run[${taskargs.map((ta) => ta.argn + "=" + ta.argv.expstr)}]<${task}>(${[consarg.rarg, ...args].map((aa) => aa.expstr).join(", ")}, ${args.map((arg) => arg.expstr).join(", ")})`);
        this.vtrgt = vtrgt;
        this.task = task;
        this.taskargs = taskargs;
        this.consarg = consarg;
        this.args = args;
    }

    isFailableOperation(): boolean {
        return this.args.some((aa) => aa.isFailableOperation()) || this.taskargs.some((aa) => aa.argv.isFailableOperation())
    }
}

class TIRTaskMultiStatement extends TIRTaskExecStatment {
    readonly vtrgts: {name: string, vtype: TIRTypeKey}[];
    readonly tasks: {task: TIRTypeKey, targs: {argn: string, argv: TIRExpression}[], argtype: TIRTypeKey, consargtype: TIRTypeKey, argexp: TIRExpression}[];

    constructor(sinfo: SourceInfo, isdefine: boolean, isconst: boolean, vtrgts: {name: string, vtype: TIRTypeKey}[], tasks: {task: TIRTypeKey, targs: {argn: string, argv: TIRExpression}[], argtype: TIRTypeKey, consargtype: TIRTypeKey, argexp: TIRExpression}[]) {
        super(TIRStatementTag.TaskMultiStatement, sinfo, isdefine, isconst, `${vtrgts.map((vv) => vv.name).join(", ")} = Task::run<${tasks.map((tt) => tt.task).join(", ")}>(${tasks.map((tt) => tt.argexp.expstr).join(", ")})`);
        this.vtrgts = vtrgts;
        this.tasks = tasks;
    }

    isFailableOperation(): boolean {
        return this.tasks.some((tt) => tt.argexp.isFailableOperation() || tt.targs.some((aa) => aa.argv.isFailableOperation()));
    }
}

class TIRTaskDashStatement extends TIRTaskExecStatment {
    readonly vtrgts: {name: string, vtype: TIRTypeKey, restype: TIRTypeKey,}[];
    readonly tasks: {task: TIRTypeKey, targs: {argn: string, argv: TIRExpression}[], argtype: TIRTypeKey, consargtype: TIRTypeKey, argexp: TIRExpression}[];

    constructor(sinfo: SourceInfo, isdefine: boolean, isconst: boolean, vtrgts: {name: string, vtype: TIRTypeKey, restype: TIRTypeKey}[], tasks: {task: TIRTypeKey, targs: {argn: string, argv: TIRExpression}[], argtype: TIRTypeKey, consargtype: TIRTypeKey, argexp: TIRExpression}[]) {
        super(TIRStatementTag.TaskMultiStatement, sinfo, isdefine, isconst, `${vtrgts.map((vv) => vv.name).join(", ")} = Task::dash<${tasks.map((tt) => tt.task).join(", ")}>(${tasks.map((tt) => tt.argexp.expstr).join(", ")})`);
        this.vtrgts = vtrgts;
        this.tasks = tasks;
    }

    isFailableOperation(): boolean {
        return this.tasks.some((tt) => tt.argexp.isFailableOperation() || tt.targs.some((aa) => aa.argv.isFailableOperation()));
    }
}

class TIRTaskAllStatement extends TIRTaskExecStatment {
    readonly vtrgt: {name: string, vtype: TIRTypeKey, elemtype: TIRTypeKey};
    readonly task: TIRTypeKey;
    readonly taskargs: {argn: string, argv: TIRExpression}[];
    readonly arg: TIRExpression;
    readonly arglisttype: TIRTypeKey;
    readonly argentrytype: TIRTypeKey;

    constructor(sinfo: SourceInfo, isdefine: boolean, isconst: boolean, vtrgt: {name: string, vtype: TIRTypeKey, elemtype: TIRTypeKey}, task: TIRTypeKey, taskargs: {argn: string, argv: TIRExpression}[], arg: TIRExpression, arglisttype: TIRTypeKey, argentrytype: TIRTypeKey) {
        super(TIRStatementTag.TaskAllStatement, sinfo, isdefine, isconst, `${vtrgt.name} = Task::all[${taskargs.map((ta) => ta.argn + "=" + ta.argv.expstr)}]<${task}>(${arg.expstr})`);
        this.vtrgt = vtrgt;
        this.task = task;
        this.taskargs = taskargs;
        this.arg = arg;
        this.arglisttype = arglisttype;
        this.argentrytype = argentrytype;
    }

    isFailableOperation(): boolean {
        return this.arg.isFailableOperation() || this.taskargs.some((aa) => aa.argv.isFailableOperation());
    }
}

class TIRTaskRaceStatement extends TIRTaskExecStatment {
    readonly vtrgt: {name: string, vtype: TIRTypeKey, restype: TIRTypeKey};
    readonly task: TIRTypeKey;
    readonly taskargs: {argn: string, argv: TIRExpression}[];
    readonly arg: TIRExpression;
    readonly arglisttype: TIRTypeKey;
    readonly argentrytype: TIRTypeKey;

    constructor(sinfo: SourceInfo, isdefine: boolean, isconst: boolean, vtrgt: {name: string, vtype: TIRTypeKey, restype: TIRTypeKey}, task: TIRTypeKey, taskargs: {argn: string, argv: TIRExpression}[], arg: TIRExpression, arglisttype: TIRTypeKey, argentrytype: TIRTypeKey) {
        super(TIRStatementTag.TaskRaceStatement, sinfo, isdefine, isconst, `${vtrgt.name} = Task::all[${taskargs.map((ta) => ta.argn + "=" + ta.argv.expstr)}]<${task}>(${arg.expstr})`);
        this.vtrgt = vtrgt;
        this.task = task;
        this.taskargs = taskargs;
        this.arg = arg;
        this.arglisttype = arglisttype;
        this.argentrytype = argentrytype;
    }

    isFailableOperation(): boolean {
        return this.arg.isFailableOperation() || this.taskargs.some((aa) => aa.argv.isFailableOperation());
    }
}

class TIRTaskSetSelfFieldStatement extends TIRStatement {
    readonly tasktype: TIRTypeKey;
    readonly field: TIRFieldKey;
    readonly fname: string;
    readonly value: TIRExpression;

    constructor(sinfo: SourceInfo, tasktype: TIRTypeKey, field: TIRFieldKey, fname: string, value: TIRExpression) {
        super(TIRStatementTag.TaskSetSelfFieldStatement, sinfo, `self.${fname} = ${value.expstr};`);
        this.tasktype = tasktype;
        this.field = field;
        this.fname = fname;
        this.value = value;
    }

    isFailableOperation(): boolean {
        return this.value.isFailableOperation();
    }

    getDirectlyModVars(): string[] {
        return ["self"];
    }
}

class TIRLoggerEmitStatement extends TIRStatement {
    readonly level: LoggerLevel;
    readonly fmt: {namespace: string, keyname: string};
    readonly args: TIRExpression[];

    constructor(sinfo: SourceInfo, level: LoggerLevel, fmt: {namespace: string, keyname: string}, args: TIRExpression[]) {
        super(TIRStatementTag.LoggerEmitStatement, sinfo, `Log::${level}(${fmt.namespace}::${fmt.keyname}${args.length !== 0 ? ", " : ""}${args.map((arg) => arg.expstr).join(", ")})`);
        this.level = level;
        this.fmt = fmt;
        this.args = args;
    }
}

class TIRLoggerEmitConditionalStatement extends TIRStatement {
    readonly level: LoggerLevel;
    readonly fmt: {namespace: string, keyname: string};
    readonly cond: TIRExpression;
    readonly args: TIRExpression[];

    constructor(sinfo: SourceInfo, level: LoggerLevel, cond: TIRExpression, fmt: {namespace: string, keyname: string}, args: TIRExpression[]) {
        super(TIRStatementTag.LoggerEmitStatement, sinfo, `Log::${level}If(${cond.expstr}, ${fmt.namespace}::${fmt.keyname}${args.length !== 0 ? ", " : ""}${args.map((arg) => arg.expstr).join(", ")})`);
        this.level = level;
        this.fmt = fmt;
        this.cond = cond;
        this.args = args;
    }
}

class TIRLoggerSetPrefixStatement extends TIRStatement {
    readonly fmt: {namespace: string, keyname: string};
    readonly args: TIRExpression[];
    readonly block: TIRScopedBlockStatement | TIRUnscopedBlockStatement;

    constructor(sinfo: SourceInfo, fmt: {namespace: string, keyname: string}, block: TIRScopedBlockStatement | TIRUnscopedBlockStatement, args: TIRExpression[]) {
        super(TIRStatementTag.LoggerSetPrefixStatement, sinfo, `Logger::scope(${fmt.namespace}::${fmt.keyname}${args.length !== 0 ? ", " : ""}${args.map((arg) => arg.expstr).join(", ")}) ${block.stmtstr}`);
        this.fmt = fmt;
        this.args = args;
        this.block = block;
    }
}

class TIRBlockStatement {
    readonly stmtstr: string;
    readonly ops: TIRStatement[];
    readonly isterminal: boolean;

    constructor(ops: TIRStatement[], isterminal: boolean) {
        this.stmtstr = "{" + ops.map((op) => op.stmtstr).join(" ") + "}";

        this.ops = ops;
        this.isterminal = isterminal;
    }

    isFailableOperation(): boolean {
        return this.ops.some((op) => op.isFailableOperation());
    }
} 

class TIRUnscopedBlockStatement extends TIRBlockStatement {
    constructor(ops: TIRStatement[]) {
        super(ops, false);
    }
}

class TIRScopedBlockStatement extends TIRBlockStatement {
    constructor(ops: TIRStatement[], isterminal: boolean,) {
        super(ops, isterminal);
    }
}

export {
    TIRCodePack,
    TIRExpressionTag, TIRExpression, TIRInvalidExpression,
    TIRLiteralNoneExpression, TIRLiteralNothingExpression, TIRLiteralBoolExpression, TIRLiteralIntegralExpression, TIRLiteralRationalExpression, TIRLiteralFloatPointExpression,
    TIRLiteralStringExpression, TIRLiteralASCIIStringExpression, TIRLiteralRegexExpression, TIRLiteralTypedStringExpression, TIRLiteralASCIITypedStringExpression, TIRLiteralTemplateStringExpression, TIRLiteralASCIITemplateStringExpression,
    TIRLiteralTypedPrimitiveDirectExpression, TIRLiteralTypedPrimitiveConstructorExpression,
    TIRAccessEnvValueExpression, TIRAccessNamespaceConstantExpression, TIRAccessConstMemberFieldExpression, TIRAccessVariableExpression, TIRAccessCapturedVariableExpression, TIRAccessScratchSingleValueExpression, TIRAccessScratchIndexExpression,
    TIRLoadIndexExpression, TIRLoadPropertyExpression, TIRLoadFieldExpression, TIRLoadFieldVirtualExpression,
    TIRConstructorPrimaryDirectExpression, TIRConstructorPrimaryCheckExpression, TIRConstructorTupleExpression, TIRConstructorRecordExpression, TIRConstructorListExpression, TIRConstructorMapExpression,
    TIRCodePackInvokeExpression,
    TIRResultOkConstructorExpression, TIRResultErrConstructorExpression, TIRSomethingConstructorExpression, TIRTypedeclDirectExpression, TIRTypedeclConstructorExpression,
    TIRCallNamespaceFunctionExpression, TIRCallNamespaceOperatorExpression, TIRCallStaticFunctionExpression,
    TIRLogicActionAndExpression, TIRLogicActionOrExpression,
    TIRPrefixNotExpression, TIRPrefixNegateExpression,
    TIRBinAddExpression, TIRBinSubExpression, TIRBinMultExpression, TIRBinDivExpression,
    TIRBinKeyEqBothUniqueExpression, TIRBinKeyEqOneUniqueExpression, TIRBinKeyEqGeneralExpression, TIRBinKeyNeqBothUniqueExpression, TIRBinKeyNeqOneUniqueExpression, TIRBinKeyNeqGeneralExpression, TIRBinKeyUniqueLessExpression, TIRBinKeyGeneralLessExpression,
    TIRNumericEqExpression, TIRNumericNeqExpression, TIRNumericLessExpression, TIRNumericLessEqExpression, TIRNumericGreaterExpression, TIRNumericGreaterEqExpression,
    TIRBinLogicAndExpression, TIRBinLogicOrExpression, TIRBinLogicImpliesExpression,
    TIRMapEntryConstructorExpression, TIRIfExpression, TIRSwitchExpression, TIRMatchExpression,
    TIRTaskSelfFieldExpression, TIRTaskSelfControlExpression, TIRTaskGetIDExpression,
    TIRCoerceSafeExpression,
    TIRInjectExpression, TIRExtractExpression,
    TIRCreateCodePackExpression,
    TIRTestIsExpression, 
    TIRITestIsSpecialExpression, TIRIsNoneSpecialExpression, TIRIsSomeSpecialExpression, TIRIsNothingSpecialExpression, TIRIsSomethingSpecialExpression, TIRIsOkSpecialExpression, TIRIsErrSpecialExpression,
    TIRITestIsLiteralEqExpression, TIRIsEqualToLiteralExpression, TIRIsNotEqualToLiteralExpression,
    TIRITestIsTypeExpression, TIRIsTypeExpression, TIRIsNotTypeExpression, TIRIsSubTypeExpression, TIRIsNotSubTypeExpression,
    TIRAsExpression,
    TIRAsSpecialExpression, TIRAsNoneSpecialExpression, TIRAsSomeSpecialExpression, TIRAsNothingSpecialExpression, TIRAsSomethingSpecialExpression, TIRAsOkSpecialExpression, TIRAsErrSpecialExpression,
    TIRIAsLiteralEqExpression, TIRAsEqualToLiteralExpression, TIRAsNotEqualToLiteralExpression,
    TIRITestAsTypeExpression, TIRAsTypeExpression, TIRAsNotTypeExpression, TIRAsSubTypeExpression, TIRAsNotSubTypeExpression,
    TIRVariableRetypeStatement, TIRVariableSCRetypeStatement, TIRExpressionSCReturnDefineAndAssignStatement, TIRExpressionSCReturnAssignStatement,
    TIRCallMemberFunctionExpression, TIRCallMemberFunctionDynamicExpression, TIRCallMemberFunctionSelfRefExpression,
    TIRCallMemberFunctionTaskExpression, TIRCallMemberFunctionTaskSelfRefExpression, TIRCallMemberActionExpression,
    TIRLiteralValue,
    TIRStatementTag,
    TIRStatement,
    TIRNopStatement, TIRAbortStatement, TIRAssertCheckStatement, TIRDebugStatement,
    TIRVarDeclareStatement, TIRVarDeclareAndAssignStatement, TIRVarAssignStatement,
    TIRCallWRefStatement,
    TIRReturnStatement, TIRReturnStatementWRef, TIRReturnStatementWTaskRef, TIRReturnStatementWAction,
    TIRIfStatement, TIRSwitchStatement, TIRMatchStatement,
    TIREnvironmentFreshStatement, TIREnvironmentSetStatement, TIREnvironmentSetStatementBracket,
    TIRTaskRunStatement, TIRTaskMultiStatement, TIRTaskDashStatement, TIRTaskAllStatement, TIRTaskRaceStatement,
    TIRTaskSetSelfFieldStatement,
    TIRLoggerEmitStatement, TIRLoggerEmitConditionalStatement, TIRLoggerSetPrefixStatement,
    TIRBlockStatement, TIRUnscopedBlockStatement, TIRScopedBlockStatement
};
