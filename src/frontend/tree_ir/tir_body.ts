
import { TIRCodePack, TIRFieldKey, TIRInvokeKey, TIRTypeKey } from "./tir_assembly";

import { LoggerLevel, logLevelName, SourceInfo } from "../build_decls";
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

    BSQONLiteralExpression = "BSQONLiteralExpression",

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

const s_iident = "  ";

function sinfo_bsqemit(sinfo: SourceInfo): string {
    return `TreeIR::SourceInfo{${sinfo.line}n, ${sinfo.column}n, ${sinfo.pos}n, ${sinfo.span}n}`;
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

    bsqemit_exp(ii: string): string {
        return `TreeIR::${this.tag}{\n${ii + s_iident}${sinfo_bsqemit(this.sinfo)},\n${ii + s_iident}"${this.etype}"`;
    }

    bsqemit_exp_il(ii: string): string {
        return `TreeIR::${this.tag}{${sinfo_bsqemit(this.sinfo)}, "${this.etype}"`;
    }

    abstract bsqemit(ii: string): string;
}

class TIRInvalidExpression extends TIRExpression {
    constructor(sinfo: SourceInfo, etype: TIRTypeKey) {
        super(TIRExpressionTag.InvalidExpresion, sinfo, etype, "[INVALID]");
    }

    bsqemit(ii: string): string {
        return "[SHOULD NOT BE EMITTED]";
    }
}

class TIRLiteralNoneExpression extends TIRExpression {
    constructor(sinfo: SourceInfo) {
        super(TIRExpressionTag.LiteralNoneExpression, sinfo, "None", "none");
    }

    bsqemit(ii: string): string {
        return this.bsqemit_exp_il(ii) + "}";
    }
}

class TIRLiteralNothingExpression extends TIRExpression {
    constructor(sinfo: SourceInfo) {
        super(TIRExpressionTag.LiteralNothingExpression, sinfo, "Nothing", "nothing");
    }

    bsqemit(ii: string): string {
        return this.bsqemit_exp_il(ii) + "}";
    }
}

class TIRLiteralBoolExpression extends TIRExpression {
    readonly value: boolean;

    constructor(sinfo: SourceInfo, value: boolean) {
        super(TIRExpressionTag.LiteralBoolExpression, sinfo, "Bool", value ? "true" : "false");
        this.value = value;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_exp_il(ii) + `, ${this.value ? "true" : "false"}}`;
    }
}

class TIRLiteralIntegralExpression extends TIRExpression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string, itype: TIRTypeKey) {
        super(TIRExpressionTag.LiteralIntegralExpression, sinfo, itype, value);
        this.value = value;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_exp_il(ii) + `, "${this.value}"}`;
    }
}

class TIRLiteralRationalExpression extends TIRExpression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string) {
        super(TIRExpressionTag.LiteralRationalExpression, sinfo, "Rational", value);
        this.value = value;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_exp_il(ii) + `, "${this.value}"}`;
    }
}

class TIRLiteralFloatPointExpression extends TIRExpression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string, fptype: TIRTypeKey) {
        super(TIRExpressionTag.LiteralFloatPointExpression, sinfo, fptype, value);
        this.value = value;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_exp_il(ii) + `, "${this.value}"}`;
    }
}

class TIRLiteralStringExpression extends TIRExpression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string) {
        super(TIRExpressionTag.LiteralStringExpression, sinfo, "String", value);
        this.value = value;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_exp_il(ii) + `, ${this.value}}`;
    }
}

class TIRLiteralRegexExpression extends TIRExpression {
    readonly value: BSQRegex;

    constructor(sinfo: SourceInfo, value: BSQRegex) {
        super(TIRExpressionTag.LiteralRegexExpression, sinfo, "Regex", value.regexstr);
        this.value = value;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_exp_il(ii) + `, "${this.value}"}`;
    }
}

class TIRLiteralASCIIStringExpression extends TIRExpression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string) {
        super(TIRExpressionTag.LiteralASCIIStringExpression, sinfo, "ASCIIString", value);
        this.value = value;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_exp_il(ii) + `, ${this.value}}`;
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

    bsqemit(ii: string): string {
        return this.bsqemit_exp_il(ii) + `, "${this.oftype}", ${this.value}}`;
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

    bsqemit(ii: string): string {
        return this.bsqemit_exp_il(ii) + `, "${this.oftype}", ${this.value}}`;
    }
}

class TIRLiteralTemplateStringExpression extends TIRExpression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string, etype: TIRTypeKey) {
        super(TIRExpressionTag.LiteralTemplateStringExpression, sinfo, etype, value);
        this.value = value;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_exp_il(ii) + `, "${this.value}"}`;
    }
}

class TIRLiteralASCIITemplateStringExpression extends TIRExpression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string, etype: TIRTypeKey) {
        super(TIRExpressionTag.LiteralASCIITemplateStringExpression, sinfo, etype, value);
        this.value = value;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_exp_il(ii) + `, "${this.value}"}`;
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

    bsqemit(ii: string): string {
        return this.bsqemit_exp_il(ii) + `, ${this.value.bsqemit("")}, "${this.constype}", "${this.basetype}"}`;
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

    bsqemit(ii: string): string {
        return this.bsqemit_exp_il(ii) + `, ${this.value.bsqemit("")}, "${this.constype}", "${this.basetype}"}`;
    }

    //
    //TODO: compiler may want to treat this like a constant and precompute with a reference for any uses
    //
}

class TIRBSQONLiteralExpression extends TIRExpression {
    readonly bsqonstr: string;

    constructor(sinfo: SourceInfo, bsqonstr: string, bsqontype: TIRTypeKey) {
        super(TIRExpressionTag.BSQONLiteralExpression, sinfo, bsqontype, bsqonstr);
        this.bsqonstr = bsqonstr;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_exp_il(ii) + `, "${this.bsqonstr}"}`;
    }
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

    bsqemit(ii: string): string {
        return this.bsqemit_exp_il(ii) + `, "${this.keyname}", "${this.valtype}", "${this.restype}", ${this.orNoneMode}}`;
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

    bsqemit(ii: string): string {
        return this.bsqemit_exp_il(ii) + `, "${this.ns}", "${this.cname}"}`;
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

    bsqemit(ii: string): string {
        return this.bsqemit_exp_il(ii) + `, "${this.tkey}", "${this.cname}"}`;
    }
}

class TIRAccessVariableExpression extends TIRExpression {
    readonly name: string;

    constructor(sinfo: SourceInfo, name: string, etype: TIRTypeKey) {
        super(TIRExpressionTag.AccessVariableExpression, sinfo, etype, name);
        this.name = name;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_exp_il(ii) + `, "${this.name}"}`;
    }
}

class TIRAccessCapturedVariableExpression extends TIRExpression {
    readonly name: string;

    constructor(sinfo: SourceInfo, name: string, etype: TIRTypeKey) {
        super(TIRExpressionTag.AccessCapturedVariableExpression, sinfo, etype, name);
        this.name = name;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_exp_il(ii) + `, "${this.name}"}`;
    }
}

class TIRAccessScratchSingleValueExpression extends TIRExpression {
    readonly sidx: number;

    constructor(sinfo: SourceInfo, etype: TIRTypeKey, sidx: number) {
        super(TIRExpressionTag.AccessScratchSingleValueExpression, sinfo, etype, `$$scratch<${sidx}, ${etype}>[]`);
        this.sidx = sidx;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_exp_il(ii) + `, ${this.sidx}n}`;
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

    bsqemit(ii: string): string {
        return this.bsqemit_exp_il(ii) + `, ${this.index}n, ${this.sidx}n}`;
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

    bsqemit_loadsingle(ii: string, accs: string): any {
        return this.bsqemit_exp(ii) + `,\n${ii + s_iident}"${this.tkey}",\n${ii + s_iident}${this.exp.bsqemit(ii + s_iident)},\n${ii + s_iident}${accs}\n${ii}}`;
    }
}

class TIRLoadIndexExpression extends TIRLoadSingleExpression {
    readonly index: number;

    constructor(sinfo: SourceInfo, exp: TIRExpression, tkey: TIRTypeKey, index: number, resultType: TIRTypeKey) {
        super(TIRExpressionTag.LoadIndexExpression, sinfo, tkey, exp, resultType, `${exp.expstr}.${index}`);
        this.index = index;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_loadsingle(ii, `${this.index}n`);
    }
} 

class TIRLoadPropertyExpression extends TIRLoadSingleExpression {
    readonly property: string;

    constructor(sinfo: SourceInfo, exp: TIRExpression, tkey: TIRTypeKey, property: string, resultType: TIRTypeKey) {
        super(TIRExpressionTag.LoadPropertyExpression, sinfo, tkey, exp, resultType, `${exp.expstr}.${property}`);
        this.property = property;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_loadsingle(ii, `"${this.property}"`);
    }
}

class TIRLoadFieldExpression extends TIRLoadSingleExpression {
    readonly fieldkey: TIRFieldKey;

    constructor(sinfo: SourceInfo, tkey: TIRTypeKey, exp: TIRExpression, fieldkey: TIRFieldKey, resultType: TIRTypeKey) {
        super(TIRExpressionTag.LoadFieldExpression, sinfo, tkey, exp, resultType, `${exp.expstr}.${fieldkey}`);
        this.fieldkey = fieldkey;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_loadsingle(ii, `"${this.fieldkey}"`);
    }
}

class TIRLoadFieldVirtualExpression extends TIRLoadSingleExpression {
    readonly fieldkey: TIRFieldKey;

    constructor(sinfo: SourceInfo, tkey: TIRTypeKey, exp: TIRExpression, fieldkey: TIRFieldKey, resultType: TIRTypeKey) {
        super(TIRExpressionTag.LoadFieldVirtualExpression, sinfo, tkey, exp, resultType, `${exp.expstr}.${fieldkey}`);
        this.fieldkey = fieldkey;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_loadsingle(ii, `"${this.fieldkey}"`);
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

    bsqemit(ii: string): string {
        const pfx = this.bsqemit_exp(ii) + `,\n${ii + s_iident}"${this.oftype}"`;
        
        if(this.args.length === 0) {
            return pfx + `\n${ii}}`;
        }
        else {
            const args = this.args.map((arg) => arg.bsqemit(ii + s_iident)).join(`,\n${ii + s_iident}`);
            return pfx + `,\n${ii + s_iident}` + args + `\n${ii}}`;
        }
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
        super(TIRExpressionTag.ConstructorListExpression, sinfo, oftype, args, `[${args.map((arg) => arg.expstr).join(", ")}]`);
    }
}
    
class TIRConstructorMapExpression extends TIRConstructorExpression {
    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.ConstructorMapExpression, sinfo, oftype, args, `[${args.map((arg) => arg.expstr).join(", ")}]`);
    }
}

class TIRCodePackInvokeExpression extends TIRExpression {
    readonly cpack: TIRCodePack;
    readonly args: TIRExpression[];

    constructor(sinfo: SourceInfo, etype: TIRTypeKey, cpack: TIRCodePack, args: TIRExpression[]) {
        super(TIRExpressionTag.CodePackInvokeExpression, sinfo, etype, `${cpack.invk}(${[...args.map((arg) => arg.expstr)].join(", ")})`);
        this.cpack = cpack;
        this.args = args;
    }

    bsqemit(ii: string): string {
        const pfx = this.bsqemit_exp(ii) + `,\n${ii + s_iident}${this.cpack.bsqemit(ii)}`;
        
        if(this.args.length === 0) {
            return pfx + `\n${ii}}`;
        }
        else {
            const args = this.args.map((arg) => arg.bsqemit(ii + s_iident)).join(`,\n${ii + s_iident}`);
            return pfx + `,\n${ii + s_iident}` + args + `\n${ii}}`;
        }
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

    bsqemit(ii: string): string {
        return this.bsqemit_exp(ii) + `,\n${ii + s_iident}"${this.oftype}",\n${ii + s_iident}${this.arg.bsqemit(ii + s_iident)}\n${ii}}`;
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

    bsqemit_call(ii: string, fci: string): string {
        const pfx = this.bsqemit_exp(ii) + `,\n${ii + s_iident}"${this.fkey}"`;

        if (this.args.length === 0) {
            return pfx + `, \n${fci}\n${ii}}`;
        }
        else {
            const args = this.args.map((arg) => arg.bsqemit(ii + s_iident + s_iident)).join(`,\n${ii + s_iident + s_iident}`);
            const agstr = args.length !== 0 ? `[\n${ii + s_iident + s_iident}${args}\n${ii + s_iident}]` : "[]";
            return pfx + `,\n${ii + s_iident}` + agstr + `, \n${fci}\n${ii}}`;
        }
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

    bsqemit(ii: string): string {
        return this.bsqemit_call(ii, `${ii + s_iident}"${this.ns}",\n${ii + s_iident}"${this.fname}"`);
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

    bsqemit(ii: string): string {
        return this.bsqemit_call(ii, `"${this.ns}",\n${ii + s_iident}"${this.oname}"`);
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

    bsqemit(ii: string): string {
        return this.bsqemit_call(ii, `"${this.tkey}",\n${ii + s_iident}"${this.fname}"`);
    }
}

//abstract class for logic actions
abstract class TIRLogicActionExpression extends TIRExpression {
    readonly args: TIRExpression[]; 

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, args: TIRExpression[], exprstr: string) {
        super(tag, sinfo, "Bool", exprstr);
        this.args = args;
    }

    bsqemit(ii: string): string {
        const pfx = this.bsqemit_exp(ii);

        if (this.args.length === 0) {
            return pfx + `\n${ii}}`;
        }
        else {
            const args = this.args.map((arg) => arg.bsqemit(ii + s_iident)).join(`,\n${ii + s_iident}`);
            return pfx + `,\n${ii + s_iident}` + args + `\n${ii}}`;
        }
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
}

class TIRPrefixNotExpression extends TIRUnaryExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression) {
        super(TIRExpressionTag.PrefixNotExpression, sinfo, "Bool", exp, `!(${exp.expstr})`);
    }

    bsqemit(ii: string): string {
        return this.bsqemit_exp(ii) + `,\n${ii + s_iident}${this.exp.bsqemit(ii + s_iident)}\n${ii}}`;
    }
}

class TIRPrefixNegateExpression extends TIRUnaryExpression {
    readonly optype: TIRTypeKey;

    constructor(sinfo: SourceInfo, exp: TIRExpression, exptype: TIRTypeKey, ntype: TIRTypeKey) {
        super(TIRExpressionTag.PrefixNegateExpression, sinfo, exptype, exp, `-(${exp.expstr})`);
        this.optype = ntype;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_exp(ii) + `,\n${ii + s_iident}${this.exp.bsqemit(ii + s_iident)},\n${ii + s_iident}"${this.optype}"\n${ii}}`;
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

    bsqemit(ii: string): any {
        return this.bsqemit_exp(ii) + `,\n${ii + s_iident}"${this.optype}",\n${ii + s_iident}${this.lhs.bsqemit(ii + s_iident)},\n${ii + s_iident}${this.rhs.bsqemit(ii + s_iident)}\n${ii}}`;
    }
}

class TIRBinAddExpression extends TIRBinOpExpression {
    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, exptype: TIRTypeKey, ntype: TIRTypeKey) {
        super(TIRExpressionTag.BinAddExpression, sinfo, lhs, rhs, exptype, ntype, `(${lhs.expstr} + ${rhs.expstr})`);
    }
}

class TIRBinSubExpression extends TIRBinOpExpression {
    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, exptype: TIRTypeKey, ntype: TIRTypeKey) {
        super(TIRExpressionTag.BinSubExpression, sinfo, lhs, rhs, exptype, ntype, `(${lhs.expstr} - ${rhs.expstr})`);
    }

    
    bsqemit(ii: string): any {
        return this.bsqemit_exp(ii) + `,\n${ii + s_iident}"${this.optype}",\n${ii + s_iident}${this.lhs.bsqemit(ii + s_iident)},\n${ii + s_iident}${this.rhs.bsqemit(ii + s_iident)},\n${ii + s_iident}-1i\n${ii}}`;
    }
}

class TIRBinMultExpression extends TIRBinOpExpression {
    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, exptype: TIRTypeKey, ntype: TIRTypeKey) {
        super(TIRExpressionTag.BinMultExpression, sinfo, lhs, rhs, exptype, ntype, `(${lhs.expstr} * ${rhs.expstr})`);
    }
}

class TIRBinDivExpression extends TIRBinOpExpression {
    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, exptype: TIRTypeKey, ntype: TIRTypeKey) {
        super(TIRExpressionTag.BinDivExpression, sinfo, lhs, rhs, exptype, ntype, `(${lhs.expstr} / ${rhs.expstr})`);
    }

    bsqemit(ii: string): any {
        return this.bsqemit_exp(ii) + `,\n${ii + s_iident}"${this.optype}",\n${ii + s_iident}${this.lhs.bsqemit(ii + s_iident)},\n${ii + s_iident}${this.rhs.bsqemit(ii + s_iident)},\n${ii + s_iident}-1i\n${ii}}`;
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

    bsqemit(ii: string): any {
        return this.bsqemit_exp(ii) + `,\n${ii + s_iident}"${this.optype}",\n${ii + s_iident}${this.lhs.bsqemit(ii + s_iident)},\n${ii + s_iident}${this.rhs.bsqemit(ii + s_iident)}\n${ii}}`;
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

    bsqemit(ii: string): string {
        return this.bsqemit_exp(ii) 
        + `,\n${ii + s_iident}"${this.oftype}",\n${ii + s_iident}${this.uarg.bsqemit(ii + s_iident)}`
        + `,\n${ii + s_iident}"${this.gtype}",\n${ii + s_iident}${this.garg.bsqemit(ii + s_iident)}`
        + `\n${ii}}`;
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

    bsqemit(ii: string): string {
        return this.bsqemit_exp(ii) 
        + `,\n${ii + s_iident}"${this.lhstype}",\n${ii + s_iident}${this.lhs.bsqemit(ii + s_iident)}`
        + `,\n${ii + s_iident}"${this.rhstype}",\n${ii + s_iident}${this.rhs.bsqemit(ii + s_iident)}`
        + `\n${ii}}`;
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

    bsqemit(ii: string): any {
        return this.bsqemit_exp(ii) + `,\n${ii + s_iident}"${this.optype}",\n${ii + s_iident}${this.lhs.bsqemit(ii + s_iident)},\n${ii + s_iident}${this.rhs.bsqemit(ii + s_iident)}\n${ii}}`;
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

    bsqemit(ii: string): string {
        return this.bsqemit_exp(ii)
        + `,\n${ii + s_iident}"${this.oftype}",\n${ii + s_iident}${this.uarg.bsqemit(ii + s_iident)}`
        + `,\n${ii + s_iident}"${this.gtype}",\n${ii + s_iident}${this.garg.bsqemit(ii + s_iident)}`
        + `\n${ii}}`;
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

    bsqemit(ii: string): string {
        return this.bsqemit_exp(ii)
        + `,\n${ii + s_iident}"${this.lhstype}",\n${ii + s_iident}${this.lhs.bsqemit(ii + s_iident)}`
        + `,\n${ii + s_iident}"${this.rhstype}",\n${ii + s_iident}${this.rhs.bsqemit(ii + s_iident)}`
        + `\n${ii}}`;
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

    bsqemit(ii: string): any {
        return this.bsqemit_exp(ii) + `,\n${ii + s_iident}"${this.optype}",\n${ii + s_iident}${this.lhs.bsqemit(ii + s_iident)},\n${ii + s_iident}${this.rhs.bsqemit(ii + s_iident)}\n${ii}}`;
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

    bsqemit(ii: string): any {
        return this.bsqemit_exp(ii) + `,\n${ii + s_iident}"${this.optype}",\n${ii + s_iident}${this.lhs.bsqemit(ii + s_iident)},\n${ii + s_iident}${this.rhs.bsqemit(ii + s_iident)}\n${ii}}`;
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

    bsqemit(ii: string): any {
        return this.bsqemit_exp(ii) + `,\n${ii + s_iident}"${this.optype}",\n${ii + s_iident}${this.lhs.bsqemit(ii + s_iident)},\n${ii + s_iident}${this.rhs.bsqemit(ii + s_iident)}\n${ii}}`;
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

    bsqemit(ii: string): any {
        return this.bsqemit_exp(ii) + `,\n${ii + s_iident}${this.lhs.bsqemit(ii + s_iident)},\n${ii + s_iident}${this.rhs.bsqemit(ii + s_iident)}\n${ii}}`;
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

    bsqemit(ii: string): string {
        return this.bsqemit_exp(ii) 
        + `,\n${ii + s_iident}"${this.ktype}",\n${ii + s_iident}${this.vtype}",\n${ii + s_iident}${this.oftype}"`
        + `,\n${ii + s_iident}${this.kexp.bsqemit(ii + s_iident)},\n${ii + s_iident}${this.vexp.bsqemit(ii + s_iident)}`
        + `\n${ii}}`;
    }
}

class TIRIfExpression extends TIRExpression {
    readonly ifentry: {test: TIRExpression, value: TIRExpression, binderinfo: [TIRExpression, number, TIRExpression, string] | undefined};
    readonly elifentries: {test: TIRExpression, value: TIRExpression, binderinfo: [TIRExpression, number, TIRExpression, string] | undefined}[];
    readonly elseentry: {value: TIRExpression, binderinfo: [TIRExpression, number, TIRExpression, string] | undefined};

    constructor(sinfo: SourceInfo, etype: TIRTypeKey, ifentry: {test: TIRExpression, value: TIRExpression, binderinfo: [TIRExpression, number, TIRExpression, string] | undefined}, elifentries: {test: TIRExpression, value: TIRExpression, binderinfo: [TIRExpression, number, TIRExpression, string] | undefined}[], elseentry: {value: TIRExpression, binderinfo: [TIRExpression, number, TIRExpression, string] | undefined}) {
        super(TIRExpressionTag.IfExpression, sinfo, etype, `if(${ifentry.test.expstr}) then ${ifentry.value.expstr} ${elifentries.map((efi) => `elif(${efi.test.expstr}) then ${efi.value.expstr}`)} else ${elseentry.value.expstr}`);
        this.ifentry = ifentry;
        this.elifentries = elifentries;
        this.elseentry = elseentry;
    }

    private static bsqemit_binder(ii: string, bb: [TIRExpression, number, TIRExpression, string] | undefined): string {
        if(bb === undefined) {
            return "none";
        }
        else {
            const iident = ii + s_iident;
            return `[`
            + `\n${iident}${bb[0].bsqemit(iident + s_iident)}`
            + `,\n${iident}${bb[1]}n`
            + `,\n${iident}${bb[2].bsqemit(iident + s_iident)}`
            + `,\n${iident}"${bb[3]}"`
            + `\n${ii}]`;
        }
    }
    private bsqemit_ifentry(ii: string): string {
        const iident = ii + s_iident;

        return `{`
        + `\n${iident}etest=${this.ifentry.test.bsqemit(iident + s_iident)}`
        + `,\n${iident}value=${this.ifentry.value.bsqemit(iident + s_iident)}`
        + `,\n${iident}binderinfo=${TIRIfExpression.bsqemit_binder(iident + s_iident, this.ifentry.binderinfo)}`
        + `\n${ii}}`;
    }
    private static bsqemit_elifentry(ii: string, entry: {test: TIRExpression, value: TIRExpression, binderinfo: [TIRExpression, number, TIRExpression, string] | undefined}): string {
        const iident = ii + s_iident;

        return `{`
        + `\n${iident}etest=${entry.test.bsqemit(iident + s_iident)}`
        + `,\n${iident}value=${entry.value.bsqemit(iident + s_iident)}`
        + `,\n${iident}binderinfo=${TIRIfExpression.bsqemit_binder(iident + s_iident, entry.binderinfo)}`
        + `\n${ii}}`;
    }
    private bsqemit_elifentries(ii: string): string {
        const iident = ii + s_iident;

        return `[`
        + this.elifentries.map((e) => TIRIfExpression.bsqemit_elifentry(iident + s_iident, e)).join(`,\n${iident}`)
        + `\n${ii}]`;
    }
    private bsqemit_elseentry(ii: string): string {
        const iident = ii + s_iident;

        return `{`
        + `${iident}value=${this.elseentry.value.bsqemit(iident + s_iident)}`
        + `,\n${iident}binderinfo=${TIRIfExpression.bsqemit_binder(iident + s_iident, this.elseentry.binderinfo)}`
        + `\n${ii + s_iident}}`;
    }

    bsqemit(ii: string): string {
        const iident = ii + s_iident;

        const ifes = this.bsqemit_ifentry(iident);
        const elifes = this.bsqemit_elifentries(iident);
        const ee = this.bsqemit_elseentry(iident);

        return this.bsqemit_exp(ii)
        + `,\n${iident}${ifes},\n${iident}${elifes},\n${iident}${ee}\n${ii}}`
        + `\n${ii}}`;
    }
}

class TIRSwitchExpression extends TIRExpression {
    readonly exp: TIRExpression;
    readonly scratchidx: number;
    readonly clauses: {match: TIRExpression, value: TIRExpression, binderinfo: [TIRExpression, string] | undefined}[];
    readonly edefault: {value: TIRExpression, binderinfo: [TIRExpression, string] | undefined} | undefined;
    readonly isexhaustive: boolean;

    constructor(sinfo: SourceInfo, etype: TIRTypeKey, exp: TIRExpression, scratchidx: number, clauses: {match: TIRExpression, value: TIRExpression, binderinfo: [TIRExpression, string] | undefined}[], edefault: {value: TIRExpression, binderinfo: [TIRExpression, string] | undefined} | undefined, isexhaustive: boolean) {
        super(TIRExpressionTag.SwitchExpression, sinfo, etype, `switch(${exp.expstr}) ${clauses.map((ci) => `(${ci.match.expstr} => ${ci.value.expstr})`)}${edefault !== undefined ? "(_ => " + edefault.value.expstr : ""}`);
        this.exp = exp;
        this.scratchidx = scratchidx;
        this.clauses = clauses;
        this.edefault = edefault;
        this.isexhaustive = isexhaustive;
    }

    private static bsqemit_binder(ii: string, bb: [TIRExpression, string] | undefined): string {
        if(bb === undefined) {
            return "none";
        }
        else {
            const iident = ii + s_iident;
            return `[`
            + `\n${iident}${bb[0].bsqemit(iident + s_iident)}`
            + `,\n${iident}"${bb[1]}"`
            + `\n${ii}]`;
        }
    }
    private static bsqemit_clauseentry(ii: string, entry: {match: TIRExpression, value: TIRExpression, binderinfo: [TIRExpression, string] | undefined}): string {
        const iident = ii + s_iident;

        return `{`
        + `\n${iident}ematch=${entry.match.bsqemit(iident + s_iident)}`
        + `,\n${iident}value=${entry.value.bsqemit(iident + s_iident)}`
        + `,\n${iident}binderinfo=${TIRSwitchExpression.bsqemit_binder(iident + s_iident, entry.binderinfo)}`
        + `\n${ii}}`;
    }
    private bsqemit_clauses(ii: string): string {
        const iident = ii + s_iident;

        return `[`
        + this.clauses.map((e) => TIRSwitchExpression.bsqemit_clauseentry(iident + s_iident, e)).join(`,\n${iident}`)
        + `\n${ii}]`;
    }
    private bsqemit_default(ii: string): string {
        const iident = ii + s_iident;
        if(this.edefault === undefined) {
            return "none";
        }
        else {
            return `{`
                + `${iident}value=${this.edefault.value.bsqemit(iident + s_iident)}`
                + `,\n${iident}binderinfo=${TIRSwitchExpression.bsqemit_binder(iident + s_iident, this.edefault.binderinfo)}`
                + `\n${ii + s_iident}}`;
        }
    }

    bsqemit(ii: string): string {
        const iident = ii + s_iident;

        const cles = this.bsqemit_clauses(iident);
        const dd = this.bsqemit_default(iident);

        return this.bsqemit_exp(ii)
        + `${this.exp.bsqemit(iident)},\n${iident}${this.scratchidx}`
        + `,\n${iident}${cles},\n${iident}${dd}`
        + `,\n${iident}${this.isexhaustive}`
        + `\n${ii}}`;
    }
}

class TIRMatchExpression extends TIRExpression {
    readonly exp: TIRExpression;
    readonly scratchidx: number;
    readonly clauses: {match: TIRExpression, value: TIRExpression, binderinfo: [TIRExpression, string] | undefined}[];
    readonly edefault: {value: TIRExpression, binderinfo: [TIRExpression, string] | undefined} | undefined;
    readonly isexhaustive: boolean;

    constructor(sinfo: SourceInfo, etype: TIRTypeKey, exp: TIRExpression, scratchidx: number, clauses: {match: TIRExpression, value: TIRExpression, binderinfo: [TIRExpression, string] | undefined}[], edefault: {value: TIRExpression, binderinfo: [TIRExpression, string] | undefined} | undefined, isexhaustive: boolean) {
        super(TIRExpressionTag.MatchExpression, sinfo, etype, `match(${exp.expstr}) ${clauses.map((ci) => `(${ci.match.expstr} => ${ci.value.expstr})`)}${edefault !== undefined ? "(_ => " + edefault.value.expstr : ""}`);
        this.exp = exp;
        this.scratchidx = scratchidx;
        this.clauses = clauses;
        this.edefault = edefault;
        this.isexhaustive = isexhaustive;
    }

    private static bsqemit_binder(ii: string, bb: [TIRExpression, string] | undefined): string {
        if(bb === undefined) {
            return "none";
        }
        else {
            const iident = ii + s_iident;
            return `[`
            + `\n${iident}${bb[0].bsqemit(iident + s_iident)}`
            + `,\n${iident}"${bb[1]}"`
            + `\n${ii}]`;
        }
    }
    private static bsqemit_clauseentry(ii: string, entry: {match: TIRExpression, value: TIRExpression, binderinfo: [TIRExpression, string] | undefined}): string {
        const iident = ii + s_iident;

        return `{`
        + `\n${iident}ematch=${entry.match.bsqemit(iident + s_iident)}`
        + `,\n${iident}value=${entry.value.bsqemit(iident + s_iident)}`
        + `,\n${iident}binderinfo=${TIRMatchExpression.bsqemit_binder(iident + s_iident, entry.binderinfo)}`
        + `\n${ii}}`;
    }
    private bsqemit_clauses(ii: string): string {
        const iident = ii + s_iident;

        return `[`
        + this.clauses.map((e) => TIRMatchExpression.bsqemit_clauseentry(iident + s_iident, e)).join(`,\n${iident}`)
        + `\n${ii}]`;
    }
    private bsqemit_default(ii: string): string {
        const iident = ii + s_iident;
        if(this.edefault === undefined) {
            return "none";
        }
        else {
            return `{`
                + `${iident}value=${this.edefault.value.bsqemit(iident + s_iident)}`
                + `,\n${iident}binderinfo=${TIRMatchExpression.bsqemit_binder(iident + s_iident, this.edefault.binderinfo)}`
                + `\n${ii + s_iident}}`;
        }
    }

    bsqemit(ii: string): string {
        const iident = ii + s_iident;

        const cles = this.bsqemit_clauses(iident);
        const dd = this.bsqemit_default(iident);

        return this.bsqemit_exp(ii)
        + `${this.exp.bsqemit(iident)},\n${iident}${this.scratchidx}`
        + `,\n${iident}${cles},\n${iident}${dd}`
        + `,\n${iident}${this.isexhaustive}`
        + `\n${ii}}`;
    }
}

class TIRTaskSelfFieldExpression extends TIRExpression {
    readonly tasktype: TIRTypeKey;
    readonly fieldkey: TIRFieldKey;
    readonly fname: string;

    constructor(sinfo: SourceInfo, tasktype: TIRTypeKey, fieldkey: TIRFieldKey, fname: string, resultType: TIRTypeKey) {
        super(TIRExpressionTag.TaskSelfFieldExpression, sinfo, resultType, `self.${fname}`);
        this.tasktype = tasktype;
        this.fieldkey = fieldkey;
        this.fname = fname;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_exp_il(ii) + `, "${this.tasktype}", "${this.fieldkey}", "${this.fname}"}`;
    }
}

class TIRTaskSelfControlExpression extends TIRExpression {
    readonly tasktype: TIRTypeKey;

    constructor(sinfo: SourceInfo, tasktype: TIRTypeKey, resultType: TIRTypeKey) {
        super(TIRExpressionTag.TaskSelfControlExpression, sinfo, resultType, `self.cntl`);
        this.tasktype = tasktype;
    }

    bsqemit(ii: string): string {
        return "[Removing Setup for Control Fields]";
    }
}

class TIRTaskGetIDExpression extends TIRExpression {
    readonly tasktype: TIRTypeKey;

    constructor(sinfo: SourceInfo, tasktype: TIRTypeKey, resultType: TIRTypeKey) {
        super(TIRExpressionTag.TaskGetIDExpression, sinfo, resultType, `getTaskID`);
        this.tasktype = tasktype;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_exp_il(ii) + `, "${this.tasktype}"}`;
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
}

class TIRCoerceSafeExpression extends TIRCoerceSafeSingleExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, fromtype: TIRTypeKey, totype: TIRTypeKey) {
        super(TIRExpressionTag.CoerceSafeExpression, sinfo, exp, fromtype, totype, `coerce_safe<${totype}>(${exp.expstr})`);
    }

    bsqemit(ii: string): string {
        return this.bsqemit_exp(ii) + `,\n${ii + s_iident}${this.exp.bsqemit(ii + s_iident)},\n${ii + s_iident}"${this.fromtype}",\n${ii + s_iident}"${this.totype}"\n${ii}}`;
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
    
    bsqemit(ii: string): string {
        return this.bsqemit_exp(ii) + `,\n${ii + s_iident}${this.exp.bsqemit(ii + s_iident)},\n${ii + s_iident}"${this.totype}"\n${ii}}`;
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

    bsqemit(ii: string): string {
        return this.bsqemit_exp(ii)
        + `,\n${ii + s_iident}${this.pcodepack.bsqemit(ii + s_iident)}`
        + `,\n${ii + s_iident}[${this.capturedirect.map((c) => `"${c}"`).join(", ")}]`
        + `,\n${ii + s_iident}[${this.captureindirect.map((c) => `"${c}"`).join(", ")}]`
        + `,\n${ii + s_iident}[${this.capturepackdirect.map((c) => `"${c}"`).join(", ")}]`
        + `,\n${ii + s_iident}[${this.capturepackindirect.map((c) => `"${c}"`).join(", ")}]`
        + `\n${ii}}`;
    }
}

//abstract class for is test operations
abstract class TIRTestIsExpression extends TIRExpression {
    readonly exp: TIRExpression;

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, exp: TIRExpression, exprstr: string) {
        super(tag, sinfo, "Bool", exprstr);
        this.exp = exp;
    }

    bsqemit_ti(ii: string): string {
        return this.bsqemit_exp(ii) + `,\n${ii + s_iident}${this.exp.bsqemit(ii + s_iident)}`;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_ti(ii) + `\n${ii}}`;
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
    readonly oktype: TIRTypeKey;

    constructor(sinfo: SourceInfo, exp: TIRExpression, oktype: TIRTypeKey) {
        super(TIRExpressionTag.IsOkSpecialExpression, sinfo, exp, `${exp.expstr}?ok`);
        this.oktype = oktype;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_ti(ii) + `,\n${ii + s_iident}"${this.oktype}"\n${ii}}`;
    }
}

class TIRIsErrSpecialExpression extends TIRITestIsSpecialExpression {
    readonly errtype: TIRTypeKey;

    constructor(sinfo: SourceInfo, exp: TIRExpression, errtype: TIRTypeKey) {
        super(TIRExpressionTag.IsErrSpecialExpression, sinfo, exp, `${exp.expstr}?err`);
        this.errtype = errtype;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_ti(ii) + `,\n${ii + s_iident}"${this.errtype}"\n${ii}}`;
    }
}

//abstract class for is literal compare operations
abstract class TIRITestIsLiteralEqExpression extends TIRTestIsExpression {
    readonly literal: TIRLiteralValue;

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, exp: TIRExpression, literal: TIRLiteralValue, exprstr: string) {
        super(tag, sinfo, exp, exprstr);
        this.literal = literal;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_exp(ii) + `,\n${ii + s_iident}${this.literal.bsqemit(ii + s_iident)}`;
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

    bsqemit(ii: string): string {
        return this.bsqemit_exp_il(ii) + `, "${this.ttype}"}`;
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
    
    
    bsqemit_ae(ii: string): string {
        return this.bsqemit_exp(ii) + `,\n${ii + s_iident}${this.exp.bsqemit(ii + s_iident)}`;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_ae(ii) + `\n${ii}}`;
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

    bsqemit(ii: string): string {
        return this.bsqemit_ae(ii) + `,\n${ii + s_iident}"${this.etype}"\n${ii}}`;
    }
}

class TIRAsErrSpecialExpression extends TIRAsSpecialExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, oftype: TIRTypeKey) {
        super(TIRExpressionTag.AsErrSpecialExpression, sinfo, exp, oftype, `${exp.expstr}@err`);
    }

    
    bsqemit(ii: string): string {
        return this.bsqemit_ae(ii) + `,\n${ii + s_iident}"${this.etype}"\n${ii}}`;
    }
}

//abstract class for is literal as operations
abstract class TIRIAsLiteralEqExpression extends TIRAsExpression {
    readonly literal: TIRLiteralValue;

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, exp: TIRExpression, literal: TIRLiteralValue, oftype: TIRTypeKey, exprstr: string) {
        super(tag, sinfo, exp, oftype, exprstr);
        this.literal = literal;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_exp(ii) + `,\n${ii + s_iident}${this.literal.bsqemit(ii + s_iident)}`;
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

    bsqemit(ii: string): string {
        return this.bsqemit_exp_il(ii) + `, "${this.ttype}"}`;
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
    readonly fdecltype: TIRTypeKey;
    readonly thisarg: TIRExpression;
    readonly args: TIRExpression[]; 

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, tkey: TIRTypeKey, fname: string, fkey: TIRInvokeKey, fdecltype: TIRTypeKey, rtype: TIRTypeKey, thisarg: TIRExpression, args: TIRExpression[], exprstr: string) {
        super(tag, sinfo, rtype, exprstr);
        this.tkey = tkey;
        this.fname = fname;
        this.fkey = fkey;
        this.fdecltype = fdecltype;
        this.thisarg = thisarg;
        this.args = args;
    }

    bsqemit_mf(ii: string): string {
        const argl = this.args.map((arg) => arg.bsqemit(ii + s_iident));
        return this.bsqemit_exp(ii)
        + `,\n${ii + s_iident}"${this.tkey}"`
        + `,\n${ii + s_iident}"${this.fname}"`
        + `,\n${ii + s_iident}"${this.fkey}"`
        + `,\n${ii + s_iident}"${this.fdecltype}"`
        + `,\n${ii + s_iident}${this.thisarg.bsqemit(ii + s_iident)}`
        + `,\n${ii + s_iident}[${argl.length !== 0 ? ("\n" + ii + s_iident + s_iident + argl.join(",\n" + ii + s_iident + s_iident) + "\n" + ii + s_iident) : ""}]`;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_mf(ii) + `\n${ii}}`;
    }
}

class TIRCallMemberFunctionExpression extends TIRIMemberFunctionExpression {
    constructor(sinfo: SourceInfo, tkey: TIRTypeKey, fname: string, fkey: TIRInvokeKey, fdecltype: TIRTypeKey, rtype: TIRTypeKey, thisarg: TIRExpression, args: TIRExpression[]) {
        super(TIRExpressionTag.CallMemberFunctionExpression, sinfo, tkey, fname, fkey, fdecltype, rtype, thisarg, args, `${thisarg.expstr}.${fkey}(${args.map((arg) => arg.expstr).join(", ")})`);
    }
}

class TIRCallMemberFunctionDynamicExpression extends TIRIMemberFunctionExpression {
    constructor(sinfo: SourceInfo, tkey: TIRTypeKey, fname: string, declkey: TIRInvokeKey, fdecltype: TIRTypeKey, rtype: TIRTypeKey, thisarg: TIRExpression, args: TIRExpression[]) {
        super(TIRExpressionTag.CallMemberFunctionDynamicExpression, sinfo, tkey, fname, declkey, fdecltype, rtype, thisarg, args, `${thisarg.expstr}.${declkey}(${args.map((arg) => arg.expstr).join(", ")})`);
    }
}

class TIRCallMemberFunctionSelfRefExpression extends TIRIMemberFunctionExpression {
    readonly scidx: number;
    readonly thisref: string;

    constructor(sinfo: SourceInfo, scidx: number, tkey: TIRTypeKey, fname: string, fkey: TIRInvokeKey, fdecltype: TIRTypeKey, rtype: TIRTypeKey, thisref: string, thisarg: TIRExpression, args: TIRExpression[]) {
        super(TIRExpressionTag.CallMemberFunctionSelfRefExpression, sinfo, tkey, fname, fkey, fdecltype, rtype, thisarg, args, `ref ${thisref}.${fkey}(${args.map((arg) => arg.expstr).join(", ")})`);
        this.scidx = scidx;
        this.thisref = thisref;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_mf(ii) + `,\n${ii + s_iident}${this.scidx},\n${ii + s_iident}"${this.thisref}"\n${ii}}`;
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

    bsqemit_tf(ii: string): string {
        const argl = this.args.map((arg) => arg.bsqemit(ii + s_iident));
        return this.bsqemit_exp(ii)
        + `,\n${ii + s_iident}"${this.fname}"`
        + `,\n${ii + s_iident}"${this.fkey}"`
        + `,\n${ii + s_iident}"${this.tsktype}"`
        + `,\n${ii + s_iident}[${argl.length !== 0 ? ("\n" + ii + s_iident + s_iident + argl.join(",\n" + ii + s_iident + s_iident) + "\n" + ii + s_iident) : ""}]`;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_tf(ii) + `\n${ii}}`;
    }
}

class TIRCallMemberFunctionTaskExpression extends TIRFunctionTaskExpression {
    constructor(sinfo: SourceInfo, fname: string, fkey: TIRInvokeKey, rtype: TIRTypeKey, tsktype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.CallMemberFunctionTaskExpression, sinfo, fname, fkey, rtype, tsktype, args, `self.${fkey}(${args.map((arg) => arg.expstr).join(", ")})`);
    }
}

class TIRCallMemberFunctionTaskSelfRefExpression extends TIRFunctionTaskExpression {
    readonly scidx: number;

    constructor(sinfo: SourceInfo, scidx: number, fname: string, fkey: TIRInvokeKey, rtype: TIRTypeKey, tsktype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.CallMemberFunctionTaskSelfRefExpression, sinfo, fname, fkey, rtype, tsktype, args, `ref self.${fkey}(${args.map((arg) => arg.expstr).join(", ")})`);
        this.scidx = scidx;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_tf(ii) + `,\n${ii + s_iident}${this.scidx}\n${ii}}`;
    }
}

class TIRCallMemberActionExpression extends TIRFunctionTaskExpression {
    readonly scidx: number;

    constructor(sinfo: SourceInfo, scidx: number, fname: string, fkey: TIRInvokeKey, rtype: TIRTypeKey, tsktype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.CallMemberActionExpression, sinfo, fname, fkey, rtype, tsktype, args, `self.${fkey}(${args.map((arg) => arg.expstr).join(", ")})`);
        this.scidx = scidx;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_tf(ii) + `,\n${ii + s_iident}${this.scidx}\n${ii}}`;
    }
}

class TIRLiteralValue {
    readonly exp: TIRExpression;
    readonly litstr: string;
    
    constructor(exp: TIRExpression, litstr: string) {
        this.exp = exp
        this.litstr = litstr;
    }

    bsqemit(ii: string): string {
        return `{\n`
        + `${ii + s_iident}${this.exp.bsqemit(ii + s_iident)},\n`
        + `${ii + s_iident}"${this.litstr}"\n`
        + `${ii}}`;
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
    StoreToScratch = "StoreToScratch",
    VarRefAssignFromScratch = "VarRefAssignFromScratch",
    TaskRefAssignFromScratch = "TaskRefAssignFromScratch",

    CallWRefStatement = "CallWRefStatememt",
    CallStatementWTaskRef = "CallStatementWTaskRef",
    CallStatementWTaskAction = "CallStatementWTaskAction",

    VariableRetypeStatement = "VariableRetypeStatement",
    VariableSCRetypeStatement = "VariableSCRetypeStatement",
    ScratchSCStatement = "ScratchSCStatement",

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

    bsqemit_stmt(ii: string): string {
        return `TreeIR::${this.tag}{\n${ii + s_iident}${sinfo_bsqemit(this.sinfo)}`;
    }

    bsqemit_stmt_il(ii: string): string {
        return `TreeIR::${this.tag}{${sinfo_bsqemit(this.sinfo)}`;
    }

    abstract bsqemit(ii: string): string;
}

class TIRNopStatement extends TIRStatement {
    constructor(sinfo: SourceInfo) {
        super(TIRStatementTag.NopStatement, sinfo, "nop;");
    }

    bsqemit(ii: string): string {
        return this.bsqemit_stmt_il(ii) + `}`;
    }
}

class TIRAbortStatement extends TIRStatement {
    readonly msg: string;

    constructor(sinfo: SourceInfo, msg: string) {
        super(TIRStatementTag.AbortStatement, sinfo, `abort("${msg}");`);
        this.msg = msg;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_stmt_il(ii) + `, "${this.msg}", -1i}`;
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

    bsqemit(ii: string): string {
        return this.bsqemit_stmt(ii) + `,\n${ii + s_iident}${this.cond.bsqemit(ii + s_iident)},\n${ii + s_iident}"${this.msg}",\n${ii + s_iident}-1i\n${ii}}`;
    }
}

class TIRDebugStatement extends TIRStatement {
    readonly value: TIRExpression;

    constructor(sinfo: SourceInfo, value: TIRExpression) {
        super(TIRStatementTag.DebugStatement, sinfo, `__debug(${value.expstr});`);
        this.value = value;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_stmt(ii) + `,\n${ii + s_iident}${this.value.bsqemit(ii + s_iident)}\n${ii}}`;
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

    bsqemit(ii: string): string {
        return this.bsqemit_stmt_il(ii) + `, "${this.vname}", "${this.vtype}"}`;
    }
}

class TIRVarDeclareAndAssignStatement extends TIRStatement {
    readonly vname: string;
    readonly vtype: TIRTypeKey;
    readonly vexp: TIRExpression;
    readonly isConst: boolean;

    constructor(sinfo: SourceInfo, vname: string, vtype: TIRTypeKey, vexp: TIRExpression, isConst: boolean) {
        super(TIRStatementTag.VarDeclareAndAssignStatement, sinfo, `${isConst ? "let" : "var"} ${vname}: ${vtype} = ${vexp.expstr};`);
        this.vname = vname;
        this.vtype = vtype;
        this.vexp = vexp;
        this.isConst = isConst;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_stmt(ii) + `,\n${ii + s_iident}"${this.vname}",\n${ii + s_iident}"${this.vtype}",\n${ii + s_iident}${this.vexp.bsqemit(ii + s_iident)},\n${ii + s_iident}${this.isConst ? "true" : "false"}\n${ii}}`;
    }
}

class TIRVarAssignStatement extends TIRStatement {
    readonly vname: string;
    readonly vtype: TIRTypeKey;
    readonly vexp: TIRExpression;

    constructor(sinfo: SourceInfo, vname: string, vtype: TIRTypeKey, vexp: TIRExpression) {
        super(TIRStatementTag.VarAssignStatement, sinfo, `${vname} = ${vexp.expstr};`);
        this.vname = vname;
        this.vtype = vtype;
        this.vexp = vexp;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_stmt(ii) + `,\n${ii + s_iident}"${this.vname}",\n${ii + s_iident}"${this.vtype}",\n${ii + s_iident}${this.vexp.bsqemit(ii + s_iident)}\n${ii}}`;
    }
}

class TIRStoreToScratch extends TIRStatement {
    readonly exp: TIRExpression;
    readonly vtype: TIRTypeKey;
    readonly scidx: number;

    constructor(sinfo: SourceInfo, exp: TIRExpression, vtype: TIRTypeKey, scidx: number) {
        super(TIRStatementTag.StoreToScratch, sinfo, `$scratch<${scidx}, ${vtype}>[0] = ${exp.expstr};`);
        this.exp = exp;
        this.vtype = vtype;
        this.scidx = scidx;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_stmt(ii) + `,\n${ii + s_iident}${this.exp.bsqemit(ii + s_iident)},\n${ii + s_iident}"${this.vtype}",\n${ii + s_iident}${this.scidx}n\n${ii}}`;
    }
}

class TIRVarRefAssignFromScratch extends TIRStatement {
    readonly vname: string;
    readonly vtype: TIRTypeKey;
    readonly scidx: number;

    constructor(sinfo: SourceInfo, vname: string, vtype: TIRTypeKey, scidx: number) {
        super(TIRStatementTag.VarRefAssignFromScratch, sinfo, `${vname} = $$scratch<${scidx}, ${vtype}>[0];`);
        this.vname = vname;
        this.vtype = vtype;
        this.scidx = scidx;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_stmt(ii) + `,\n${ii + s_iident}"${this.vname}",\n${ii + s_iident}"${this.vtype}",\n${ii + s_iident}${this.scidx}n\n${ii}}`;
    }
}

class TIRTaskRefAssignFromScratch extends TIRStatement {
    readonly vtype: TIRTypeKey;
    readonly scidx: number;

    constructor(sinfo: SourceInfo, vtype: TIRTypeKey, scidx: number) {
        super(TIRStatementTag.TaskRefAssignFromScratch, sinfo, `self = $$scratch<${scidx}, ${vtype}>[0];`);
        this.vtype = vtype;
        this.scidx = scidx;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_stmt(ii) + `,\n${ii + s_iident}"${this.vtype}",\n${ii + s_iident}${this.scidx}n\n${ii}}`;
    }
}

abstract class TIRCallWRefStatementGeneral extends TIRStatement {
    readonly vexp: TIRExpression;
    readonly restype: TIRTypeKey;
    readonly reftype: TIRTypeKey;
    readonly sidx: number;
    //always stores to scratch location

    constructor(tag: TIRStatementTag, sinfo: SourceInfo, vexp: TIRExpression, restype: TIRTypeKey, reftype: TIRTypeKey, sidx: number) {
        super(tag, sinfo, `${vexp.expstr};`);
        this.vexp = vexp;
        this.restype = restype;
        this.reftype = reftype;
        this.sidx = sidx;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_stmt(ii) + `,\n${ii + s_iident}${this.vexp.bsqemit(ii + s_iident)},\n${ii + s_iident}"${this.restype}",\n${ii + s_iident}"${this.reftype}",\n${ii + s_iident}${this.sidx}n\n${ii}}`;
    }
}

class TIRCallStatementWRef extends TIRCallWRefStatementGeneral {
    constructor(sinfo: SourceInfo, vexp: TIRExpression, restype: TIRTypeKey, reftype: TIRTypeKey, sidx: number) {
        super(TIRStatementTag.CallWRefStatement, sinfo, vexp, restype, reftype, sidx);
    }
}

class TIRCallStatementWTaskRef extends TIRCallWRefStatementGeneral {
    constructor(sinfo: SourceInfo, vexp: TIRExpression, restype: TIRTypeKey, reftype: TIRTypeKey, sidx: number) {
        super(TIRStatementTag.CallStatementWTaskRef, sinfo, vexp, restype, reftype, sidx);
    }
}

class TIRCallStatementWAction extends TIRCallWRefStatementGeneral {
    constructor(sinfo: SourceInfo, vexp: TIRExpression, restype: TIRTypeKey, reftype: TIRTypeKey, sidx: number) {
        super(TIRStatementTag.CallStatementWTaskAction, sinfo, vexp, restype, reftype, sidx);
    }
}

class TIRVariableRetypeStatement extends TIRStatement {
    readonly vname: string;
    readonly origtype: TIRTypeKey;
    readonly newtype: TIRTypeKey;
    readonly asconv: TIRExpression;

    constructor(sinfo: SourceInfo, vname: string, origtype: TIRTypeKey, newtype: TIRTypeKey, asconv: TIRExpression) {
        super(TIRStatementTag.VariableRetypeStatement, sinfo, `${vname} = ${asconv.expstr}`);
        this.vname = vname;
        this.origtype = origtype;
        this.newtype = newtype;
        this.asconv = asconv;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_stmt(ii) + `,\n${ii + s_iident}"${this.vname}",\n${ii + s_iident}"${this.origtype}",\n${ii + s_iident}"${this.newtype}",\n${ii + s_iident}${this.asconv.bsqemit(ii + s_iident)}\n${ii}}`;
    }
}

class TIRVariableSCRetypeStatement extends TIRStatement {
    readonly vname: string;
    readonly origtype: TIRTypeKey;
    readonly test: TIRExpression;
    readonly asconv: TIRExpression;
    readonly resexp: TIRExpression;
    readonly binderinfo: [TIRExpression, string] | undefined;

    constructor(sinfo: SourceInfo, vname: string, origtype: TIRTypeKey, test: TIRExpression, asconv: TIRExpression, resexp: TIRExpression, binderinfo: [TIRExpression, string] | undefined) {
        super(TIRStatementTag.VariableSCRetypeStatement, sinfo, `${vname} ?? ${test.expstr} -- ${vname} = safe ${asconv.expstr} : ${resexp.expstr}`);
        this.vname = vname;
        this.origtype = origtype;
        this.test = test;
        this.asconv = asconv;
        this.resexp = resexp;
        this.binderinfo = binderinfo;
    }

    bsqemit(ii: string): string {
        let binfo: string = "none";
        if(this.binderinfo !== undefined) {
            binfo = `[\n${ii + s_iident + s_iident}${this.binderinfo[0].bsqemit(ii + s_iident + s_iident)},\n${ii + s_iident + s_iident}"${this.binderinfo[1]}"\n${ii + s_iident }]`;
        }

        return this.bsqemit_stmt(ii) 
            + `,\n${ii + s_iident}"${this.vname}"`
            + `,\n${ii + s_iident}"${this.origtype}"`
            + `,\n${ii + s_iident}${this.test.bsqemit(ii + s_iident)}`
            + `,\n${ii + s_iident}${this.asconv.bsqemit(ii + s_iident)}`
            + `,\n${ii + s_iident}${this.resexp.bsqemit(ii + s_iident)}`
            + `,\n${ii + s_iident}${binfo}`
            + `\n${ii}}`;
    }
}

class TIRScratchSCStatement extends TIRStatement {
    readonly sidx: number;
    readonly pos: number | undefined;
    readonly origtype: TIRTypeKey;
    readonly test: TIRExpression;
    readonly resexp: TIRExpression;
    readonly binderinfo: [TIRExpression, string] | undefined;

    constructor(sinfo: SourceInfo, sidx: number, pos: number | undefined, origtype: TIRTypeKey, test: TIRExpression, asconv: TIRExpression, resexp: TIRExpression, binderinfo: [TIRExpression, string] | undefined) {
        super(TIRStatementTag.ScratchSCStatement, sinfo, `$$scratch<${sidx}>[${pos !== undefined ? pos : -1}] ?? ${test.expstr} -- $$scratch<${sidx}>[${pos !== undefined ? pos : -1}] = safe ${asconv.expstr} : ${resexp.expstr}`);
        this.sidx = sidx;
        this.pos = pos;
        this.origtype = origtype;
        this.test = test;
        this.resexp = resexp;
        this.binderinfo = binderinfo;
    }

    bsqemit(ii: string): string {
        let binfo: string = "none";
        if(this.binderinfo !== undefined) {
            binfo = `[\n${ii + s_iident + s_iident}${this.binderinfo[0].bsqemit(ii + s_iident + s_iident)},\n${ii + s_iident + s_iident}"${this.binderinfo[1]}"\n${ii + s_iident }]`;
        }

        return this.bsqemit_stmt(ii) 
            + `,\n${ii + s_iident}${this.sidx}n`
            + `,\n${ii + s_iident}${this.pos !== undefined ? (this.pos.toString() + "n") : "none"}`
            + `,\n${ii + s_iident}"${this.origtype}"`
            + `,\n${ii + s_iident}${this.test.bsqemit(ii + s_iident)}`
            + `,\n${ii + s_iident}${this.resexp.bsqemit(ii + s_iident)}`
            + `,\n${ii + s_iident}${binfo}`
            + `\n${ii}}`;
    }
}

abstract class TIRReturnStatementGeneral extends TIRStatement {
    readonly value: TIRExpression;

    constructor(tag: TIRStatementTag, sinfo: SourceInfo, value: TIRExpression, stmtstr: string) {
        super(tag, sinfo, stmtstr);
        this.value = value;
    }

    bsqemit(ii: string): string {
        return this.bsqemit_stmt(ii) + `,\n${ii + s_iident}${this.value.bsqemit(ii + s_iident)}\n${ii}}`;
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
    readonly ifentry: {test: TIRExpression, value: TIRScopedBlockStatement, binderinfo: [TIRExpression, number, TIRExpression, string] | undefined, recasttypes: {vname: string, cast: TIRExpression}[]};
    readonly elifentries: {test: TIRExpression, value: TIRScopedBlockStatement, binderinfo: [TIRExpression, number, TIRExpression, string] | undefined, recasttypes: {vname: string, cast: TIRExpression}[]}[];
    readonly elseentry: {value: TIRScopedBlockStatement, binderinfo: [TIRExpression, number, TIRExpression, string] | undefined, recasttypes: {vname: string, cast: TIRExpression}[]};

    constructor(sinfo: SourceInfo, ifentry: {test: TIRExpression, value: TIRScopedBlockStatement, binderinfo: [TIRExpression, number, TIRExpression, string] | undefined, recasttypes: {vname: string, cast: TIRExpression}[]}, elifentries: {test: TIRExpression, value: TIRScopedBlockStatement, binderinfo: [TIRExpression, number, TIRExpression, string] | undefined, recasttypes: {vname: string, cast: TIRExpression}[]}[], elseentry: {value: TIRScopedBlockStatement, binderinfo: [TIRExpression, number, TIRExpression, string] | undefined, recasttypes: {vname: string, cast: TIRExpression}[]}) {
        super(TIRStatementTag.IfStatement, sinfo, `if(${ifentry.test.expstr}) ${ifentry.value.stmtstr} ${elifentries.map((efi) => `elif(${efi.test.expstr}) ${efi.value.stmtstr}`)} else ${elseentry.value.stmtstr}`);
        this.ifentry = ifentry;
        this.elifentries = elifentries;
        this.elseentry = elseentry;
    }

    private static bsqemit_binder(ii: string, bb: [TIRExpression, number, TIRExpression, string] | undefined): string {
        if(bb === undefined) {
            return "none";
        }
        else {
            const iident = ii + s_iident;
            return `[`
            + `\n${iident}${bb[0].bsqemit(iident + s_iident)}`
            + `,\n${iident}${bb[1]}n`
            + `,\n${iident}${bb[2].bsqemit(iident + s_iident)}`
            + `,\n${iident}"${bb[3]}"`
            + `\n${ii}]`;
        }
    }
    private static bsqemit_recast(ii: string, rc: {vname: string, cast: TIRExpression}[]): string {
        if(rc.length === 0) {
            return "[]";
        }
        else {
            const iident = ii + s_iident;

            const rcc = rc.map((r) => `{`
                + `\n${iident + s_iident}vname=${r.vname}}`
                + `,\n${iident + s_iident}cast=${r.cast.bsqemit(iident + s_iident)}`
                + `\n${iident}}`
            );

            return `[\n${iident}${rcc.join(`,\n${iident}`)}\n${ii}]`;
        }
    }
    private bsqemit_ifentry(ii: string): string {
        const iident = ii + s_iident;

        return `{`
        + `\n${iident}etest=${this.ifentry.test.bsqemit(iident + s_iident)}`
        + `,\n${iident}value=${this.ifentry.value.bsqemit(iident + s_iident)}`
        + `,\n${iident}binderinfo=${TIRIfStatement.bsqemit_binder(iident + s_iident, this.ifentry.binderinfo)}`
        + `,\n${iident}recasttypes=${TIRIfStatement.bsqemit_recast(iident + s_iident, this.ifentry.recasttypes)}`
        + `\n${ii}}`;
    }
    private static bsqemit_elifentry(ii: string, entry: {test: TIRExpression, value: TIRScopedBlockStatement, binderinfo: [TIRExpression, number, TIRExpression, string] | undefined, recasttypes: {vname: string, cast: TIRExpression}[]}): string {
        const iident = ii + s_iident;

        return `{`
        + `\n${iident}etest=${entry.test.bsqemit(iident + s_iident)}`
        + `,\n${iident}value=${entry.value.bsqemit(iident + s_iident)}`
        + `,\n${iident}binderinfo=${TIRIfStatement.bsqemit_binder(iident + s_iident, entry.binderinfo)}`
        + `,\n${iident}recasttypes=${TIRIfStatement.bsqemit_recast(iident + s_iident, entry.recasttypes)}`
        + `\n${ii}}`;
    }
    private bsqemit_elifentries(ii: string): string {
        const iident = ii + s_iident;

        return `[`
        + this.elifentries.map((e) => TIRIfStatement.bsqemit_elifentry(iident + s_iident, e)).join(`,\n${iident}`)
        + `\n${ii}]`;
    }
    private bsqemit_elseentry(ii: string): string {
        const iident = ii + s_iident;

        return `{`
        + `${iident}value=${this.elseentry.value.bsqemit(iident + s_iident)}`
        + `,\n${iident}binderinfo=${TIRIfStatement.bsqemit_binder(iident + s_iident, this.elseentry.binderinfo)}`
        + `,\n${iident}recasttypes=${TIRIfStatement.bsqemit_recast(iident + s_iident, this.elseentry.recasttypes)}`
        + `\n${ii + s_iident}}`;
    }

    bsqemit(ii: string): string {
        const iident = ii + s_iident;

        const ifes = this.bsqemit_ifentry(iident);
        const elifes = this.bsqemit_elifentries(iident);
        const ee = this.bsqemit_elseentry(iident);

        return this.bsqemit_stmt(ii)
        + `,\n${iident}${ifes},\n${iident}${elifes},\n${iident}${ee}\n${ii}}`
        + `\n${ii}}`;
    }
}

class TIRSwitchStatement extends TIRStatement {
    readonly exp: TIRExpression;
    readonly scratchidx: number;
    readonly clauses: {match: TIRExpression, value: TIRScopedBlockStatement, binderinfo: [TIRExpression, string] | undefined, recasttypes: {vname: string, cast: TIRExpression}[]}[];
    readonly edefault: {value: TIRScopedBlockStatement, binderinfo: [TIRExpression, string] | undefined, recasttypes: {vname: string, cast: TIRExpression}[]} | undefined;
    readonly isexhaustive: boolean;

    constructor(sinfo: SourceInfo, exp: TIRExpression, scratchidx: number, clauses: {match: TIRExpression, value: TIRScopedBlockStatement, binderinfo: [TIRExpression, string] | undefined, recasttypes: {vname: string, cast: TIRExpression}[]}[], edefault: {value: TIRScopedBlockStatement, binderinfo: [TIRExpression, string] | undefined, recasttypes: {vname: string, cast: TIRExpression}[]} | undefined, isexhaustive: boolean) {
        super(TIRStatementTag.SwitchStatement, sinfo, `switch(${exp.expstr}) ${clauses.map((ci) => `(${ci.match.expstr} => ${ci.value.stmtstr})`)}${edefault !== undefined ? "(_ => " + edefault.value.stmtstr : ""}`);
        this.exp = exp;
        this.scratchidx = scratchidx;
        this.clauses = clauses;
        this.edefault = edefault;
        this.isexhaustive = isexhaustive;
    }

    private static bsqemit_binder(ii: string, bb: [TIRExpression, string] | undefined): string {
        if(bb === undefined) {
            return "none";
        }
        else {
            const iident = ii + s_iident;
            return `[`
            + `\n${iident}${bb[0].bsqemit(iident + s_iident)}`
            + `,\n${iident}"${bb[1]}"`
            + `\n${ii}]`;
        }
    }
    private static bsqemit_recast(ii: string, rc: {vname: string, cast: TIRExpression}[]): string {
        if(rc.length === 0) {
            return "[]";
        }
        else {
            const iident = ii + s_iident;

            const rcc = rc.map((r) => `{`
                + `\n${iident + s_iident}vname=${r.vname}}`
                + `,\n${iident + s_iident}cast=${r.cast.bsqemit(iident + s_iident)}`
                + `\n${iident}}`
            );

            return `[\n${iident}${rcc.join(`,\n${iident}`)}\n${ii}]`;
        }
    }
    private static bsqemit_clauseentry(ii: string, entry: {match: TIRExpression, value: TIRScopedBlockStatement, binderinfo: [TIRExpression, string] | undefined, recasttypes: {vname: string, cast: TIRExpression}[]}): string {
        const iident = ii + s_iident;

        return `{`
        + `\n${iident}ematch=${entry.match.bsqemit(iident + s_iident)}`
        + `,\n${iident}value=${entry.value.bsqemit(iident + s_iident)}`
        + `,\n${iident}binderinfo=${TIRSwitchStatement.bsqemit_binder(iident + s_iident, entry.binderinfo)}`
        + `,\n${iident}recasttypes=${TIRSwitchStatement.bsqemit_recast(iident + s_iident, entry.recasttypes)}`
        + `\n${ii}}`;
    }
    private bsqemit_clauses(ii: string): string {
        const iident = ii + s_iident;

        return `[`
        + this.clauses.map((e) => TIRSwitchStatement.bsqemit_clauseentry(iident + s_iident, e)).join(`,\n${iident}`)
        + `\n${ii}]`;
    }
    private bsqemit_default(ii: string): string {
        const iident = ii + s_iident;
        if(this.edefault === undefined) {
            return "none";
        }
        else {
            return `{`
                + `${iident}value=${this.edefault.value.bsqemit(iident + s_iident)}`
                + `,\n${iident}binderinfo=${TIRSwitchStatement.bsqemit_binder(iident + s_iident, this.edefault.binderinfo)}`
                + `\n${ii + s_iident}}`;
        }
    }

    bsqemit(ii: string): string {
        const iident = ii + s_iident;

        const cles = this.bsqemit_clauses(iident);
        const dd = this.bsqemit_default(iident);

        return this.bsqemit_stmt(ii)
        + `${this.exp.bsqemit(iident)},\n${iident}${this.scratchidx}`
        + `,\n${iident}${cles},\n${iident}${dd}`
        + `,\n${iident}${this.isexhaustive}`
        + `\n${ii}}`;
    }
}

class TIRMatchStatement extends TIRStatement {
    readonly exp: TIRExpression;
    readonly scratchidx: number;
    readonly clauses: {match: TIRExpression, value: TIRScopedBlockStatement, binderinfo: [TIRExpression, string] | undefined, recasttypes: {vname: string, cast: TIRExpression}[]}[];
    readonly edefault: {value: TIRScopedBlockStatement, binderinfo: [TIRExpression, string] | undefined, recasttypes: {vname: string, cast: TIRExpression}[]} | undefined;
    readonly isexhaustive: boolean;

    constructor(sinfo: SourceInfo, exp: TIRExpression, scratchidx: number, clauses: {match: TIRExpression, value: TIRScopedBlockStatement, binderinfo: [TIRExpression, string] | undefined, recasttypes: {vname: string, cast: TIRExpression}[]}[], edefault: {value: TIRScopedBlockStatement, binderinfo: [TIRExpression, string] | undefined, recasttypes: {vname: string, cast: TIRExpression}[]} | undefined, isexhaustive: boolean) {
        super(TIRStatementTag.MatchStatement, sinfo, `match(${exp.expstr}) ${clauses.map((ci) => `(${ci.match.expstr} => ${ci.value.stmtstr})`)}${edefault !== undefined ? "(_ => " + edefault.value.stmtstr : ""}`);
        this.exp = exp;
        this.scratchidx = scratchidx;
        this.clauses = clauses;
        this.edefault = edefault;
        this.isexhaustive = isexhaustive;
    }

    private static bsqemit_binder(ii: string, bb: [TIRExpression, string] | undefined): string {
        if(bb === undefined) {
            return "none";
        }
        else {
            const iident = ii + s_iident;
            return `[`
            + `\n${iident}${bb[0].bsqemit(iident + s_iident)}`
            + `,\n${iident}"${bb[1]}"`
            + `\n${ii}]`;
        }
    }
    private static bsqemit_recast(ii: string, rc: {vname: string, cast: TIRExpression}[]): string {
        if(rc.length === 0) {
            return "[]";
        }
        else {
            const iident = ii + s_iident;

            const rcc = rc.map((r) => `{`
                + `\n${iident + s_iident}vname=${r.vname}}`
                + `,\n${iident + s_iident}cast=${r.cast.bsqemit(iident + s_iident)}`
                + `\n${iident}}`
            );

            return `[\n${iident}${rcc.join(`,\n${iident}`)}\n${ii}]`;
        }
    }
    private static bsqemit_clauseentry(ii: string, entry: {match: TIRExpression, value: TIRScopedBlockStatement, binderinfo: [TIRExpression, string] | undefined, recasttypes: {vname: string, cast: TIRExpression}[]}): string {
        const iident = ii + s_iident;

        return `{`
        + `\n${iident}ematch=${entry.match.bsqemit(iident + s_iident)}`
        + `,\n${iident}value=${entry.value.bsqemit(iident + s_iident)}`
        + `,\n${iident}binderinfo=${TIRMatchStatement.bsqemit_binder(iident + s_iident, entry.binderinfo)}`
        + `,\n${iident}recasttypes=${TIRMatchStatement.bsqemit_recast(iident + s_iident, entry.recasttypes)}`
        + `\n${ii}}`;
    }
    private bsqemit_clauses(ii: string): string {
        const iident = ii + s_iident;

        return `[`
        + this.clauses.map((e) => TIRMatchStatement.bsqemit_clauseentry(iident + s_iident, e)).join(`,\n${iident}`)
        + `\n${ii}]`;
    }
    private bsqemit_default(ii: string): string {
        const iident = ii + s_iident;
        if(this.edefault === undefined) {
            return "none";
        }
        else {
            return `{`
                + `${iident}value=${this.edefault.value.bsqemit(iident + s_iident)}`
                + `,\n${iident}binderinfo=${TIRMatchStatement.bsqemit_binder(iident + s_iident, this.edefault.binderinfo)}`
                + `\n${ii + s_iident}}`;
        }
    }

    bsqemit(ii: string): string {
        const iident = ii + s_iident;

        const cles = this.bsqemit_clauses(iident);
        const dd = this.bsqemit_default(iident);

        return this.bsqemit_stmt(ii)
        + `${this.exp.bsqemit(iident)},\n${iident}${this.scratchidx}`
        + `,\n${iident}${cles},\n${iident}${dd}`
        + `,\n${iident}${this.isexhaustive}`
        + `\n${ii}}`;
    }
}

class TIREnvironmentFreshStatement extends TIRStatement {
    readonly assigns: {keyname: string, valexp: [TIRTypeKey, TIRExpression]}[];

    constructor(sinfo: SourceInfo, assigns: {keyname: string, valexp: [TIRTypeKey, TIRExpression]}[]) {
        super(TIRStatementTag.EnvironmentFreshStatement, sinfo, `env{${assigns.map((asgn) => asgn.keyname + ": " + asgn.valexp[0] + "=" + asgn.valexp[1].expstr).join(", ")}};`);
        this.assigns = assigns;
    }

    bsqemit(ii: string): string {
        return "[NOT SUPPORTED TIREnvironmentFreshStatement]";
    }
}

class TIREnvironmentSetStatement extends TIRStatement {
    readonly assigns: {keyname: string, valexp: [TIRTypeKey, TIRExpression] | undefined}[];

    constructor(sinfo: SourceInfo, assigns: {keyname: string, valexp: [TIRTypeKey, TIRExpression] | undefined}[]) {
        super(TIRStatementTag.EnvironmentFreshStatement, sinfo, `env[${assigns.map((asgn) => asgn.keyname + (asgn.valexp !== undefined ? (": " + asgn.valexp[0] + "=" + asgn.valexp[1].expstr) : "=_")).join(", ")}];`);
        this.assigns = assigns;
    }

    bsqemit(ii: string): string {
        return "[NOT SUPPORTED TIREnvironmentSetStatement]";
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

    bsqemit(ii: string): string {
        return "[NOT SUPPORTED TIREnvironmentSetStatementBracket]";
    }
}

abstract class TIRTaskExecStatment extends TIRStatement {
    readonly isdefine: boolean;
    readonly isconst: boolean;

    constructor(tag: TIRStatementTag, sinfo: SourceInfo, isdefine: boolean, isconst: boolean, stmtstr: string) {
        super(tag, sinfo, (isdefine ? (isconst ? "let " : "var ") : "") + stmtstr);
        this.isdefine= isdefine;
        this.isconst = isconst;
    }

    bsqemit(ii: string): string {
        return "[NOT SUPPORTED TIRTaskExecStatment]]"
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
}

class TIRTaskMultiStatement extends TIRTaskExecStatment {
    readonly vtrgts: {name: string, vtype: TIRTypeKey}[];
    readonly tasks: {task: TIRTypeKey, targs: {argn: string, argv: TIRExpression}[], argtype: TIRTypeKey, consargtype: TIRTypeKey, argexp: TIRExpression}[];

    constructor(sinfo: SourceInfo, isdefine: boolean, isconst: boolean, vtrgts: {name: string, vtype: TIRTypeKey}[], tasks: {task: TIRTypeKey, targs: {argn: string, argv: TIRExpression}[], argtype: TIRTypeKey, consargtype: TIRTypeKey, argexp: TIRExpression}[]) {
        super(TIRStatementTag.TaskMultiStatement, sinfo, isdefine, isconst, `${vtrgts.map((vv) => vv.name).join(", ")} = Task::run<${tasks.map((tt) => tt.task).join(", ")}>(${tasks.map((tt) => tt.argexp.expstr).join(", ")})`);
        this.vtrgts = vtrgts;
        this.tasks = tasks;
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

    bsqemit(ii: string): string {
        return "[NOT SUPPORTED TIRTaskSetSelfFieldStatement]";
    }
}

class TIRLoggerEmitStatement extends TIRStatement {
    readonly level: LoggerLevel;
    readonly fmt: {ns: string, keyname: string};
    readonly args: TIRExpression[];

    constructor(sinfo: SourceInfo, level: LoggerLevel, fmt: {ns: string, keyname: string}, args: TIRExpression[]) {
        super(TIRStatementTag.LoggerEmitStatement, sinfo, `Log::${logLevelName(level)}(${fmt.ns}::${fmt.keyname}${args.length !== 0 ? ", " : ""}${args.map((arg) => arg.expstr).join(", ")})`);
        this.level = level;
        this.fmt = fmt;
        this.args = args;
    }

    bsqemit(ii: string): string {
        return "[NOT SUPPORTED TIRTaskSetSelfFieldStatement]";
    }
}

class TIRLoggerEmitConditionalStatement extends TIRStatement {
    readonly level: LoggerLevel;
    readonly fmt: {ns: string, keyname: string};
    readonly cond: TIRExpression;
    readonly args: TIRExpression[];

    constructor(sinfo: SourceInfo, level: LoggerLevel, cond: TIRExpression, fmt: {ns: string, keyname: string}, args: TIRExpression[]) {
        super(TIRStatementTag.LoggerEmitStatement, sinfo, `Log::${logLevelName(level)}If(${cond.expstr}, ${fmt.ns}::${fmt.keyname}${args.length !== 0 ? ", " : ""}${args.map((arg) => arg.expstr).join(", ")})`);
        this.level = level;
        this.fmt = fmt;
        this.cond = cond;
        this.args = args;
    }

    bsqemit(ii: string): string {
        return "[NOT SUPPORTED TIRTaskSetSelfFieldStatement]";
    }
}

class TIRLoggerSetPrefixStatement extends TIRStatement {
    readonly fmt: {ns: string, keyname: string};
    readonly args: TIRExpression[];
    readonly block: TIRScopedBlockStatement | TIRUnscopedBlockStatement;

    constructor(sinfo: SourceInfo, fmt: {ns: string, keyname: string}, block: TIRScopedBlockStatement | TIRUnscopedBlockStatement, args: TIRExpression[]) {
        super(TIRStatementTag.LoggerSetPrefixStatement, sinfo, `Logger::scope(${fmt.ns}::${fmt.keyname}${args.length !== 0 ? ", " : ""}${args.map((arg) => arg.expstr).join(", ")}) ${block.stmtstr}`);
        this.fmt = fmt;
        this.args = args;
        this.block = block;
    }

    bsqemit(ii: string): string {
        return "[NOT SUPPORTED TIRTaskSetSelfFieldStatement]";
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

    bsqemit(ii: string): string {
        const ops = this.ops.length !== 0 ? ("[" + this.ops.map((op) => op.bsqemit(ii + s_iident + s_iident)).join(",\n" + ii + s_iident + s_iident) + ii + s_iident + "]") : "[]";
        return `TreeIR::BlockStatement{\n${ii + s_iident}${ops},\n${ii + s_iident}${this.isterminal}\n${ii}}`;
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
    TIRBSQONLiteralExpression,
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
    TIRVariableRetypeStatement, TIRVariableSCRetypeStatement, TIRScratchSCStatement,
    TIRCallMemberFunctionExpression, TIRCallMemberFunctionDynamicExpression, TIRCallMemberFunctionSelfRefExpression,
    TIRCallMemberFunctionTaskExpression, TIRCallMemberFunctionTaskSelfRefExpression, TIRCallMemberActionExpression,
    TIRLiteralValue,
    TIRStatementTag,
    TIRStatement,
    TIRNopStatement, TIRAbortStatement, TIRAssertCheckStatement, TIRDebugStatement,
    TIRVarDeclareStatement, TIRVarDeclareAndAssignStatement, TIRVarAssignStatement,
    TIRStoreToScratch, TIRVarRefAssignFromScratch, TIRTaskRefAssignFromScratch,
    TIRCallStatementWRef, TIRCallStatementWTaskRef, TIRCallStatementWAction,
    TIRReturnStatement, TIRReturnStatementWRef, TIRReturnStatementWTaskRef, TIRReturnStatementWAction,
    TIRIfStatement, TIRSwitchStatement, TIRMatchStatement,
    TIREnvironmentFreshStatement, TIREnvironmentSetStatement, TIREnvironmentSetStatementBracket,
    TIRTaskRunStatement, TIRTaskMultiStatement, TIRTaskDashStatement, TIRTaskAllStatement, TIRTaskRaceStatement,
    TIRTaskSetSelfFieldStatement,
    TIRLoggerEmitStatement, TIRLoggerEmitConditionalStatement, TIRLoggerSetPrefixStatement,
    TIRBlockStatement, TIRUnscopedBlockStatement, TIRScopedBlockStatement
};
