
import { TIRCodePack, TIRFieldKey, TIRInvokeKey, TIRTypeKey } from "./tir_assembly";

import { LoggerLevel, logLevelName, SourceInfo } from "../build_decls";
import { BSQRegex } from "../bsqregex";

function assert(cond: boolean, msg?: string) {
    if(!cond) {
        throw new Error((msg || "error")  + " -- body_emitter.ts");
    }
} 

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

    bsqemit_exp(): any {
        return {sinfo: this.sinfo.bsqemit(), etype: this.etype};
    }

    abstract bsqemit(): any;

    static bsqparse(jv: any): TIRExpression {
        if(jv[0] === "TreeIR::LiteralNoneExpression") {
            return TIRLiteralNoneExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::LiteralNothingExpression") {
            return TIRLiteralNothingExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::LiteralBoolExpression") {
            return TIRLiteralBoolExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::LiteralIntegralExpression") {
            return TIRLiteralIntegralExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::LiteralRationalExpression") {
            return TIRLiteralRationalExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::LiteralFloatPointExpression") {
            return TIRLiteralFloatPointExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::LiteralRegexExpression") {
            return TIRLiteralRegexExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::LiteralStringExpression") {
            return TIRLiteralStringExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::LiteralASCIIStringExpression") {
            return TIRLiteralASCIIStringExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::LiteralTypedStringExpression") {
            return TIRLiteralTypedStringExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::LiteralASCIITypedStringExpression") {
            return TIRLiteralASCIITypedStringExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::LiteralTemplateStringExpression") {
            return TIRLiteralTemplateStringExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::LiteralASCIITemplateStringExpression") {
            return TIRLiteralASCIITemplateStringExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::LiteralTypedPrimitiveDirectExpression") {
            return TIRLiteralTypedPrimitiveDirectExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::LiteralTypedPrimitiveConstructorExpression") {
            return TIRLiteralTypedPrimitiveConstructorExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::AccessEnvValueExpression") {
            return TIRAccessEnvValueExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::AccessNamespaceConstantExpression") {
            return TIRAccessNamespaceConstantExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::AccessConstMemberFieldExpression") {
            return TIRAccessConstMemberFieldExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::AccessVariableExpression") {
            return TIRAccessVariableExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::AccessCapturedVariableExpression") {
            return TIRAccessCapturedVariableExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::AccessScratchSingleValueExpression") {
            return TIRAccessScratchSingleValueExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::AccessScratchIndexExpression") {
            return TIRAccessScratchIndexExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::LoadIndexExpression") {
            return TIRLoadIndexExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::LoadPropertyExpression") {
            return TIRLoadPropertyExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::LoadFieldExpression") {
            return TIRLoadFieldExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::LoadFieldVirtualExpression") {
            return TIRLoadFieldVirtualExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::ConstructorPrimaryDirectExpression") {
            return TIRConstructorPrimaryDirectExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::ConstructorPrimaryCheckExpression") {
            return TIRConstructorPrimaryCheckExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::ConstructorTupleExpression") {
            return TIRConstructorTupleExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::ConstructorRecordExpression") {
            return TIRConstructorRecordExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::ConstructorListExpression") {
            return TIRConstructorListExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::ConstructorMapExpression") {
            return TIRConstructorMapExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::CodePackInvokeExpression") {
            return TIRCodePackInvokeExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::ResultOkConstructorExpression") {
            return TIRResultOkConstructorExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::ResultErrConstructorExpression") {
            return TIRResultErrConstructorExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::SomethingConstructorExpression") {
            return TIRSomethingConstructorExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::TypedeclDirectExpression") {
            return TIRTypedeclDirectExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::TypedeclConstructorExpression") {
            return TIRTypedeclConstructorExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::CallNamespaceFunctionExpression") {
            return TIRCallNamespaceFunctionExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::CallNamespaceOperatorExpression") {
            return TIRCallNamespaceOperatorExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::CallStaticFunctionExpression") {
            return TIRCallStaticFunctionExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::LogicActionAndExpression") {
            return TIRLogicActionAndExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::LogicActionOrExpression") {
            return TIRLogicActionOrExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::PrefixNotExpression") {
            return TIRPrefixNotExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::PrefixNegateExpression") {
            return TIRPrefixNegateExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::BinAddExpression") {
            return TIRBinAddExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::BinSubExpression") {
            return TIRBinSubExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::BinMultExpression") {
            return TIRBinMultExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::BinDivExpression") {
            return TIRBinDivExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::BinKeyEqBothUniqueExpression") {
            return TIRBinKeyEqBothUniqueExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::BinKeyEqOneUniqueExpression") {
            return TIRBinKeyEqOneUniqueExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::BinKeyEqGeneralExpression") {
            return TIRBinKeyEqGeneralExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::BinKeyNeqBothUniqueExpression") {
            return TIRBinKeyNeqBothUniqueExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::BinKeyNeqOneUniqueExpression") {
            return TIRBinKeyNeqOneUniqueExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::BinKeyNeqGeneralExpression") {
            return TIRBinKeyNeqGeneralExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::BinKeyUniqueLessExpression") {
            return TIRBinKeyUniqueLessExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::BinKeyGeneralLessExpression") {
            return TIRBinKeyGeneralLessExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::NumericEqExpression") {
            return TIRNumericEqExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::NumericNeqExpression") {
            return TIRNumericNeqExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::NumericLessExpression") {
            return TIRNumericLessExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::NumericLessEqExpression") {
            return TIRNumericLessEqExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::NumericGreaterExpression") {
            return TIRNumericGreaterExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::NumericGreaterEqExpression") {
            return TIRNumericGreaterEqExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::BinLogicAndExpression") {
            return TIRBinLogicAndExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::BinLogicOrExpression") {
            return TIRBinLogicOrExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::BinLogicImpliesExpression") {
            return TIRBinLogicImpliesExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::MapEntryConstructorExpression") {
            return TIRMapEntryConstructorExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::IfExpression") {
            return TIRIfExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::SwitchExpression") {
            return TIRSwitchExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::MatchExpression") {
            return TIRMatchExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::TaskSelfFieldExpression") {
            return TIRTaskSelfFieldExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::TaskSelfControlExpression") {
            return TIRTaskSelfControlExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::TaskGetIDExpression") {
            return TIRTaskGetIDExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::CoerceSafeExpression") {
            return TIRCoerceSafeExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::InjectExpression") {
            return TIRInjectExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::ExtractExpression") {
            return TIRExtractExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::CreateCodePackExpression") {
            return TIRCreateCodePackExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::IsNoneSpecialExpression") {
            return TIRIsNoneSpecialExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::IsSomeSpecialExpression") {
            return TIRIsSomeSpecialExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::IsNothingSpecialExpression") {
            return TIRIsNothingSpecialExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::IsSomethingSpecialExpression") {
            return TIRIsSomethingSpecialExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::IsOkSpecialExpression") {
            return TIRIsOkSpecialExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::IsErrSpecialExpression") {
            return TIRIsErrSpecialExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::IsEqualToLiteralExpression") {
            return TIRIsEqualToLiteralExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::IsNotEqualToLiteralExpression") {
            return TIRIsNotEqualToLiteralExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::IsTypeExpression") {
            return TIRIsTypeExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::IsNotTypeExpression") {
            return TIRIsNotTypeExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::IsSubTypeExpression") {
            return TIRIsSubTypeExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::IsNotSubTypeExpression") {
            return TIRIsNotSubTypeExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::AsNoneSpecialExpression") {
            return TIRAsNoneSpecialExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::AsSomeSpecialExpression") {
            return TIRAsSomeSpecialExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::AsNothingSpecialExpression") {
            return TIRAsNothingSpecialExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::AsSomethingSpecialExpression") {
            return TIRAsSomethingSpecialExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::AsOkSpecialExpression") {
            return TIRAsOkSpecialExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::AsErrSpecialExpression") {
            return TIRAsErrSpecialExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::AsEqualToLiteralExpression") {
            return TIRAsEqualToLiteralExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::AsNotEqualToLiteralExpression") {
            return TIRAsNotEqualToLiteralExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::AsTypeExpression") {
            return TIRAsTypeExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::AsNotTypeExpression") {
            return TIRAsNotTypeExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::AsSubTypeExpression") {
            return TIRAsSubTypeExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::AsNotSubTypeExpression") {
            return TIRAsNotSubTypeExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::CallMemberFunctionExpression") {
            return TIRCallMemberFunctionExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::CallMemberFunctionDynamicExpression") {
            return TIRCallMemberFunctionDynamicExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::CallMemberFunctionSelfRefExpression") {
            return TIRCallMemberFunctionSelfRefExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::CallMemberFunctionTaskExpression") {
            return TIRCallMemberFunctionTaskExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::CallMemberFunctionTaskSelfRefExpression") {
            return TIRCallMemberFunctionTaskSelfRefExpression.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::CallMemberActionExpression") {
            return TIRCallMemberActionExpression.bsqparse(jv);
        }
        else {
            assert(false, "Unknown TIRExpression tag: " + jv[0]);
            return (undefined as any) as TIRExpression;
        }
    }
}

class TIRInvalidExpression extends TIRExpression {
    constructor(sinfo: SourceInfo, etype: TIRTypeKey) {
        super(TIRExpressionTag.InvalidExpresion, sinfo, etype, "[INVALID]");
    }

    bsqemit(): any {
        return ["TreeIR::InvalidExpression", this.bsqemit_exp()];
    }
    static bsqparse(jv: any): TIRInvalidExpression {
        return new TIRInvalidExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].etype);
    }
}

class TIRLiteralNoneExpression extends TIRExpression {
    constructor(sinfo: SourceInfo) {
        super(TIRExpressionTag.LiteralNoneExpression, sinfo, "None", "none");
    }

    bsqemit(): any {
        return ["TreeIR::LiteralNoneExpression", this.bsqemit_exp()];
    }
    static bsqparse(jv: any): TIRLiteralNoneExpression {
        return new TIRLiteralNoneExpression(SourceInfo.bsqparse(jv[1].sinfo));
    }
}

class TIRLiteralNothingExpression extends TIRExpression {
    constructor(sinfo: SourceInfo) {
        super(TIRExpressionTag.LiteralNothingExpression, sinfo, "Nothing", "nothing");
    }

    bsqemit(): any {
        return ["TreeIR::LiteralNothingExpression", this.bsqemit_exp()];
    }
    static bsqparse(jv: any): TIRLiteralNothingExpression {
        return new TIRLiteralNothingExpression(SourceInfo.bsqparse(jv[1].sinfo));
    }
}

class TIRLiteralBoolExpression extends TIRExpression {
    readonly value: boolean;

    constructor(sinfo: SourceInfo, value: boolean) {
        super(TIRExpressionTag.LiteralBoolExpression, sinfo, "Bool", value ? "true" : "false");
        this.value = value;
    }

    bsqemit(): any {
        return ["TreeIR::LiteralBoolExpression", {...this.bsqemit_exp(), value: this.value}];
    }
    static bsqparse(jv: any): TIRLiteralBoolExpression {
        return new TIRLiteralBoolExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].value);
    }
}

class TIRLiteralIntegralExpression extends TIRExpression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string, itype: TIRTypeKey) {
        super(TIRExpressionTag.LiteralIntegralExpression, sinfo, itype, value);
        this.value = value;
    }

    bsqemit(): any {
        return ["TreeIR::LiteralIntegralExpression", {...this.bsqemit_exp(), value: this.value}];
    }
    static bsqparse(jv: any): TIRLiteralIntegralExpression {
        return new TIRLiteralIntegralExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].value, jv[1].etype);
    }
}

class TIRLiteralRationalExpression extends TIRExpression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string) {
        super(TIRExpressionTag.LiteralRationalExpression, sinfo, "Rational", value);
        this.value = value;
    }

    bsqemit(): any {
        return ["TreeIR::LiteralRationalExpression", {...this.bsqemit_exp(), value: this.value}];
    }
    static bsqparse(jv: any): TIRLiteralRationalExpression {
        return new TIRLiteralRationalExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].value);
    }
}

class TIRLiteralFloatPointExpression extends TIRExpression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string, fptype: TIRTypeKey) {
        super(TIRExpressionTag.LiteralFloatPointExpression, sinfo, fptype, value);
        this.value = value;
    }

    bsqemit(): any {
        return ["TreeIR::LiteralFloatPointExpression", {...this.bsqemit_exp(), value: this.value}];
    }
    static bsqparse(jv: any): TIRLiteralFloatPointExpression {
        return new TIRLiteralFloatPointExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].value, jv[1].etype);
    }
}

class TIRLiteralStringExpression extends TIRExpression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string) {
        super(TIRExpressionTag.LiteralStringExpression, sinfo, "String", value);
        this.value = value;
    }

    bsqemit(): any {
        return ["TreeIR::LiteralStringExpression", {...this.bsqemit_exp(), value: this.value}];
    }
    static bsqparse(jv: any): TIRLiteralStringExpression {
        return new TIRLiteralStringExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].value);
    }
}

class TIRLiteralRegexExpression extends TIRExpression {
    readonly value: BSQRegex;

    constructor(sinfo: SourceInfo, value: BSQRegex) {
        super(TIRExpressionTag.LiteralRegexExpression, sinfo, "Regex", value.regexstr);
        this.value = value;
    }

    bsqemit(): any {
        return ["TreeIR::LiteralRegexExpression", {...this.bsqemit_exp(), value: this.value.jemit()}];
    }
    static bsqparse(jv: any): TIRLiteralRegexExpression {
        return new TIRLiteralRegexExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].value);
    }
}

class TIRLiteralASCIIStringExpression extends TIRExpression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string) {
        super(TIRExpressionTag.LiteralASCIIStringExpression, sinfo, "ASCIIString", value);
        this.value = value;
    }

    bsqemit(): any {
        return ["TreeIR::LiteralASCIIStringExpression", {...this.bsqemit_exp(), value: this.value}];
    }
    static bsqparse(jv: any): TIRLiteralASCIIStringExpression {
        return new TIRLiteralASCIIStringExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].value);
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

    bsqemit(): any {
        return ["TreeIR::LiteralTypedStringExpression", {...this.bsqemit_exp(), oftype: this.oftype, value: this.value}];
    }
    static bsqparse(jv: any): TIRLiteralTypedStringExpression {
        return new TIRLiteralTypedStringExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].value, jv[1].etype, jv[1].oftype);
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

    bsqemit(): any {
        return ["TreeIR::LiteralASCIITypedStringExpression", {...this.bsqemit_exp(), oftype: this.oftype, value: this.value}];
    }
    static bsqparse(jv: any): TIRLiteralASCIITypedStringExpression {
        return new TIRLiteralASCIITypedStringExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].value, jv[1].etype, jv[1].oftype);
    }
}

class TIRLiteralTemplateStringExpression extends TIRExpression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string, etype: TIRTypeKey) {
        super(TIRExpressionTag.LiteralTemplateStringExpression, sinfo, etype, value);
        this.value = value;
    }

    bsqemit(): any {
        return ["TreeIR::LiteralTemplateStringExpression", {...this.bsqemit_exp(), value: this.value}];
    }
    static bsqparse(jv: any): TIRLiteralTemplateStringExpression {
        return new TIRLiteralTemplateStringExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].value, jv[1].etype);
    }
}

class TIRLiteralASCIITemplateStringExpression extends TIRExpression {
    readonly value: string;

    constructor(sinfo: SourceInfo, value: string, etype: TIRTypeKey) {
        super(TIRExpressionTag.LiteralASCIITemplateStringExpression, sinfo, etype, value);
        this.value = value;
    }

    bsqemit(): any {
        return ["TreeIR::LiteralTemplateASCIIStringExpression", {...this.bsqemit_exp(), value: this.value}];
    }
    static bsqparse(jv: any): TIRLiteralASCIITemplateStringExpression {
        return new TIRLiteralASCIITemplateStringExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].value, jv[1].etype);
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

    bsqemit(): any {
        return ["TreeIR::LiteralTypedPrimitiveDirectExpression", {...this.bsqemit_exp(), value: this.value, constype: this.constype, basetype: this.basetype}];
    }
    static bsqparse(jv: any): TIRLiteralTypedPrimitiveDirectExpression {
        return new TIRLiteralTypedPrimitiveDirectExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].value, jv[1].constype, jv[1].basetype);
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

    bsqemit(): any {
        return ["TreeIR::LiteralTypedPrimitiveConstructorExpression", {...this.bsqemit_exp(), value: this.value, constype: this.constype, basetype: this.basetype}];
    }
    static bsqparse(jv: any): TIRLiteralTypedPrimitiveConstructorExpression {
        return new TIRLiteralTypedPrimitiveConstructorExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].value, jv[1].constype, jv[1].basetype);
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

    bsqemit(): any {
        return ["TreeIR::AccessEnvValueExpression", {...this.bsqemit_exp(), keyname: this.keyname, valtype: this.valtype, restype: this.restype, orNoneMode: this.orNoneMode}];
    }
    static bsqparse(jv: any): TIRAccessEnvValueExpression {
        return new TIRAccessEnvValueExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].keyname, jv[1].valtype, jv[1].restype, jv[1].orNoneMode);
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

    bsqemit(): any {
        return ["TreeIR::AccessNamespaceConstantExpression", {...this.bsqemit_exp(), ns: this.ns, cname: this.cname}];
    }
    static bsqparse(jv: any): TIRAccessNamespaceConstantExpression {
        return new TIRAccessNamespaceConstantExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].ns, jv[1].cname, jv[1].etype);
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

    bsqemit(): any {
        return ["TreeIR::AccessConstMemberFieldExpression", {...this.bsqemit_exp(), tkey: this.tkey, cname: this.cname}];
    }
    static bsqparse(jv: any): TIRAccessConstMemberFieldExpression {
        return new TIRAccessConstMemberFieldExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].tkey, jv[1].cname, jv[1].etype);
    }
}

class TIRAccessVariableExpression extends TIRExpression {
    readonly name: string;

    constructor(sinfo: SourceInfo, name: string, etype: TIRTypeKey) {
        super(TIRExpressionTag.AccessVariableExpression, sinfo, etype, name);
        this.name = name;
    }

    bsqemit(): any {
        return ["TreeIR::AccessVariableExpression", {...this.bsqemit_exp(), name: this.name}];
    }
    static bsqparse(jv: any): TIRAccessVariableExpression {
        return new TIRAccessVariableExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].name, jv[1].etype);
    }
}

class TIRAccessCapturedVariableExpression extends TIRExpression {
    readonly name: string;

    constructor(sinfo: SourceInfo, name: string, etype: TIRTypeKey) {
        super(TIRExpressionTag.AccessCapturedVariableExpression, sinfo, etype, name);
        this.name = name;
    }

    bsqemit(): any {
        return ["TreeIR::AccessCapturedVariableExpression", {...this.bsqemit_exp(), name: this.name}];
    }
    static bsqparse(jv: any): TIRAccessCapturedVariableExpression {
        return new TIRAccessCapturedVariableExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].name, jv[1].etype);
    }
}

class TIRAccessScratchSingleValueExpression extends TIRExpression {
    readonly sidx: number;

    constructor(sinfo: SourceInfo, etype: TIRTypeKey, sidx: number) {
        super(TIRExpressionTag.AccessScratchSingleValueExpression, sinfo, etype, `$$scratch<${sidx}, ${etype}>[]`);
        this.sidx = sidx;
    }

    bsqemit(): any {
        return ["TreeIR::AccessScratchSingleValueExpression", {...this.bsqemit_exp(), sidx: this.sidx}];
    }
    static bsqparse(jv: any): TIRAccessScratchSingleValueExpression {
        return new TIRAccessScratchSingleValueExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].etype, jv[1].sidx);
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

    bsqemit(): any {
        return ["TreeIR::AccessScratchIndexExpression", {...this.bsqemit_exp(), index: this.index, sidx: this.sidx}];
    }
    static bsqparse(jv: any): TIRAccessScratchIndexExpression {
        return new TIRAccessScratchIndexExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].index, jv[1].etype, jv[1].sidx);
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

    bsqemit_loadsingle(): any {
        return {...this.bsqemit_exp(), tkey: this.tkey, exp: this.exp.bsqemit()};
    }
}

class TIRLoadIndexExpression extends TIRLoadSingleExpression {
    readonly index: number;

    constructor(sinfo: SourceInfo, exp: TIRExpression, tkey: TIRTypeKey, index: number, resultType: TIRTypeKey) {
        super(TIRExpressionTag.LoadIndexExpression, sinfo, tkey, exp, resultType, `${exp.expstr}.${index}`);
        this.index = index;
    }

    bsqemit(): any {
        return ["TreeIR::LoadIndexExpression", {...this.bsqemit_loadsingle(), index: this.index}];
    }
    static bsqparse(jv: any): TIRLoadIndexExpression {
        return new TIRLoadIndexExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp), jv[1].tkey, jv[1].index, jv[1].etype);
    }
} 

class TIRLoadPropertyExpression extends TIRLoadSingleExpression {
    readonly property: string;

    constructor(sinfo: SourceInfo, exp: TIRExpression, tkey: TIRTypeKey, property: string, resultType: TIRTypeKey) {
        super(TIRExpressionTag.LoadPropertyExpression, sinfo, tkey, exp, resultType, `${exp.expstr}.${property}`);
        this.property = property;
    }

    bsqemit(): any {
        return ["TreeIR::LoadPropertyExpression", {...this.bsqemit_loadsingle(), property: this.property}];
    }
    static bsqparse(jv: any): TIRLoadPropertyExpression {
        return new TIRLoadPropertyExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp), jv[1].tkey, jv[1].property, jv[1].etype);
    }
}

class TIRLoadFieldExpression extends TIRLoadSingleExpression {
    readonly fieldkey: TIRFieldKey;

    constructor(sinfo: SourceInfo, tkey: TIRTypeKey, exp: TIRExpression, fieldkey: TIRFieldKey, resultType: TIRTypeKey) {
        super(TIRExpressionTag.LoadFieldExpression, sinfo, tkey, exp, resultType, `${exp.expstr}.${fieldkey}`);
        this.fieldkey = fieldkey;
    }

    bsqemit(): any {
        return ["TreeIR::LoadFieldExpression", {...this.bsqemit_loadsingle(), fieldkey: this.fieldkey}];
    }
    static bsqparse(jv: any): TIRLoadFieldExpression {
        return new TIRLoadFieldExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].tkey, TIRExpression.bsqparse(jv[1].exp), jv[1].fieldkey, jv[1].etype);
    }
}

class TIRLoadFieldVirtualExpression extends TIRLoadSingleExpression {
    readonly fieldkey: TIRFieldKey;

    constructor(sinfo: SourceInfo, tkey: TIRTypeKey, exp: TIRExpression, fieldkey: TIRFieldKey, resultType: TIRTypeKey) {
        super(TIRExpressionTag.LoadFieldVirtualExpression, sinfo, tkey, exp, resultType, `${exp.expstr}.${fieldkey}`);
        this.fieldkey = fieldkey;
    }

    bsqemit(): any {
        return ["TreeIR::LoadFieldVirtualExpression", {...this.bsqemit_loadsingle(), fieldkey: this.fieldkey}];
    }
    static bsqparse(jv: any): TIRLoadFieldVirtualExpression {
        return new TIRLoadFieldVirtualExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].tkey, TIRExpression.bsqparse(jv[1].exp), jv[1].fieldkey, jv[1].etype);
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

    bsqemit_consexp(): any {
        return {...this.bsqemit_exp(), oftype: this.oftype, args: this.args.map((arg) => arg.bsqemit())};
    }
}

class TIRConstructorPrimaryDirectExpression extends TIRConstructorExpression {
    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.ConstructorPrimaryDirectExpression, sinfo, oftype, args, `${oftype}{${args.map((arg) => arg.expstr).join(", ")}`);
    }

    bsqemit(): any {
        return ["TreeIR::ConstructorPrimaryDirectExpression", {...this.bsqemit_consexp()}];
    }
    static bsqparse(jv: any): TIRConstructorPrimaryDirectExpression {
        return new TIRConstructorPrimaryDirectExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].oftype, jv[1].args.map((arg: any) => TIRExpression.bsqparse(arg)));
    }
}

class TIRConstructorPrimaryCheckExpression extends TIRConstructorExpression {
    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.ConstructorPrimaryCheckExpression, sinfo, oftype, args, `${oftype}{${args.map((arg) => arg.expstr).join(", ")}`);
    }

    bsqemit(): any {
        return ["TreeIR::ConstructorPrimaryCheckExpression", {...this.bsqemit_consexp()}];
    }
    static bsqparse(jv: any): TIRConstructorPrimaryCheckExpression {
        return new TIRConstructorPrimaryCheckExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].oftype, jv[1].args.map((arg: any) => TIRExpression.bsqparse(arg)));
    }
}

class TIRConstructorTupleExpression extends TIRConstructorExpression {
    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.ConstructorTupleExpression, sinfo, oftype, args, `[${args.map((arg) => arg.expstr).join(", ")}]`);
    }

    bsqemit(): any {
        return ["TreeIR::ConstructorTupleExpression", {...this.bsqemit_consexp()}];
    }
    static bsqparse(jv: any): TIRConstructorTupleExpression {
        return new TIRConstructorTupleExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].oftype, jv[1].args.map((arg: any) => TIRExpression.bsqparse(arg)));
    }
}

class TIRConstructorRecordExpression extends TIRConstructorExpression {
    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.ConstructorRecordExpression, sinfo, oftype, args, `{${args.map((arg) => arg.expstr).join(", ")}}`);
    }

    bsqemit(): any {
        return ["TreeIR::ConstructorRecordExpression", {...this.bsqemit_consexp()}];
    }
    static bsqparse(jv: any): TIRConstructorRecordExpression {
        return new TIRConstructorRecordExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].oftype, jv[1].args.map((arg: any) => TIRExpression.bsqparse(arg)));
    }
}

class TIRConstructorListExpression  extends TIRConstructorExpression {
    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.ConstructorListExpression, sinfo, oftype, args, `List{${args.map((arg) => arg.expstr).join(", ")}}`);
    }

    bsqemit(): any {
        return ["TreeIR::ConstructorListExpression", {...this.bsqemit_consexp()}];
    }
    static bsqparse(jv: any): TIRConstructorListExpression {
        return new TIRConstructorListExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].oftype, jv[1].args.map((arg: any) => TIRExpression.bsqparse(arg)));
    }
}
    
class TIRConstructorMapExpression extends TIRConstructorExpression {
    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.ConstructorMapExpression, sinfo, oftype, args, `Map{${args.map((arg) => arg.expstr).join(", ")}}`);
    }

    bsqemit(): any {
        return ["TreeIR::ConstructorMapExpression", {...this.bsqemit_consexp()}];
    }
    static bsqparse(jv: any): TIRConstructorMapExpression {
        return new TIRConstructorMapExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].oftype, jv[1].args.map((arg: any) => TIRExpression.bsqparse(arg)));
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

    bsqemit(): any {
        return ["TreeIR::CodePackInvokeExpression", {...this.bsqemit_exp(), cpack: this.cpack.bsqemit(), args: this.args.map((arg) => arg.bsqemit())}];
    }
    static bsqparse(jv: any): TIRCodePackInvokeExpression {
        return new TIRCodePackInvokeExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].etype, TIRCodePack.bsqparse(jv[1].cpack), jv[1].args.map((arg: any) => TIRExpression.bsqparse(arg)));
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

    bsqemit_consof(): any {
        return {...this.bsqemit_exp(), oftype: this.oftype, arg: this.arg.bsqemit()};
    }
}

class TIRResultOkConstructorExpression extends TIRConstructorOfExpression {
    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, arg: TIRExpression) {
        super(TIRExpressionTag.ResultOkConstructorExpression, sinfo, oftype, arg, `cons_ok<${oftype}>{${arg.expstr}}`);
    }

    bsqemit(): any {
        return ["TreeIR::ResultOkConstructorExpression", {...this.bsqemit_consof()}];
    }
    static bsqparse(jv: any): TIRResultOkConstructorExpression {
        return new TIRResultOkConstructorExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].oftype, TIRExpression.bsqparse(jv[1].arg));
    }
}

class TIRResultErrConstructorExpression extends TIRConstructorOfExpression {
    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, arg: TIRExpression) {
        super(TIRExpressionTag.ResultErrConstructorExpression, sinfo, oftype, arg, `cons_err<${oftype}>{${arg.expstr}}`);
    }

    bsqemit(): any {
        return ["TreeIR::ResultErrConstructorExpression", {...this.bsqemit_consof()}];
    }
    static bsqparse(jv: any): TIRResultErrConstructorExpression {
        return new TIRResultErrConstructorExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].oftype, TIRExpression.bsqparse(jv[1].arg));
    }
}

class TIRSomethingConstructorExpression extends TIRConstructorOfExpression {
    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, arg: TIRExpression) {
        super(TIRExpressionTag.SomethingConstructorExpression, sinfo, oftype, arg, `cons_something<${oftype}>{${arg.expstr}}`);
    }

    bsqemit(): any {
        return ["TreeIR::SomethingConstructorExpression", {...this.bsqemit_consof()}];
    }
    static bsqparse(jv: any): TIRSomethingConstructorExpression {
        return new TIRSomethingConstructorExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].oftype, TIRExpression.bsqparse(jv[1].arg));
    }
}

class TIRTypedeclDirectExpression extends TIRConstructorOfExpression {
    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, arg: TIRExpression) {
        super(TIRExpressionTag.TypedeclDirectExpression, sinfo, oftype, arg, `cons_typedecl<${oftype}>{${arg.expstr}}`);
    }

    bsqemit(): any {
        return ["TreeIR::TypedeclDirectExpression", {...this.bsqemit_consof()}];
    }
    static bsqparse(jv: any): TIRTypedeclDirectExpression {
        return new TIRTypedeclDirectExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].oftype, TIRExpression.bsqparse(jv[1].arg));
    }
}

class TIRTypedeclConstructorExpression extends TIRConstructorOfExpression {
    constructor(sinfo: SourceInfo, oftype: TIRTypeKey, arg: TIRExpression) {
        super(TIRExpressionTag.TypedeclConstructorExpression, sinfo, oftype, arg, `cons_typedecl<${oftype}>{${arg.expstr}}`);
    }

    isFailableOperation(): boolean {
        return true;
    }

    bsqemit(): any {
        return ["TreeIR::TypedeclConstructorExpression", {...this.bsqemit_consof()}];
    }
    static bsqparse(jv: any): TIRTypedeclConstructorExpression {
        return new TIRTypedeclConstructorExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].oftype, TIRExpression.bsqparse(jv[1].arg));
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

    bsqemit_call(): any {
        return {...this.bsqemit_exp(), fkey: this.fkey, args: this.args.map((arg) => arg.bsqemit())};
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

    bsqemit(): any {
        return ["TreeIR::CallNamespaceFunctionExpression", {...this.bsqemit_call(), ns: this.ns, fname: this.fname}];
    }
    static bsqparse(jv: any): TIRCallNamespaceFunctionExpression {
        return new TIRCallNamespaceFunctionExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].ns, jv[1].fname, jv[1].fkey, jv[1].etype, jv[1].args.map((arg: any) => TIRExpression.bsqparse(arg)));
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

    bsqemit(): any {
        return ["TreeIR::CallNamespaceOperatorExpression", {...this.bsqemit_call(), ns: this.ns, oname: this.oname}];
    }
    static bsqparse(jv: any): TIRCallNamespaceOperatorExpression {
        return new TIRCallNamespaceOperatorExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].ns, jv[1].oname, jv[1].fkey, jv[1].etype, jv[1].args.map((arg: any) => TIRExpression.bsqparse(arg)));
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

    bsqemit(): any {
        return ["TreeIR::CallStaticFunctionExpression", {...this.bsqemit_call(), tkey: this.tkey, fname: this.fname}];
    }
    static bsqparse(jv: any): TIRCallStaticFunctionExpression {
        return new TIRCallStaticFunctionExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].tkey, jv[1].fname, jv[1].fkey, jv[1].etype, jv[1].args.map((arg: any) => TIRExpression.bsqparse(arg)));
    }
}

//abstract class for logic actions
abstract class TIRLogicActionExpression extends TIRExpression {
    readonly args: TIRExpression[]; 

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, args: TIRExpression[], exprstr: string) {
        super(tag, sinfo, "Bool", exprstr);
        this.args = args;
    }

    bsqemit_laction(): any {
        return {...this.bsqemit_exp(), args: this.args.map((arg) => arg.bsqemit())};
    }
}

class TIRLogicActionAndExpression extends TIRLogicActionExpression {
    constructor(sinfo: SourceInfo, args: TIRExpression[]) {
        super(TIRExpressionTag.LogicActionAndExpression, sinfo, args, `/\\(${args.map((arg) => arg.expstr).join(", ")})`);
    }

    bsqemit(): any {
        return ["TreeIR::LogicActionAndExpression", this.bsqemit_laction()];
    }
    static bsqparse(jv: any): TIRLogicActionAndExpression {
        return new TIRLogicActionAndExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].args.map((arg: any) => TIRExpression.bsqparse(arg)));
    }
}

class TIRLogicActionOrExpression extends TIRLogicActionExpression {
    constructor(sinfo: SourceInfo, args: TIRExpression[]) {
        super(TIRExpressionTag.LogicActionOrExpression, sinfo, args, `\\/(${args.map((arg) => arg.expstr).join(", ")})`);
    }

    bsqemit(): any {
        return ["TreeIR::LogicActionOrExpression", this.bsqemit_laction()];
    }
    static bsqparse(jv: any): TIRLogicActionOrExpression {
        return new TIRLogicActionOrExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].args.map((arg: any) => TIRExpression.bsqparse(arg)));
    }
}

//abstract class for unary expressions
abstract class TIRUnaryExpression extends TIRExpression {
    readonly exp: TIRExpression;

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, rtype: TIRTypeKey, exp: TIRExpression, exprstr: string) {
        super(tag, sinfo, rtype, exprstr);
        this.exp = exp;
    }

    bsqemit_unary(): any {
        return {...this.bsqemit_exp(), exp: this.exp.bsqemit()};
    }
}

class TIRPrefixNotExpression extends TIRUnaryExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression) {
        super(TIRExpressionTag.PrefixNotExpression, sinfo, "Bool", exp, `!(${exp.expstr})`);
    }

    bsqemit(): any {
        return ["TreeIR::PrefixNotExpression", this.bsqemit_unary()];
    }
    static bsqparse(jv: any): TIRPrefixNotExpression {
        return new TIRPrefixNotExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp));
    }
}

class TIRPrefixNegateExpression extends TIRUnaryExpression {
    readonly optype: TIRTypeKey;

    constructor(sinfo: SourceInfo, exp: TIRExpression, exptype: TIRTypeKey, ntype: TIRTypeKey) {
        super(TIRExpressionTag.PrefixNegateExpression, sinfo, exptype, exp, `-(${exp.expstr})`);
        this.optype = ntype;
    }

    bsqemit(): any {
        return ["TreeIR::PrefixNegateExpression", {...this.bsqemit_unary(), optype: this.optype}];
    }
    static bsqparse(jv: any): TIRPrefixNegateExpression {
        return new TIRPrefixNegateExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp), jv[1].etype, jv[1].optype);
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

    bsqemit_binop(): any {
        return {...this.bsqemit_exp(), optype: this.optype, lhs: this.lhs.bsqemit(), rhs: this.rhs.bsqemit()};
    }
}

class TIRBinAddExpression extends TIRBinOpExpression {
    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, exptype: TIRTypeKey, ntype: TIRTypeKey) {
        super(TIRExpressionTag.BinAddExpression, sinfo, lhs, rhs, exptype, ntype, `(${lhs.expstr} + ${rhs.expstr})`);
    }

    bsqemit(): any {
        return ["TreeIR::BinAddExpression", this.bsqemit_binop()];
    }
    static bsqparse(jv: any): TIRBinAddExpression {
        return new TIRBinAddExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].lhs), TIRExpression.bsqparse(jv[1].rhs), jv[1].etype, jv[1].optype);
    }
}

class TIRBinSubExpression extends TIRBinOpExpression {
    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, exptype: TIRTypeKey, ntype: TIRTypeKey) {
        super(TIRExpressionTag.BinSubExpression, sinfo, lhs, rhs, exptype, ntype, `(${lhs.expstr} - ${rhs.expstr})`);
    }

    bsqemit(): any {
        return ["TreeIR::BinSubExpression", this.bsqemit_binop()];
    }
    static bsqparse(jv: any): TIRBinSubExpression {
        return new TIRBinSubExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].lhs), TIRExpression.bsqparse(jv[1].rhs), jv[1].etype, jv[1].optype);
    }
}

class TIRBinMultExpression extends TIRBinOpExpression {
    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, exptype: TIRTypeKey, ntype: TIRTypeKey) {
        super(TIRExpressionTag.BinMultExpression, sinfo, lhs, rhs, exptype, ntype, `(${lhs.expstr} * ${rhs.expstr})`);
    }

    bsqemit(): any {
        return ["TreeIR::BinMultExpression", this.bsqemit_binop()];
    }
    static bsqparse(jv: any): TIRBinMultExpression {
        return new TIRBinMultExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].lhs), TIRExpression.bsqparse(jv[1].rhs), jv[1].etype, jv[1].optype);
    }
}

class TIRBinDivExpression extends TIRBinOpExpression {
    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, exptype: TIRTypeKey, ntype: TIRTypeKey) {
        super(TIRExpressionTag.BinDivExpression, sinfo, lhs, rhs, exptype, ntype, `(${lhs.expstr} / ${rhs.expstr})`);
    }

    bsqemit(): any {
        return ["TreeIR::BinDivExpression", this.bsqemit_binop()];
    }
    static bsqparse(jv: any): TIRBinDivExpression {
        return new TIRBinDivExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].lhs), TIRExpression.bsqparse(jv[1].rhs), jv[1].etype, jv[1].optype);
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

    bsqemit(): any {
        return ["TreeIR::BinKeyEqBothUniqueExpression", {...this.bsqemit_exp(), optype: this.optype, lhs: this.lhs.bsqemit(), rhs: this.rhs.bsqemit()}];
    }
    static bsqparse(jv: any): TIRBinKeyEqBothUniqueExpression {
        return new TIRBinKeyEqBothUniqueExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].lhs), TIRExpression.bsqparse(jv[1].rhs), jv[1].optype);
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

    bsqemit(): any {
        return ["TreeIR::BinKeyEqOneUniqueExpression", {...this.bsqemit_exp(), oftype: this.oftype, uarg: this.uarg.bsqemit(), gtype: this.gtype, garg: this.garg.bsqemit()}];
    }
    static bsqparse(jv: any): TIRBinKeyEqOneUniqueExpression {
        return new TIRBinKeyEqOneUniqueExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].oftype, TIRExpression.bsqparse(jv[1].uarg), jv[1].gtype, TIRExpression.bsqparse(jv[1].garg));
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

    bsqemit(): any {
        return ["TreeIR::BinKeyEqGeneralExpression", {...this.bsqemit_exp(), lhstype: this.lhstype, lhs: this.lhs.bsqemit(), rhstype: this.rhstype, rhs: this.rhs.bsqemit()}];
    }
    static bsqparse(jv: any): TIRBinKeyEqGeneralExpression {
        return new TIRBinKeyEqGeneralExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].lhstype, TIRExpression.bsqparse(jv[1].lhs), jv[1].rhstype, TIRExpression.bsqparse(jv[1].rhs));
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

    bsqemit(): any {
        return ["TreeIR::BinKeyNeqBothUniqueExpression", {...this.bsqemit_exp(), optype: this.optype, lhs: this.lhs.bsqemit(), rhs: this.rhs.bsqemit()}];
    }
    static bsqparse(jv: any): TIRBinKeyNeqBothUniqueExpression {
        return new TIRBinKeyNeqBothUniqueExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].lhs), TIRExpression.bsqparse(jv[1].rhs), jv[1].optype);
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

    bsqemit(): any {
        return ["TreeIR::BinKeyNeqOneUniqueExpression", {...this.bsqemit_exp(), oftype: this.oftype, uarg: this.uarg.bsqemit(), gtype: this.gtype, garg: this.garg.bsqemit()}];
    }
    static bsqparse(jv: any): TIRBinKeyNeqOneUniqueExpression {
        return new TIRBinKeyNeqOneUniqueExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].oftype, TIRExpression.bsqparse(jv[1].uarg), jv[1].gtype, TIRExpression.bsqparse(jv[1].garg));
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

    bsqemit(): any {
        return ["TreeIR::BinKeyNeqGeneralExpression", {...this.bsqemit_exp(), lhstype: this.lhstype, lhs: this.lhs.bsqemit(), rhstype: this.rhstype, rhs: this.rhs.bsqemit()}];
    }
    static bsqparse(jv: any): TIRBinKeyNeqGeneralExpression {
        return new TIRBinKeyNeqGeneralExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].lhstype, TIRExpression.bsqparse(jv[1].lhs), jv[1].rhstype, TIRExpression.bsqparse(jv[1].rhs));
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

    bsqemit(): any {
        return ["TreeIR::BinKeyUniqueLessExpression", {...this.bsqemit_exp(), optype: this.optype, lhs: this.lhs.bsqemit(), rhs: this.rhs.bsqemit()}];
    }
    static bsqparse(jv: any): TIRBinKeyUniqueLessExpression {
        return new TIRBinKeyUniqueLessExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].lhs), TIRExpression.bsqparse(jv[1].rhs), jv[1].optype);
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

    bsqemit(): any {
        return ["TreeIR::BinKeyGeneralLessExpression", {...this.bsqemit_exp(), optype: this.optype, lhs: this.lhs.bsqemit(), rhs: this.rhs.bsqemit()}];
    }
    static bsqparse(jv: any): TIRBinKeyGeneralLessExpression {
        return new TIRBinKeyGeneralLessExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].lhs), TIRExpression.bsqparse(jv[1].rhs), jv[1].optype);
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

    bsqemit_bincmp(): any {
        return {...this.bsqemit_exp(), optype: this.optype, lhs: this.lhs.bsqemit(), rhs: this.rhs.bsqemit()};
    }
}

class TIRNumericEqExpression extends TIRNumericBinCmpExpression {
    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, ntype: TIRTypeKey) {
        super(TIRExpressionTag.NumericEqExpression, sinfo, lhs, rhs, ntype, `(${lhs.expstr} == ${rhs.expstr})`);
    }

    bsqemit(): any {
        return ["TreeIR::NumericEqExpression", this.bsqemit_bincmp()];
    }
    static bsqparse(jv: any): TIRNumericEqExpression {
        return new TIRNumericEqExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].lhs), TIRExpression.bsqparse(jv[1].rhs), jv[1].optype);
    }
}

class TIRNumericNeqExpression extends TIRNumericBinCmpExpression {
    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, ntype: TIRTypeKey) {
        super(TIRExpressionTag.NumericNeqExpression, sinfo, lhs, rhs, ntype, `(${lhs.expstr} != ${rhs.expstr})`);
    }

    bsqemit(): any {
        return ["TreeIR::NumericNeqExpression", this.bsqemit_bincmp()];
    }
    static bsqparse(jv: any): TIRNumericNeqExpression {
        return new TIRNumericNeqExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].lhs), TIRExpression.bsqparse(jv[1].rhs), jv[1].optype);
    }
}

class TIRNumericLessExpression extends TIRNumericBinCmpExpression {
    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, ntype: TIRTypeKey) {
        super(TIRExpressionTag.NumericLessExpression, sinfo, lhs, rhs, ntype, `(${lhs.expstr} < ${rhs.expstr})`);
    }

    bsqemit(): any {
        return ["TreeIR::NumericLessExpression", this.bsqemit_bincmp()];
    }
    static bsqparse(jv: any): TIRNumericLessExpression {
        return new TIRNumericLessExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].lhs), TIRExpression.bsqparse(jv[1].rhs), jv[1].optype);
    }
}

class TIRNumericLessEqExpression extends TIRNumericBinCmpExpression {
    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, ntype: TIRTypeKey) {
        super(TIRExpressionTag.NumericLessEqExpression, sinfo, lhs, rhs, ntype, `(${lhs.expstr} <= ${rhs.expstr})`);
    }

    bsqemit(): any {
        return ["TreeIR::NumericLessEqExpression", this.bsqemit_bincmp()];
    }
    static bsqparse(jv: any): TIRNumericLessEqExpression {
        return new TIRNumericLessEqExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].lhs), TIRExpression.bsqparse(jv[1].rhs), jv[1].optype);
    }
}

class TIRNumericGreaterExpression extends TIRNumericBinCmpExpression {
    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, ntype: TIRTypeKey) {
        super(TIRExpressionTag.NumericGreaterExpression, sinfo, lhs, rhs, ntype, `(${lhs.expstr} > ${rhs.expstr})`);
    }

    bsqemit(): any {
        return ["TreeIR::NumericGreaterExpression", this.bsqemit_bincmp()];
    }
    static bsqparse(jv: any): TIRNumericGreaterExpression {
        return new TIRNumericGreaterExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].lhs), TIRExpression.bsqparse(jv[1].rhs), jv[1].optype);
    }
}

class TIRNumericGreaterEqExpression extends TIRNumericBinCmpExpression {
    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression, ntype: TIRTypeKey) {
        super(TIRExpressionTag.NumericGreaterEqExpression, sinfo, lhs, rhs, ntype, `(${lhs.expstr} >= ${rhs.expstr})`);
    }

    bsqemit(): any {
        return ["TreeIR::NumericGreaterEqExpression", this.bsqemit_bincmp()];
    }
    static bsqparse(jv: any): TIRNumericGreaterEqExpression {
        return new TIRNumericGreaterEqExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].lhs), TIRExpression.bsqparse(jv[1].rhs), jv[1].optype);
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

    bsqemit_logic(): any {
        return {...this.bsqemit_exp(), lhs: this.lhs.bsqemit(), rhs: this.rhs.bsqemit()};
    }
}

class TIRBinLogicAndExpression extends TIRBinLogicExpression {
    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression) {
        super(TIRExpressionTag.BinLogicAndExpression, sinfo, lhs, rhs, `(${lhs.expstr} && ${rhs.expstr})`);
    }

    bsqemit(): any {
        return ["TreeIR::BinLogicAndExpression", this.bsqemit_logic()];
    }
    static bsqparse(jv: any): TIRBinLogicAndExpression {
        return new TIRBinLogicAndExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].lhs), TIRExpression.bsqparse(jv[1].rhs));
    }
}

class TIRBinLogicOrExpression extends TIRBinLogicExpression {
    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression) {
        super(TIRExpressionTag.BinLogicOrExpression, sinfo, lhs, rhs, `(${lhs.expstr} || ${rhs.expstr})`);
    }

    bsqemit(): any {
        return ["TreeIR::BinLogicOrExpression", this.bsqemit_logic()];
    }
    static bsqparse(jv: any): TIRBinLogicOrExpression {
        return new TIRBinLogicOrExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].lhs), TIRExpression.bsqparse(jv[1].rhs));
    }
}

class TIRBinLogicImpliesExpression extends TIRBinLogicExpression {
    constructor(sinfo: SourceInfo, lhs: TIRExpression, rhs: TIRExpression) {
        super(TIRExpressionTag.BinLogicImpliesExpression, sinfo, lhs, rhs, `(${lhs.expstr} ==> ${rhs.expstr})`);
    }

    bsqemit(): any {
        return ["TreeIR::BinLogicImpliesExpression", this.bsqemit_logic()];
    }
    static bsqparse(jv: any): TIRBinLogicImpliesExpression {
        return new TIRBinLogicImpliesExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].lhs), TIRExpression.bsqparse(jv[1].rhs));
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

    bsqemit(): any {
        return ["TreeIR::MapEntryConstructorExpression", {...this.bsqemit_exp(), ktype: this.ktype, vtype: this.vtype, oftype: this.oftype, kexp: this.kexp.bsqemit(), vexp: this.vexp.bsqemit()}];
    }
    static bsqparse(jv: any): TIRMapEntryConstructorExpression {
        return new TIRMapEntryConstructorExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].kexp), TIRExpression.bsqparse(jv[1].vexp), jv[1].ktype, jv[1].vtype, jv[1].oftype);
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

    bsqemit(): any {
        return ["TreeIR::IfExpression", {
            ...this.bsqemit_exp(), 
            ifentry: {etest: this.ifentry.test.bsqemit(), value: this.ifentry.value.bsqemit(), binderinfo: this.ifentry.binderinfo !== undefined ? [this.ifentry.binderinfo[0].bsqemit(), this.ifentry.binderinfo[1], this.ifentry.binderinfo[2].bsqemit(), this.ifentry.binderinfo[3]] : null}, 
            elifentries: this.elifentries.map((efi) => ({etest: efi.test.bsqemit(), value: efi.value.bsqemit(), binderinfo: efi.binderinfo !== undefined ? [efi.binderinfo[0].bsqemit(), efi.binderinfo[1], efi.binderinfo[2].bsqemit(), efi.binderinfo[3]] : null})), 
            elseentry: {value: this.elseentry.value.bsqemit(), binderinfo: this.elseentry.binderinfo !== undefined ? [this.elseentry.binderinfo[0].bsqemit(), this.elseentry.binderinfo[1], this.elseentry.binderinfo[2].bsqemit(), this.elseentry.binderinfo[3]] : null}
        }];
    }
    static bsqparse(jv: any): TIRIfExpression {
        return new TIRIfExpression(
            SourceInfo.bsqparse(jv[1].sinfo), jv[1].etype,
            {test: TIRExpression.bsqparse(jv[1].ifentry.etest), value: TIRExpression.bsqparse(jv[1].ifentry.value), binderinfo: jv[1].ifentry.binderinfo !== null ? [TIRExpression.bsqparse(jv[1].ifentry.binderinfo[0]), jv[1].ifentry.binderinfo[1], TIRExpression.bsqparse(jv[1].ifentry.binderinfo[2]), jv[1].ifentry.binderinfo[3]] : undefined},
            jv[1].elifentries.map((efi: any) => ({test: TIRExpression.bsqparse(efi.etest), value: TIRExpression.bsqparse(efi.value), binderinfo: efi.binderinfo !== null ? [TIRExpression.bsqparse(efi.binderinfo[0]), efi.binderinfo[1], TIRExpression.bsqparse(efi.binderinfo[2]), efi.binderinfo[3]] : undefined})),
            {value: TIRExpression.bsqparse(jv[1].elseentry.value), binderinfo: jv[1].elseentry.binderinfo !== null ? [TIRExpression.bsqparse(jv[1].elseentry.binderinfo[0]), jv[1].elseentry.binderinfo[1], TIRExpression.bsqparse(jv[1].elseentry.binderinfo[2]), jv[1].elseentry.binderinfo[3]] : undefined}
        )
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

    bsqemit(): any {
        return ["TreeIR::SwitchExpression", {
            ...this.bsqemit_exp(), 
            exp: this.exp.bsqemit(), 
            scratchidx: this.scratchidx, 
            clauses: this.clauses.map((ci) => ({ematch: ci.match.bsqemit(), value: ci.value.bsqemit(), binderinfo: ci.binderinfo !== undefined ? [ci.binderinfo[0].bsqemit(), ci.binderinfo[1]] : null})), 
            edefault: this.edefault !== undefined ? {value: this.edefault.value.bsqemit(), binderinfo: this.edefault.binderinfo !== undefined ? [this.edefault.binderinfo[0].bsqemit(), this.edefault.binderinfo[1]] : null} : null, 
            isexhaustive: this.isexhaustive
        }];
    }
    static bsqparse(jv: any): TIRSwitchExpression {
        return new TIRSwitchExpression(
            SourceInfo.bsqparse(jv[1].sinfo), jv[1].etype,
            TIRExpression.bsqparse(jv[1].exp), jv[1].scratchidx,
            jv[1].clauses.map((ci: any) => ({match: TIRExpression.bsqparse(ci.ematch), value: TIRExpression.bsqparse(ci.value), binderinfo: ci.binderinfo !== null ? [TIRExpression.bsqparse(ci.binderinfo[0]), ci.binderinfo[1]] : undefined})),
            jv[1].edefault !== null ? {value: TIRExpression.bsqparse(jv[1].edefault.value), binderinfo: jv[1].edefault.binderinfo !== null ? [TIRExpression.bsqparse(jv[1].edefault.binderinfo[0]), jv[1].edefault.binderinfo[1]] : undefined} : undefined,
            jv[1].isexhaustive
        )
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

    bsqemit(): any {
        return ["TreeIR::MatchExpression", {
            ...this.bsqemit_exp(), 
            exp: this.exp.bsqemit(), 
            scratchidx: this.scratchidx, 
            clauses: this.clauses.map((ci) => ({ematch: ci.match.bsqemit(), value: ci.value.bsqemit(), binderinfo: ci.binderinfo !== undefined ? [ci.binderinfo[0].bsqemit(), ci.binderinfo[1]] : null})), 
            edefault: this.edefault !== undefined ? {value: this.edefault.value.bsqemit(), binderinfo: this.edefault.binderinfo !== undefined ? [this.edefault.binderinfo[0].bsqemit(), this.edefault.binderinfo[1]] : null} : null, 
            isexhaustive: this.isexhaustive
        }];
    }
    static bsqparse(jv: any): TIRMatchExpression {
        return new TIRMatchExpression(
            SourceInfo.bsqparse(jv[1].sinfo), jv[1].etype,
            TIRExpression.bsqparse(jv[1].exp), jv[1].scratchidx,
            jv[1].clauses.map((ci: any) => ({match: TIRExpression.bsqparse(ci.ematch), value: TIRExpression.bsqparse(ci.value), binderinfo: ci.binderinfo !== null ? [TIRExpression.bsqparse(ci.binderinfo[0]), ci.binderinfo[1]] : undefined})),
            jv[1].edefault !== null ? {value: TIRExpression.bsqparse(jv[1].edefault.value), binderinfo: jv[1].edefault.binderinfo !== null ? [TIRExpression.bsqparse(jv[1].edefault.binderinfo[0]), jv[1].edefault.binderinfo[1]] : undefined} : undefined,
            jv[1].isexhaustive
        )
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

    bsqemit(): any {
        return ["TreeIR::TaskSelfFieldExpression", {...this.bsqemit_exp(), tasktype: this.tasktype, fieldkey: this.fieldkey, fname: this.fname}];
    }
    static bsqparse(jv: any): TIRTaskSelfFieldExpression {
        return new TIRTaskSelfFieldExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].tasktype, jv[1].field, jv[1].fname, jv[1].etype);
    }
}

class TIRTaskSelfControlExpression extends TIRExpression {
    readonly tasktype: TIRTypeKey;

    constructor(sinfo: SourceInfo, tasktype: TIRTypeKey, resultType: TIRTypeKey) {
        super(TIRExpressionTag.TaskSelfControlExpression, sinfo, resultType, `self.cntl`);
        this.tasktype = tasktype;
    }

    bsqemit(): any {
        return ["TreeIR::TaskSelfControlExpression", {...this.bsqemit_exp(), tasktype: this.tasktype}];
    }
    static bsqparse(jv: any): TIRTaskSelfControlExpression {
        return new TIRTaskSelfControlExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].tasktype, jv[1].etype);
    }
}

class TIRTaskGetIDExpression extends TIRExpression {
    readonly tasktype: TIRTypeKey;

    constructor(sinfo: SourceInfo, tasktype: TIRTypeKey, resultType: TIRTypeKey) {
        super(TIRExpressionTag.TaskGetIDExpression, sinfo, resultType, `getTaskID`);
        this.tasktype = tasktype;
    }

    bsqemit(): any {
        return ["TreeIR::TaskGetIDExpression", {...this.bsqemit_exp(), tasktype: this.tasktype}];
    }
    static bsqparse(jv: any): TIRTaskGetIDExpression {
        return new TIRTaskGetIDExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].tasktype, jv[1].etype);
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

    bsqemit(): any {
        return ["TreeIR::CoerceSafeExpression", {...this.bsqemit_exp(), exp: this.exp.bsqemit(), fromtype: this.fromtype, totype: this.totype}];
    }
    static bsqparse(jv: any): TIRCoerceSafeExpression {
        return new TIRCoerceSafeExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp), jv[1].fromtype, jv[1].totype);
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
    
    bsqemit_ie(): any {
        return {...this.bsqemit_exp(), exp: this.exp.bsqemit(), totype: this.totype};
    }
}

class TIRInjectExpression extends TIRInjectExtractExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, totype: TIRTypeKey) {
        super(TIRExpressionTag.InjectExpression, sinfo, exp, totype, `inject<${totype}>(${exp.expstr})`);
    }

    bsqemit() {
        return ["TreeIR::InjectExpression", this.bsqemit_ie()];
    }
    static bsqparse(jv: any): TIRInjectExpression {
        return new TIRInjectExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp), jv[1].totype);
    }
}

class TIRExtractExpression extends TIRInjectExtractExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, totype: TIRTypeKey) {
        super(TIRExpressionTag.ExtractExpression, sinfo, exp, totype, `extract<${totype}>(${exp.expstr})`);
    }

    bsqemit(): any {
        return ["TreeIR::ExtractExpression", this.bsqemit_ie()];
    }
    static bsqparse(jv: any): TIRExtractExpression {
        return new TIRExtractExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp), jv[1].totype);
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

    bsqemit(): any {
        return ["TreeIR::CreateCodePackExpression", {...this.bsqemit_exp(), pcodepack: this.pcodepack.bsqemit(), capturedirect: this.capturedirect, captureindirect: this.captureindirect, capturepackdirect: this.capturepackdirect, capturepackindirect: this.capturepackindirect}];
    }
    static bsqparse(jv: any): TIRCreateCodePackExpression {
        return new TIRCreateCodePackExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRCodePack.bsqparse(jv[1].pcodepack), jv[1].etype, jv[1].capturedirect, jv[1].captureindirect, jv[1].capturepackdirect, jv[1].capturepackindirect);
    }
}

//abstract class for is test operations
abstract class TIRTestIsExpression extends TIRExpression {
    readonly exp: TIRExpression;

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, exp: TIRExpression, exprstr: string) {
        super(tag, sinfo, "Bool", exprstr);
        this.exp = exp;
    }

    bsqemit_ti(): any {
        return {...this.bsqemit_exp(), exp: this.exp.bsqemit()};
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

    bsqemit(): any {
        return ["TreeIR::IsNoneSpecialExpression", this.bsqemit_ti()];
    }
    static bsqparse(jv: any): TIRIsNoneSpecialExpression {
        return new TIRIsNoneSpecialExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp));
    }
} 

class TIRIsSomeSpecialExpression extends TIRITestIsSpecialExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression) {
        super(TIRExpressionTag.IsSomeSpecialExpression, sinfo, exp, `${exp.expstr}?!none`);
    }

    bsqemit(): any {
        return ["TreeIR::IsSomeSpecialExpression", this.bsqemit_ti()];
    }
    static bsqparse(jv: any): TIRIsSomeSpecialExpression {
        return new TIRIsSomeSpecialExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp));
    }
}

class TIRIsNothingSpecialExpression extends TIRITestIsSpecialExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression) {
        super(TIRExpressionTag.IsNothingSpecialExpression, sinfo, exp, `${exp.expstr}?nothing`);
    }

    bsqemit(): any {
        return ["TreeIR::IsNothingSpecialExpression", this.bsqemit_ti()];
    }
    static bsqparse(jv: any): TIRIsNothingSpecialExpression {
        return new TIRIsNothingSpecialExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp));
    }
}

class TIRIsSomethingSpecialExpression extends TIRITestIsSpecialExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression) {
        super(TIRExpressionTag.IsSomethingSpecialExpression, sinfo, exp, `${exp.expstr}?something`);
    }

    bsqemit(): any {
        return ["TreeIR::IsSomethingSpecialExpression", this.bsqemit_ti()];
    }
    static bsqparse(jv: any): TIRIsSomethingSpecialExpression {
        return new TIRIsSomethingSpecialExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp));
    }
}

class TIRIsOkSpecialExpression  extends TIRITestIsSpecialExpression {
    readonly oktype: TIRTypeKey;

    constructor(sinfo: SourceInfo, exp: TIRExpression, oktype: TIRTypeKey) {
        super(TIRExpressionTag.IsOkSpecialExpression, sinfo, exp, `${exp.expstr}?ok`);
        this.oktype = oktype;
    }

    bsqemit(): any {
        return ["TreeIR::IsOkSpecialExpression", {...this.bsqemit_ti(), oktype: this.oktype}];
    }
    static bsqparse(jv: any): TIRIsOkSpecialExpression {
        return new TIRIsOkSpecialExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp), jv[1].oktype);
    }
}

class TIRIsErrSpecialExpression extends TIRITestIsSpecialExpression {
    readonly errtype: TIRTypeKey;

    constructor(sinfo: SourceInfo, exp: TIRExpression, errtype: TIRTypeKey) {
        super(TIRExpressionTag.IsErrSpecialExpression, sinfo, exp, `${exp.expstr}?err`);
        this.errtype = errtype;
    }

    bsqemit(): any {
        return ["TreeIR::IsErrSpecialExpression", {...this.bsqemit_ti(), errtype: this.errtype}];
    }
    static bsqparse(jv: any): TIRIsErrSpecialExpression {
        return new TIRIsErrSpecialExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp), jv[1].errtype);
    }
}

//abstract class for is literal compare operations
abstract class TIRITestIsLiteralEqExpression extends TIRTestIsExpression {
    readonly literal: TIRLiteralValue;

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, exp: TIRExpression, literal: TIRLiteralValue, exprstr: string) {
        super(tag, sinfo, exp, exprstr);
        this.literal = literal;
    }

    bsqemit_tle(): any {
        return {...this.bsqemit_ti(), literal: this.literal.bsqemit()};
    }
}

class TIRIsEqualToLiteralExpression extends TIRITestIsLiteralEqExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, literal: TIRLiteralValue) {
        super(TIRExpressionTag.IsEqualToLiteralExpression, sinfo, exp, literal, `${exp.expstr}?[${literal.litstr}]`);
    }

    bsqemit(): any {
        return ["TreeIR::IsEqualToLiteralExpression", this.bsqemit_tle()];
    }
    static bsqparse(jv: any): TIRIsEqualToLiteralExpression {
        return new TIRIsEqualToLiteralExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp), TIRLiteralValue.bsqparse(jv[1].literal));
    }
}

class TIRIsNotEqualToLiteralExpression extends TIRITestIsLiteralEqExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, literal: TIRLiteralValue) {
        super(TIRExpressionTag.IsNotEqualToLiteralExpression, sinfo, exp, literal, `${exp.expstr}?[!${literal.litstr}]`);
    }

    bsqemit(): any {
        return ["TreeIR::IsNotEqualToLiteralExpression", this.bsqemit_tle()];
    }
    static bsqparse(jv: any): TIRIsNotEqualToLiteralExpression {
        return new TIRIsNotEqualToLiteralExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp), TIRLiteralValue.bsqparse(jv[1].literal));
    }
}

//abstract class for is type compare operations
abstract class TIRITestIsTypeExpression extends TIRTestIsExpression {
    readonly ttype: TIRTypeKey;

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, exp: TIRExpression, ttype: TIRTypeKey, exprstr: string) {
        super(tag, sinfo, exp, exprstr);
        this.ttype = ttype;
    }

    bsqemit_tit(): any {
        return {...this.bsqemit_ti(), ttype: this.ttype};
    }
}

class TIRIsTypeExpression extends TIRITestIsTypeExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, ttype: TIRTypeKey) {
        super(TIRExpressionTag.IsTypeExpression, sinfo, exp, ttype, `${exp.expstr}?<${ttype}>`);
    }

    bsqemit(): any {
        return ["TreeIR::IsTypeExpression", this.bsqemit_tit()];
    }
    static bsqparse(jv: any): TIRIsTypeExpression {
        return new TIRIsTypeExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp), jv[1].ttype);
    }
}

class TIRIsNotTypeExpression  extends TIRITestIsTypeExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, ttype: TIRTypeKey) {
        super(TIRExpressionTag.IsNotTypeExpression, sinfo, exp, ttype, `${exp.expstr}?<!${ttype}>`);
    }

    bsqemit(): any {
        return ["TreeIR::IsNotTypeExpression", this.bsqemit_tit()];
    }
    static bsqparse(jv: any): TIRIsNotTypeExpression {
        return new TIRIsNotTypeExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp), jv[1].ttype);
    }
}

class TIRIsSubTypeExpression  extends TIRITestIsTypeExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, ttype: TIRTypeKey) {
        super(TIRExpressionTag.IsSubTypeExpression, sinfo, exp, ttype, `${exp.expstr}?<<:${ttype}>`);
    }

    bsqemit(): any {
        return ["TreeIR::IsSubTypeExpression", this.bsqemit_tit()];
    }
    static bsqparse(jv: any): TIRIsSubTypeExpression {
        return new TIRIsSubTypeExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp), jv[1].ttype);
    }
}

class TIRIsNotSubTypeExpression  extends TIRITestIsTypeExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, ttype: TIRTypeKey) {
        super(TIRExpressionTag.IsNotSubTypeExpression, sinfo, exp, ttype, `${exp.expstr}?<!<:${ttype}>`);
    }

    bsqemit(): any {
        return ["TreeIR::IsNotSubTypeExpression", this.bsqemit_tit()];
    }
    static bsqparse(jv: any): TIRIsNotSubTypeExpression {
        return new TIRIsNotSubTypeExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp), jv[1].ttype);
    }
}

//abstract class for as expressions
abstract class TIRAsExpression extends TIRExpression {
    readonly exp: TIRExpression;
    
    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, exp: TIRExpression, oftype: TIRTypeKey, exprstr: string) {
        super(tag, sinfo, oftype, exprstr);
        this.exp = exp;
    }
    
    bsqemit_ae(): any {
        return {...this.bsqemit_exp(), exp: this.exp.bsqemit()};
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

    bsqemit(): any {
        return ["TreeIR::AsNoneSpecialExpression", this.bsqemit_ae()];
    }
    static bsqparse(jv: any): TIRAsNoneSpecialExpression {
        return new TIRAsNoneSpecialExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp));
    }
}

class TIRAsSomeSpecialExpression extends TIRAsSpecialExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, oftype: TIRTypeKey) {
        super(TIRExpressionTag.AsSomeSpecialExpression, sinfo, exp, oftype, `${exp.expstr}@!none`);
    }

    bsqemit(): any {
        return ["TreeIR::AsSomeSpecialExpression", this.bsqemit_ae()];
    }
    static bsqparse(jv: any): TIRAsSomeSpecialExpression {
        return new TIRAsSomeSpecialExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp), jv[1].etype);
    }
}

class TIRAsNothingSpecialExpression extends TIRAsSpecialExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression) {
        super(TIRExpressionTag.AsNothingSpecialExpression, sinfo, exp, "Nothing", `${exp.expstr}@nothing`);
    }

    bsqemit(): any {
        return ["TreeIR::AsNothingSpecialExpression", this.bsqemit_ae()];
    }
    static bsqparse(jv: any): TIRAsNothingSpecialExpression {
        return new TIRAsNothingSpecialExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp));
    }
}

class TIRAsSomethingSpecialExpression extends TIRAsSpecialExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, oftype: TIRTypeKey) {
        super(TIRExpressionTag.AsSomethingSpecialExpression, sinfo, exp, oftype, `${exp.expstr}@something`);
    }

    bsqemit(): any {
        return ["TreeIR::AsSomethingSpecialExpression", this.bsqemit_ae()];
    }
    static bsqparse(jv: any): TIRAsSomethingSpecialExpression {
        return new TIRAsSomethingSpecialExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp), jv[1].etype);
    }
}

class TIRAsOkSpecialExpression extends TIRAsSpecialExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, oftype: TIRTypeKey) {
        super(TIRExpressionTag.AsOkSpecialExpression, sinfo, exp, oftype, `${exp.expstr}@ok`);
    }

    bsqemit(): any {
        return ["TreeIR::AsOkSpecialExpression", this.bsqemit_ae()];
    }
    static bsqparse(jv: any): TIRAsOkSpecialExpression {
        return new TIRAsOkSpecialExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp), jv[1].etype);
    }
}

class TIRAsErrSpecialExpression extends TIRAsSpecialExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, oftype: TIRTypeKey) {
        super(TIRExpressionTag.AsErrSpecialExpression, sinfo, exp, oftype, `${exp.expstr}@err`);
    }

    bsqemit(): any {
        return ["TreeIR::AsErrSpecialExpression", this.bsqemit_ae()];
    }
    static bsqparse(jv: any): TIRAsErrSpecialExpression {
        return new TIRAsErrSpecialExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp), jv[1].etype);
    }
}

//abstract class for is literal as operations
abstract class TIRIAsLiteralEqExpression extends TIRAsExpression {
    readonly literal: TIRLiteralValue;

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, exp: TIRExpression, literal: TIRLiteralValue, oftype: TIRTypeKey, exprstr: string) {
        super(tag, sinfo, exp, oftype, exprstr);
        this.literal = literal;
    }

    bsqemit_ael(): any {
        return {...this.bsqemit_ae(), literal: this.literal.bsqemit()};
    }
}

class TIRAsEqualToLiteralExpression extends TIRIAsLiteralEqExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, literal: TIRLiteralValue, oftype: TIRTypeKey) {
        super(TIRExpressionTag.AsEqualToLiteralExpression, sinfo, exp, literal, oftype, `${exp.expstr}@[${literal.litstr}]`);
    }

    bsqemit(): any {
        return ["TreeIR::AsEqualToLiteralExpression", this.bsqemit_ael()];
    }
    static bsqparse(jv: any): TIRAsEqualToLiteralExpression {
        return new TIRAsEqualToLiteralExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp), TIRLiteralValue.bsqparse(jv[1].literal), jv[1].etype);
    }
}

class TIRAsNotEqualToLiteralExpression extends TIRIAsLiteralEqExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, literal: TIRLiteralValue, oftype: TIRTypeKey) {
        super(TIRExpressionTag.AsNotEqualToLiteralExpression, sinfo, exp, literal, oftype, `${exp.expstr}@[!${literal.litstr}]`);
    }

    bsqemit(): any {
        return ["TreeIR::AsNotEqualToLiteralExpression", this.bsqemit_ael()];
    }
    static bsqparse(jv: any): TIRAsNotEqualToLiteralExpression {
        return new TIRAsNotEqualToLiteralExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp), TIRLiteralValue.bsqparse(jv[1].literal), jv[1].etype);
    }
}

//abstract class for is type as operations
abstract class TIRITestAsTypeExpression extends TIRAsExpression {
    readonly ttype: TIRTypeKey;

    constructor(tag: TIRExpressionTag, sinfo: SourceInfo, exp: TIRExpression, ttype: TIRTypeKey, oftype: TIRTypeKey, exprstr: string) {
        super(tag, sinfo, exp, oftype, exprstr);
        this.ttype = ttype;
    }

    bsqemit_aet(): any {
        return {...this.bsqemit_ae(), ttype: this.ttype};
    }
}

class TIRAsTypeExpression extends TIRITestAsTypeExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, ttype: TIRTypeKey, oftype: TIRTypeKey) {
        super(TIRExpressionTag.AsTypeExpression, sinfo, exp, ttype, oftype, `${exp.expstr}@<${ttype}>`);
    }

    bsqemit(): any {
        return ["TreeIR::AsTypeExpression", this.bsqemit_aet()];
    }
    static bsqparse(jv: any): TIRAsTypeExpression {
        return new TIRAsTypeExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp), jv[1].ttype, jv[1].etype);
    }
}

class TIRAsNotTypeExpression extends TIRITestAsTypeExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, ttype: TIRTypeKey, oftype: TIRTypeKey) {
        super(TIRExpressionTag.AsNotTypeExpression, sinfo, exp, ttype, oftype, `${exp.expstr}@<!${ttype}>`);
    }

    bsqemit(): any {
        return ["TreeIR::AsNotTypeExpression", this.bsqemit_aet()];
    }
    static bsqparse(jv: any): TIRAsNotTypeExpression {
        return new TIRAsNotTypeExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp), jv[1].ttype, jv[1].etype);
    }
}

class TIRAsSubTypeExpression extends TIRITestAsTypeExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, ttype: TIRTypeKey, oftype: TIRTypeKey) {
        super(TIRExpressionTag.AsSubTypeExpression, sinfo, exp, ttype, oftype, `${exp.expstr}@<<:${ttype}>`);
    }

    bsqemit(): any {
        return ["TreeIR::AsSubTypeExpression", this.bsqemit_aet()];
    }
    static bsqparse(jv: any): TIRAsSubTypeExpression {
        return new TIRAsSubTypeExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp), jv[1].ttype, jv[1].etype);
    }
}

class TIRAsNotSubTypeExpression extends TIRITestAsTypeExpression {
    constructor(sinfo: SourceInfo, exp: TIRExpression, ttype: TIRTypeKey, oftype: TIRTypeKey) {
        super(TIRExpressionTag.AsNotSubTypeExpression, sinfo, exp, ttype, oftype, `${exp.expstr}@<!<:${ttype}>`);
    }

    bsqemit(): any {
        return ["TreeIR::AsNotSubTypeExpression", this.bsqemit_aet()];
    }
    static bsqparse(jv: any): TIRAsNotSubTypeExpression {
        return new TIRAsNotSubTypeExpression(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp), jv[1].ttype, jv[1].etype);
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

    bsqemit_mf(): any {
        return {...this.bsqemit_exp(), tkey: this.tkey, fname: this.fname, fkey: this.fkey, fdecltype: this.fdecltype, thisarg: this.thisarg.bsqemit(), args: this.args.map((arg) => arg.bsqemit())};
    }
}

class TIRCallMemberFunctionExpression extends TIRIMemberFunctionExpression {
    constructor(sinfo: SourceInfo, tkey: TIRTypeKey, fname: string, fkey: TIRInvokeKey, fdecltype: TIRTypeKey, rtype: TIRTypeKey, thisarg: TIRExpression, args: TIRExpression[]) {
        super(TIRExpressionTag.CallMemberFunctionExpression, sinfo, tkey, fname, fkey, fdecltype, rtype, thisarg, args, `${thisarg.expstr}.${fkey}(${args.map((arg) => arg.expstr).join(", ")})`);
    }

    bsqemit(): any {
        return ["TreeIR::CallMemberFunctionExpression", this.bsqemit_mf()];
    }
    static bsqparse(jv: any): TIRCallMemberFunctionExpression {
        return new TIRCallMemberFunctionExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].tkey, jv[1].fname, jv[1].fkey, jv[1].fdecltype, jv[1].etype, TIRExpression.bsqparse(jv[1].thisarg), jv[1].args.map((arg: any) => TIRExpression.bsqparse(arg)));
    }
}

class TIRCallMemberFunctionDynamicExpression extends TIRIMemberFunctionExpression {
    constructor(sinfo: SourceInfo, tkey: TIRTypeKey, fname: string, declkey: TIRInvokeKey, fdecltype: TIRTypeKey, rtype: TIRTypeKey, thisarg: TIRExpression, args: TIRExpression[]) {
        super(TIRExpressionTag.CallMemberFunctionDynamicExpression, sinfo, tkey, fname, declkey, fdecltype, rtype, thisarg, args, `${thisarg.expstr}.${declkey}(${args.map((arg) => arg.expstr).join(", ")})`);
    }

    bsqemit(): any {
        return ["TreeIR::CallMemberFunctionDynamicExpression", this.bsqemit_mf()];
    }
    static bsqparse(jv: any): TIRCallMemberFunctionDynamicExpression {
        return new TIRCallMemberFunctionDynamicExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].tkey, jv[1].fname, jv[1].fkey, jv[1].fdecltype, jv[1].etype, TIRExpression.bsqparse(jv[1].thisarg), jv[1].args.map((arg: any) => TIRExpression.bsqparse(arg)));
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

    bsqemit(): any {
        return ["TreeIR::CallMemberFunctionSelfRefExpression", {...this.bsqemit_mf(), scidx: this.scidx, thisref: this.thisref}];
    }
    static bsqparse(jv: any): TIRCallMemberFunctionSelfRefExpression {
        return new TIRCallMemberFunctionSelfRefExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].scidx, jv[1].tkey, jv[1].fname, jv[1].fkey, jv[1].fdecltype, jv[1].etype, jv[1].thisref, TIRExpression.bsqparse(jv[1].thisarg), jv[1].args.map((arg: any) => TIRExpression.bsqparse(arg)));
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

    bsqemit_tf(): any {
        return {...this.bsqemit_exp(), fname: this.fname, fkey: this.fkey, tsktype: this.tsktype, args: this.args.map((arg) => arg.bsqemit())};
    }
}

class TIRCallMemberFunctionTaskExpression extends TIRFunctionTaskExpression {
    constructor(sinfo: SourceInfo, fname: string, fkey: TIRInvokeKey, rtype: TIRTypeKey, tsktype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.CallMemberFunctionTaskExpression, sinfo, fname, fkey, rtype, tsktype, args, `self.${fkey}(${args.map((arg) => arg.expstr).join(", ")})`);
    }

    bsqemit(): any {
        return ["TreeIR::CallMemberFunctionTaskExpression", this.bsqemit_tf()];
    }
    static bsqparse(jv: any): TIRCallMemberFunctionTaskExpression {
        return new TIRCallMemberFunctionTaskExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].fname, jv[1].fkey, jv[1].etype, jv[1].tsktype, jv[1].args.map((arg: any) => TIRExpression.bsqparse(arg)));
    }
}

class TIRCallMemberFunctionTaskSelfRefExpression extends TIRFunctionTaskExpression {
    readonly scidx: number;

    constructor(sinfo: SourceInfo, scidx: number, fname: string, fkey: TIRInvokeKey, rtype: TIRTypeKey, tsktype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.CallMemberFunctionTaskSelfRefExpression, sinfo, fname, fkey, rtype, tsktype, args, `ref self.${fkey}(${args.map((arg) => arg.expstr).join(", ")})`);
        this.scidx = scidx;
    }

    bsqemit(): any {
        return ["TreeIR::CallMemberFunctionTaskSelfRefExpression", {...this.bsqemit_tf(), scidx: this.scidx}];
    }
    static bsqparse(jv: any): TIRCallMemberFunctionTaskSelfRefExpression {
        return new TIRCallMemberFunctionTaskSelfRefExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].scidx, jv[1].fname, jv[1].fkey, jv[1].etype, jv[1].tsktype, jv[1].args.map((arg: any) => TIRExpression.bsqparse(arg)));
    }
}

class TIRCallMemberActionExpression extends TIRFunctionTaskExpression {
    readonly scidx: number;

    constructor(sinfo: SourceInfo, scidx: number, fname: string, fkey: TIRInvokeKey, rtype: TIRTypeKey, tsktype: TIRTypeKey, args: TIRExpression[]) {
        super(TIRExpressionTag.CallMemberActionExpression, sinfo, fname, fkey, rtype, tsktype, args, `self.${fkey}(${args.map((arg) => arg.expstr).join(", ")})`);
        this.scidx = scidx;
    }

    bsqemit(): any {
        return ["TreeIR::CallMemberActionExpression", {...this.bsqemit_tf(), scidx: this.scidx}];
    }
    static bsqparse(jv: any): TIRCallMemberActionExpression {
        return new TIRCallMemberActionExpression(SourceInfo.bsqparse(jv[1].sinfo), jv[1].scidx, jv[1].fname, jv[1].fkey, jv[1].etype, jv[1].tsktype, jv[1].args.map((arg: any) => TIRExpression.bsqparse(arg)));
    }
}

class TIRLiteralValue {
    readonly exp: TIRExpression;
    readonly litstr: string;
    
    constructor(exp: TIRExpression, litstr: string) {
        this.exp = exp
        this.litstr = litstr;
    }

    bsqemit(): any {
        return {exp: this.exp.bsqemit(), litstr: this.litstr};
    }
    static bsqparse(jv: any): TIRLiteralValue {
        return new TIRLiteralValue(TIRExpression.bsqparse(jv[1].exp), jv[1].litstr);
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

    bsqemit_stmt(): any {
        return {sinfo: this.sinfo.bsqemit()};
    }

    abstract bsqemit(): any;

    static bsqparse(jv: any): TIRStatement {
        if(jv[0] === "TreeIR::NopStatement") {
            return TIRNopStatement.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::AbortStatement") {
            return TIRAbortStatement.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::AssertCheckStatement") {
            return TIRAssertCheckStatement.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::DebugStatement") {
            return TIRDebugStatement.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::VarDeclareStatement") {
            return TIRVarDeclareStatement.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::VarAssignStatement") {
            return TIRVarAssignStatement.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::VarDeclareAndAssignStatement") {
            return TIRVarDeclareAndAssignStatement.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::StoreToScratch") {
            return TIRStoreToScratch.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::VarRefAssignFromScratch") {
            return TIRVarRefAssignFromScratch.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::TaskRefAssignFromScratch") {
            return TIRTaskRefAssignFromScratch.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::CallStatementWRef") {
            return TIRCallStatementWRef.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::CallStatementWTaskRef") {
            return TIRCallStatementWTaskRef.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::CallStatementWTaskAction") {
            return TIRCallStatementWAction.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::VariableRetypeStatement") {
            return TIRVariableRetypeStatement.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::VariableSCRetypeStatement") {
            return TIRVariableSCRetypeStatement.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::ScratchSCStatement") {
            return TIRScratchSCStatement.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::ReturnStatement") {
            return TIRReturnStatement.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::ReturnStatementWRef") {
            return TIRReturnStatementWRef.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::ReturnStatementWTaskRef") {
            return TIRReturnStatementWTaskRef.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::ReturnStatementWAction") {
            return TIRReturnStatementWAction.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::IfStatement") {
            return TIRIfStatement.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::SwitchStatement") {
            return TIRSwitchStatement.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::MatchStatement") {
            return TIRMatchStatement.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::EnvironmentFreshStatement") {
            return TIREnvironmentFreshStatement.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::EnvironmentSetStatement") {
            return TIREnvironmentSetStatement.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::EnvironmentSetStatementBracket") {
            return TIREnvironmentSetStatementBracket.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::TaskRunStatement") {
            return TIRTaskRunStatement.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::TaskMultiStatement") {
            return TIRTaskMultiStatement.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::TaskDashStatement") {
            return TIRTaskDashStatement.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::TaskAllStatement") {
            return TIRTaskAllStatement.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::TaskRaceStatement") {
            return TIRTaskRaceStatement.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::TaskSetSelfFieldStatement") {
            return TIRTaskSetSelfFieldStatement.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::LoggerEmitStatement") {
            return TIRLoggerEmitStatement.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::LoggerEmitConditionalStatement") {
            return TIRLoggerEmitConditionalStatement.bsqparse(jv);
        }
        else if(jv[0] === "TreeIR::LoggerSetPrefixStatement") {
            return TIRLoggerSetPrefixStatement.bsqparse(jv);
        }
        else {
            assert(false, "unhandled parse of TIRStatementTag: " + jv[0]);

            return (undefined as any) as TIRStatement;
        }
    }
}

class TIRNopStatement extends TIRStatement {
    constructor(sinfo: SourceInfo) {
        super(TIRStatementTag.NopStatement, sinfo, "nop;");
    }

    bsqemit(): any {
        return ["TreeIR::NopStatement", this.bsqemit_stmt()];
    }
    static bsqparse(jv: any): TIRNopStatement {
        return new TIRNopStatement(SourceInfo.bsqparse(jv[1].sinfo));
    }
}

class TIRAbortStatement extends TIRStatement {
    readonly msg: string;

    constructor(sinfo: SourceInfo, msg: string) {
        super(TIRStatementTag.AbortStatement, sinfo, `abort("${msg}");`);
        this.msg = msg;
    }

    bsqemit(): any {
        return ["TreeIR::AbortStatement", {...this.bsqemit_stmt(), msg: this.msg}];
    }
    static bsqparse(jv: any): TIRAbortStatement {
        return new TIRAbortStatement(SourceInfo.bsqparse(jv[1].sinfo), jv[1].msg);
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

    bsqemit(): any {
        return ["TreeIR::AssertCheckStatement", {...this.bsqemit_stmt(), cond: this.cond.bsqemit(), msg: this.msg}];
    }
    static bsqparse(jv: any): TIRAssertCheckStatement {
        return new TIRAssertCheckStatement(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].cond), jv[1].msg);
    }
}

class TIRDebugStatement extends TIRStatement {
    readonly value: TIRExpression;

    constructor(sinfo: SourceInfo, value: TIRExpression) {
        super(TIRStatementTag.DebugStatement, sinfo, `__debug(${value.expstr});`);
        this.value = value;
    }

    bsqemit(): any {
        return ["TreeIR::DebugStatement", {...this.bsqemit_stmt(), value: this.value.bsqemit()}];
    }
    static bsqparse(jv: any): TIRDebugStatement {
        return new TIRDebugStatement(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].value));
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

    bsqemit(): any {
        return ["TreeIR::VarDeclareStatement", {...this.bsqemit_stmt(), vname: this.vname, vtype: this.vtype}];
    }
    static bsqparse(jv: any): TIRVarDeclareStatement {
        return new TIRVarDeclareStatement(SourceInfo.bsqparse(jv[1].sinfo), jv[1].vname, jv[1].vtype);
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

    bsqemit(): any {
        return ["TreeIR::VarDeclareAndAssignStatement", {...this.bsqemit_stmt(), vname: this.vname, vtype: this.vtype, vexp: this.vexp.bsqemit(), isConst: this.isConst}];
    }
    static bsqparse(jv: any): TIRVarDeclareAndAssignStatement {
        return new TIRVarDeclareAndAssignStatement(SourceInfo.bsqparse(jv[1].sinfo), jv[1].vname, jv[1].vtype, TIRExpression.bsqparse(jv[1].vexp), jv[1].isConst);
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

    bsqemit(): any {
        return ["TreeIR::VarAssignStatement", {...this.bsqemit_stmt(), vname: this.vname, vtype: this.vtype, vexp: this.vexp.bsqemit()}];
    }
    static bsqparse(jv: any): TIRVarAssignStatement {
        return new TIRVarAssignStatement(SourceInfo.bsqparse(jv[1].sinfo), jv[1].vname, jv[1].vtype, TIRExpression.bsqparse(jv[1].vexp));
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

    bsqemit(): any {
        return ["TreeIR::StoreToScratch", {...this.bsqemit_stmt(), exp: this.exp.bsqemit(), vtype: this.vtype, scidx: this.scidx}];
    }
    static bsqparse(jv: any): TIRStoreToScratch {
        return new TIRStoreToScratch(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].exp), jv[1].vtype, jv[1].scidx);
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

    bsqemit(): any {
        return ["TreeIR::VarRefAssignFromScratch", {...this.bsqemit_stmt(), vname: this.vname, vtype: this.vtype, scidx: this.scidx}];
    }
    static bsqparse(jv: any): TIRVarRefAssignFromScratch {
        return new TIRVarRefAssignFromScratch(SourceInfo.bsqparse(jv[1].sinfo), jv[1].vname, jv[1].vtype, jv[1].scidx);
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

    bsqemit(): any {
        return ["TreeIR::TaskRefAssignFromScratch", {...this.bsqemit_stmt(), vtype: this.vtype, scidx: this.scidx}];
    }
    static bsqparse(jv: any): TIRTaskRefAssignFromScratch {
        return new TIRTaskRefAssignFromScratch(SourceInfo.bsqparse(jv[1].sinfo), jv[1].vtype, jv[1].scidx);
    }
}

abstract class TIRCallWRefStatementGeneral extends TIRStatement {
    readonly vexp: TIRExpression;
    readonly restype: TIRTypeKey;
    readonly reftype: TIRTypeKey;
    readonly sidx: number;
    //always stores to scratch location as a EList

    constructor(tag: TIRStatementTag, sinfo: SourceInfo, vexp: TIRExpression, restype: TIRTypeKey, reftype: TIRTypeKey, sidx: number) {
        super(tag, sinfo, `${vexp.expstr};`);
        this.vexp = vexp;
        this.restype = restype;
        this.reftype = reftype;
        this.sidx = sidx;
    }

    bsqemit_cwr(): any {
        return {...this.bsqemit_stmt(), vexp: this.vexp.bsqemit(), restype: this.restype, reftype: this.reftype, sidx: this.sidx};
    }
}

class TIRCallStatementWRef extends TIRCallWRefStatementGeneral {
    constructor(sinfo: SourceInfo, vexp: TIRExpression, restype: TIRTypeKey, reftype: TIRTypeKey, sidx: number) {
        super(TIRStatementTag.CallWRefStatement, sinfo, vexp, restype, reftype, sidx);
    }

    bsqemit(): any {
        return ["TreeIR::CallStatementWRef", this.bsqemit_cwr()];
    }
    static bsqparse(jv: any): TIRCallStatementWRef {
        return new TIRCallStatementWRef(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].vexp), jv[1].restype, jv[1].reftype, jv[1].sidx);
    }
}

class TIRCallStatementWTaskRef extends TIRCallWRefStatementGeneral {
    constructor(sinfo: SourceInfo, vexp: TIRExpression, restype: TIRTypeKey, reftype: TIRTypeKey, sidx: number) {
        super(TIRStatementTag.CallStatementWTaskRef, sinfo, vexp, restype, reftype, sidx);
    }

    bsqemit(): any {
        return ["TreeIR::CallStatementWTaskRef", this.bsqemit_cwr()];
    }
    static bsqparse(jv: any): TIRCallStatementWTaskRef {
        return new TIRCallStatementWTaskRef(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].vexp), jv[1].restype, jv[1].reftype, jv[1].sidx);
    }
}

class TIRCallStatementWAction extends TIRCallWRefStatementGeneral {
    constructor(sinfo: SourceInfo, vexp: TIRExpression, restype: TIRTypeKey, reftype: TIRTypeKey, sidx: number) {
        super(TIRStatementTag.CallStatementWTaskAction, sinfo, vexp, restype, reftype, sidx);
    }

    bsqemit(): any {
        return ["TreeIR::CallStatementWAction", this.bsqemit_cwr()];
    }
    static bsqparse(jv: any): TIRCallStatementWAction {
        return new TIRCallStatementWAction(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].vexp), jv[1].restype, jv[1].reftype, jv[1].sidx);
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

    bsqemit(): any {
        return ["TreeIR::VariableRetypeStatement", {...this.bsqemit_stmt(), vname: this.vname, origtype: this.origtype, newtype: this.newtype, asconv: this.asconv.bsqemit()}];
    }
    static bsqparse(jv: any): TIRVariableRetypeStatement {
        return new TIRVariableRetypeStatement(SourceInfo.bsqparse(jv[1].sinfo), jv[1].vname, jv[1].origtype, jv[1].newtype, TIRExpression.bsqparse(jv[1].asconv));
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

    bsqemit(): any {
        return ["TreeIR::VariableSCRetypeStatement", {...this.bsqemit_stmt(), vname: this.vname, origtype: this.origtype, vtest: this.test.bsqemit(), asconv: this.asconv.bsqemit(), resexp: this.resexp.bsqemit(), binderinfo: this.binderinfo !== undefined ? [this.binderinfo[0].bsqemit(), this.binderinfo[1]] : null}];
    }
    static bsqparse(jv: any): TIRVariableSCRetypeStatement {
        return new TIRVariableSCRetypeStatement(SourceInfo.bsqparse(jv[1].sinfo), jv[1].vname, jv[1].origtype, TIRExpression.bsqparse(jv[1].vtest), TIRExpression.bsqparse(jv[1].asconv), TIRExpression.bsqparse(jv[1].resexp), jv[1].binderinfo !== null ? [TIRExpression.bsqparse(jv[1].binderinfo[0]), jv[1].binderinfo[1]] : undefined);
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

    bsqemit(): any {
        return ["TreeIR::ScratchSCStatement", {...this.bsqemit_stmt(), sidx: this.sidx, pos: this.pos !== undefined ? this.pos : null, origtype: this.origtype, vtest: this.test.bsqemit(), resexp: this.resexp.bsqemit(), binderinfo: this.binderinfo !== undefined ? [this.binderinfo[0].bsqemit(), this.binderinfo[1]] : null}];
    }
    static bsqparse(jv: any): TIRScratchSCStatement {
        return new TIRScratchSCStatement(SourceInfo.bsqparse(jv[1].sinfo), jv[1].sidx, jv[1].pos !== null ? jv[1].pos : undefined, jv[1].origtype, TIRExpression.bsqparse(jv[1].vtest), TIRExpression.bsqparse(jv[1].asconv), TIRExpression.bsqparse(jv[1].resexp), jv[1].binderinfo !== null ? [TIRExpression.bsqparse(jv[1].binderinfo[0]), jv[1].binderinfo[1]] : undefined);
    }
}

abstract class TIRReturnStatementGeneral extends TIRStatement {
    readonly value: TIRExpression;

    constructor(tag: TIRStatementTag, sinfo: SourceInfo, value: TIRExpression, stmtstr: string) {
        super(tag, sinfo, stmtstr);
        this.value = value;
    }

    bsqemit_rg(): any {
        return {...this.bsqemit_stmt(), value: this.value.bsqemit()};
    }
}

class TIRReturnStatement extends TIRReturnStatementGeneral {
    constructor(sinfo: SourceInfo, value: TIRExpression) {
        super(TIRStatementTag.ReturnStatement, sinfo, value, `return ${value.expstr};`);
    }

    bsqemit(): any {
        return ["TreeIR::ReturnStatement", this.bsqemit_rg()];
    }
    static bsqparse(jv: any): TIRReturnStatement {
        return new TIRReturnStatement(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].value));
    }
}

class TIRReturnStatementWRef extends TIRReturnStatementGeneral {
    constructor(sinfo: SourceInfo, value: TIRExpression) {
        super(TIRStatementTag.ReturnStatementWRef, sinfo, value, `return ${value.expstr};`);
    }

    bsqemit(): any {
        return ["TreeIR::ReturnStatementWRef", this.bsqemit_rg()];
    }
    static bsqparse(jv: any): TIRReturnStatementWRef {
        return new TIRReturnStatementWRef(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].value));
    }
}

class TIRReturnStatementWTaskRef extends TIRReturnStatementGeneral {
    constructor(sinfo: SourceInfo, value: TIRExpression) {
        super(TIRStatementTag.ReturnStatementWTaskRef, sinfo, value, `return ${value.expstr};`);
    }

    bsqemit(): any {
        return ["TreeIR::ReturnStatementWTaskRef", this.bsqemit_rg()];
    }
    static bsqparse(jv: any): TIRReturnStatementWTaskRef {
        return new TIRReturnStatementWTaskRef(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].value));
    }
}

class TIRReturnStatementWAction extends TIRReturnStatementGeneral {
    constructor(sinfo: SourceInfo, value: TIRExpression) {
        super(TIRStatementTag.ReturnStatementWAction, sinfo, value, `return ${value.expstr};`);
    }

    bsqemit(): any {
        return ["TreeIR::ReturnStatementWAction", this.bsqemit_rg()];
    }
    static bsqparse(jv: any): TIRReturnStatementWAction {
        return new TIRReturnStatementWAction(SourceInfo.bsqparse(jv[1].sinfo), TIRExpression.bsqparse(jv[1].value));
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

    bsqemit(): any {
        return ["TreeIR::IfStatement", {
            ...this.bsqemit_stmt(), 
            ifentry: {etest: this.ifentry.test.bsqemit(), value: this.ifentry.value.bsqemit(), binderinfo: this.ifentry.binderinfo !== undefined ? [this.ifentry.binderinfo[0].bsqemit(), this.ifentry.binderinfo[1], this.ifentry.binderinfo[2].bsqemit(), this.ifentry.binderinfo[3]] : null, recasttypes: this.ifentry.recasttypes.map((rt) => ({vname: rt.vname, cast: rt.cast.bsqemit()}))}, 
            elifentries: this.elifentries.map((efi) => ({etest: efi.test.bsqemit(), value: efi.value.bsqemit(), binderinfo: efi.binderinfo !== undefined ? [efi.binderinfo[0].bsqemit(), efi.binderinfo[1], efi.binderinfo[2].bsqemit(), efi.binderinfo[3]] : null, recasttypes: efi.recasttypes.map((rt) => ({vname: rt.vname, cast: rt.cast.bsqemit()}))})), 
            elseentry: {value: this.elseentry.value.bsqemit(), binderinfo: this.elseentry.binderinfo !== undefined ? [this.elseentry.binderinfo[0].bsqemit(), this.elseentry.binderinfo[1], this.elseentry.binderinfo[2].bsqemit(), this.elseentry.binderinfo[3]] : null, recasttypes: this.elseentry.recasttypes.map((rt) => ({vname: rt.vname, cast: rt.cast.bsqemit()}))}
        }];
    }
    static bsqparse(jv: any): TIRIfStatement {
        return new TIRIfStatement(
            SourceInfo.bsqparse(jv[1].sinfo),
            {test: TIRExpression.bsqparse(jv[1].ifentry.etest), value: TIRScopedBlockStatement.bsqparse(jv[1].ifentry.value), binderinfo: jv[1].ifentry.binderinfo !== null ? [TIRExpression.bsqparse(jv[1].ifentry.binderinfo[0]), jv[1].ifentry.binderinfo[1], TIRExpression.bsqparse(jv[1].ifentry.binderinfo[2]), jv[1].ifentry.binderinfo[3]] : undefined, recasttypes: jv[1].ifentry.recasttypes.map((rt: any) => ({vname: rt.vname, cast: TIRExpression.bsqparse(rt.cast)}))},
            jv[1].elifentries.map((efi: any) => ({test: TIRExpression.bsqparse(efi.etest), value: TIRScopedBlockStatement.bsqparse(efi.value), binderinfo: efi.binderinfo !== null ? [TIRExpression.bsqparse(efi.binderinfo[0]), efi.binderinfo[1], TIRExpression.bsqparse(efi.binderinfo[2]), efi.binderinfo[3]] : undefined, recasttypes: efi.recasttypes.map((rt: any) => ({vname: rt.vname, cast: TIRExpression.bsqparse(rt.cast)}))})),
            {value: TIRScopedBlockStatement.bsqparse(jv[1].elseentry.value), binderinfo: jv[1].elseentry.binderinfo !== null ? [TIRExpression.bsqparse(jv[1].elseentry.binderinfo[0]), jv[1].elseentry.binderinfo[1], TIRExpression.bsqparse(jv[1].elseentry.binderinfo[2]), jv[1].elseentry.binderinfo[3]] : undefined, recasttypes: jv[1].elseentry.recasttypes.map((rt: any) => ({vname: rt.vname, cast: TIRExpression.bsqparse(rt.cast)}))}
        )
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

    bsqemit(): any {
        return ["TreeIR::SwitchStatement", {
            ...this.bsqemit_stmt(), 
            exp: this.exp.bsqemit(), 
            scratchidx: this.scratchidx, 
            clauses: this.clauses.map((ci) => ({ematch: ci.match.bsqemit(), value: ci.value.bsqemit(), binderinfo: ci.binderinfo !== undefined ? [ci.binderinfo[0].bsqemit(), ci.binderinfo[1]] : null, recasttypes: ci.recasttypes.map((rt) => ({vname: rt.vname, cast: rt.cast.bsqemit()}))})), 
            edefault: this.edefault !== undefined ? {value: this.edefault.value.bsqemit(), binderinfo: this.edefault.binderinfo !== undefined ? [this.edefault.binderinfo[0].bsqemit(), this.edefault.binderinfo[1]] : null, recasttypes: this.edefault.recasttypes.map((rt) => ({vname: rt.vname, cast: rt.cast.bsqemit()}))} : null, 
            isexhaustive: this.isexhaustive
        }];
    }
    static bsqparse(jv: any): TIRSwitchStatement {
        return new TIRSwitchStatement(
            SourceInfo.bsqparse(jv[1].sinfo),
            TIRExpression.bsqparse(jv[1].exp), jv[1].scratchidx,
            jv[1].clauses.map((ci: any) => ({match: TIRExpression.bsqparse(ci.ematch), value: TIRScopedBlockStatement.bsqparse(ci.value), binderinfo: ci.binderinfo !== null ? [TIRExpression.bsqparse(ci.binderinfo[0]), ci.binderinfo[1]] : undefined, recasttypes: ci.recasttypes.map((rt: any) => ({vname: rt.vname, cast: TIRExpression.bsqparse(rt.cast)}))})),
            jv[1].edefault !== null ? {value: TIRScopedBlockStatement.bsqparse(jv[1].edefault.value), binderinfo: jv[1].edefault.binderinfo !== null ? [TIRExpression.bsqparse(jv[1].edefault.binderinfo[0]), jv[1].edefault.binderinfo[1]] : undefined, recasttypes: jv[1].edefault.recasttypes.map((rt: any) => ({vname: rt.vname, cast: TIRExpression.bsqparse(rt.cast)}))} : undefined,
            jv[1].isexhaustive
        )
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

    bsqemit(): any {
        return ["TreeIR::MatchStatement", {
            ...this.bsqemit_stmt(), 
            exp: this.exp.bsqemit(), 
            scratchidx: this.scratchidx, 
            clauses: this.clauses.map((ci) => ({ematch: ci.match.bsqemit(), value: ci.value.bsqemit(), binderinfo: ci.binderinfo !== undefined ? [ci.binderinfo[0].bsqemit(), ci.binderinfo[1]] : null, recasttypes: ci.recasttypes.map((rt) => ({vname: rt.vname, cast: rt.cast.bsqemit()}))})), 
            edefault: this.edefault !== undefined ? {value: this.edefault.value.bsqemit(), binderinfo: this.edefault.binderinfo !== undefined ? [this.edefault.binderinfo[0].bsqemit(), this.edefault.binderinfo[1]] : null, recasttypes: this.edefault.recasttypes.map((rt) => ({vname: rt.vname, cast: rt.cast.bsqemit()}))} : null, 
            isexhaustive: this.isexhaustive
        }];
    }
    static bsqparse(jv: any): TIRMatchStatement {
        return new TIRMatchStatement(
            SourceInfo.bsqparse(jv[1].sinfo),
            TIRExpression.bsqparse(jv[1].exp), jv[1].scratchidx,
            jv[1].clauses.map((ci: any) => ({match: TIRExpression.bsqparse(ci.ematch), value: TIRScopedBlockStatement.bsqparse(ci.value), binderinfo: ci.binderinfo !== null ? [TIRExpression.bsqparse(ci.binderinfo[0]), ci.binderinfo[1]] : undefined, recasttypes: ci.recasttypes.map((rt: any) => ({vname: rt.vname, cast: TIRExpression.bsqparse(rt.cast)}))})),
            jv[1].edefault !== null ? {value: TIRScopedBlockStatement.bsqparse(jv[1].edefault.value), binderinfo: jv[1].edefault.binderinfo !== null ? [TIRExpression.bsqparse(jv[1].edefault.binderinfo[0]), jv[1].edefault.binderinfo[1]] : undefined, recasttypes: jv[1].edefault.recasttypes.map((rt: any) => ({vname: rt.vname, cast: TIRExpression.bsqparse(rt.cast)}))} : undefined,
            jv[1].isexhaustive
        )
    }
}

class TIREnvironmentFreshStatement extends TIRStatement {
    readonly assigns: {keyname: string, valexp: [TIRTypeKey, TIRExpression]}[];

    constructor(sinfo: SourceInfo, assigns: {keyname: string, valexp: [TIRTypeKey, TIRExpression]}[]) {
        super(TIRStatementTag.EnvironmentFreshStatement, sinfo, `env{${assigns.map((asgn) => asgn.keyname + ": " + asgn.valexp[0] + "=" + asgn.valexp[1].expstr).join(", ")}};`);
        this.assigns = assigns;
    }

    bsqemit(): any {
        return ["TreeIR::EnvironmentFreshStatement", {...this.bsqemit_stmt(), assigns: this.assigns.map((asgn) => ({keyname: asgn.keyname, valexp: [asgn.valexp[0], asgn.valexp[1].bsqemit()]}))}];
    }
    static bsqparse(jv: any): TIREnvironmentFreshStatement {
        return new TIREnvironmentFreshStatement(SourceInfo.bsqparse(jv[1].sinfo), jv[1].assigns.map((asgn: any) => ({keyname: asgn.keyname, valexp: [asgn.valexp[0], TIRExpression.bsqparse(asgn.valexp[1])]})))
    }
}

class TIREnvironmentSetStatement extends TIRStatement {
    readonly assigns: {keyname: string, valexp: [TIRTypeKey, TIRExpression] | undefined}[];

    constructor(sinfo: SourceInfo, assigns: {keyname: string, valexp: [TIRTypeKey, TIRExpression] | undefined}[]) {
        super(TIRStatementTag.EnvironmentFreshStatement, sinfo, `env[${assigns.map((asgn) => asgn.keyname + (asgn.valexp !== undefined ? (": " + asgn.valexp[0] + "=" + asgn.valexp[1].expstr) : "=_")).join(", ")}];`);
        this.assigns = assigns;
    }

    bsqemit(): any {
        return ["TreeIR::EnvironmentSetStatement", {...this.bsqemit_stmt(), assigns: this.assigns.map((asgn) => ({keyname: asgn.keyname, valexp: asgn.valexp !== undefined ? [asgn.valexp[0], asgn.valexp[1].bsqemit()] : null}))}];
    }
    static bsqparse(jv: any): TIREnvironmentSetStatement {
        return new TIREnvironmentSetStatement(SourceInfo.bsqparse(jv[1].sinfo), jv[1].assigns.map((asgn: any) => ({keyname: asgn.keyname, valexp: asgn.valexp !== null ? [asgn.valexp[0], TIRExpression.bsqparse(asgn.valexp[1])] : undefined})))
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

    bsqemit(): any {
        return ["TreeIR::EnvironmentSetStatementBracket", {...this.bsqemit_stmt(), assigns: this.assigns.map((asgn) => ({keyname: asgn.keyname, valexp: asgn.valexp !== undefined ? [asgn.valexp[0], asgn.valexp[1].bsqemit()] : null})), block: this.block.bsqemit(), isFresh: this.isFresh}];
    }
    static bsqparse(jv: any): TIREnvironmentSetStatementBracket {
        return new TIREnvironmentSetStatementBracket(SourceInfo.bsqparse(jv[1].sinfo), jv[1].assigns.map((asgn: any) => ({keyname: asgn.keyname, valexp: asgn.valexp !== null ? [asgn.valexp[0], TIRExpression.bsqparse(asgn.valexp[1])] : undefined})), TIRUnscopedBlockStatement.bsqparse(jv[1].block), jv[1].isFresh)
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

    bsqemit_tes(): any {
        return {...this.bsqemit_stmt(), isdefine: this.isdefine, isconst: this.isconst};
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

    bsqemit(): any {
        return ["TreeIR::TaskRunStatement", {...this.bsqemit_tes(), vtrgt: this.vtrgt, ttask: this.task, taskargs: this.taskargs, consarg: this.consarg, args: this.args.map((arg) => arg.bsqemit())}];
    }
    static bsqparse(jv: any): TIRTaskRunStatement {
        return new TIRTaskRunStatement(SourceInfo.bsqparse(jv[1].sinfo), jv[1].isdefine, jv[1].isconst, jv[1].vtrgt, jv[1].ttask, jv[1].taskargs, jv[1].consarg, jv[1].args.map((arg: any) => TIRExpression.bsqparse(arg)));
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

    bsqemit(): any {
        return ["TreeIR::TaskMultiStatement", {...this.bsqemit_tes(), vtrgts: this.vtrgts, tasks: this.tasks.map((task) => ({ttask: task.task, targs: task.targs, argtype: task.argtype, consargtype: task.consargtype, argexp: task.argexp.bsqemit()}))}];
    }
    static bsqparse(jv: any): TIRTaskMultiStatement {
        return new TIRTaskMultiStatement(SourceInfo.bsqparse(jv[1].sinfo), jv[1].isdefine, jv[1].isconst, jv[1].vtrgts, jv[1].tasks.map((task: any) => ({ttask: task.task, targs: task.targs, argtype: task.argtype, consargtype: task.consargtype, argexp: TIRExpression.bsqparse(task.argexp)})));
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

    bsqemit(): any {
        return ["TreeIR::TaskDashStatement", {...this.bsqemit_tes(), vtrgts: this.vtrgts, tasks: this.tasks.map((task) => ({ttask: task.task, targs: task.targs, argtype: task.argtype, consargtype: task.consargtype, argexp: task.argexp.bsqemit()}))}];
    }
    static bsqparse(jv: any): TIRTaskDashStatement {
        return new TIRTaskDashStatement(SourceInfo.bsqparse(jv[1].sinfo), jv[1].isdefine, jv[1].isconst, jv[1].vtrgts, jv[1].tasks.map((task: any) => ({ttask: task.task, targs: task.targs, argtype: task.argtype, consargtype: task.consargtype, argexp: TIRExpression.bsqparse(task.argexp)})));
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

    bsqemit(): any {
        return ["TreeIR::TaskAllStatement", {...this.bsqemit_tes(), vtrgt: this.vtrgt, ttask: this.task, taskargs: this.taskargs, arg: this.arg.bsqemit(), arglisttype: this.arglisttype, argentrytype: this.argentrytype}];
    }
    static bsqparse(jv: any): TIRTaskAllStatement {
        return new TIRTaskAllStatement(SourceInfo.bsqparse(jv[1].sinfo), jv[1].isdefine, jv[1].isconst, jv[1].vtrgt, jv[1].ttask, jv[1].taskargs, TIRExpression.bsqparse(jv[1].arg), jv[1].arglisttype, jv[1].argentrytype);
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

    bsqemit(): any {
        return ["TreeIR::TaskRaceStatement", {...this.bsqemit_tes(), vtrgt: this.vtrgt, ttask: this.task, taskargs: this.taskargs, arg: this.arg.bsqemit(), arglisttype: this.arglisttype, argentrytype: this.argentrytype}];
    }
    static bsqparse(jv: any): TIRTaskRaceStatement {
        return new TIRTaskRaceStatement(SourceInfo.bsqparse(jv[1].sinfo), jv[1].isdefine, jv[1].isconst, jv[1].vtrgt, jv[1].ttask, jv[1].taskargs, TIRExpression.bsqparse(jv[1].arg), jv[1].arglisttype, jv[1].argentrytype);
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

    bsqemit(): any {
        return ["TreeIR::TaskSetSelfFieldStatement", {sinfo: this.sinfo.bsqemit(), tasktype: this.tasktype, sfield: this.field, fname: this.fname, value: this.value.bsqemit()}];
    }
    static bsqparse(jv: any): TIRTaskSetSelfFieldStatement {
        return new TIRTaskSetSelfFieldStatement(SourceInfo.bsqparse(jv[1].sinfo), jv[1].tasktype, jv[1].sfield, jv[1].fname, TIRExpression.bsqparse(jv[1].value));
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

    bsqemit(): any {
        return ["TreeIR::LoggerEmitStatement", {sinfo: this.sinfo.bsqemit(), level: this.level, fmt: this.fmt, args: this.args.map((arg) => arg.bsqemit())}];
    }
    static bsqparse(jv: any): TIRLoggerEmitStatement {
        return new TIRLoggerEmitStatement(SourceInfo.bsqparse(jv[1].sinfo), jv[1].level, jv[1].fmt, jv[1].args.map((arg: any) => TIRExpression.bsqparse(arg)));
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

    bsqemit(): any {
        return ["TreeIR::LoggerEmitConditionalStatement", {sinfo: this.sinfo.bsqemit(), level: this.level, fmt: this.fmt, cond: this.cond.bsqemit(), args: this.args.map((arg) => arg.bsqemit())}];
    }
    static bsqparse(jv: any): TIRLoggerEmitConditionalStatement {
        return new TIRLoggerEmitConditionalStatement(SourceInfo.bsqparse(jv[1].sinfo), jv[1].level, TIRExpression.bsqparse(jv[1].cond), jv[1].fmt, jv[1].args.map((arg: any) => TIRExpression.bsqparse(arg)));
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

    bsqemit(): any {
        return ["TreeIR::LoggerSetPrefixStatement", {sinfo: this.sinfo.bsqemit(), fmt: this.fmt, args: this.args.map((arg) => arg.bsqemit()), block: this.block.bsqemit()}];
    }
    static bsqparse(jv: any): TIRLoggerSetPrefixStatement {
        return new TIRLoggerSetPrefixStatement(SourceInfo.bsqparse(jv[1].sinfo), jv[1].fmt, TIRScopedBlockStatement.bsqparse(jv[1].block), jv[1].args.map((arg: any) => TIRExpression.bsqparse(arg)));
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

    bsqemit_blck(): any {
        return {ops: this.ops.map((op) => op.bsqemit()), isterminal: this.isterminal};
    }
} 

class TIRUnscopedBlockStatement extends TIRBlockStatement {
    constructor(ops: TIRStatement[]) {
        super(ops, false);
    }

    bsqemit(): any {
        return ["TreeIR::UnscopedBlockStatement", this.bsqemit_blck()];
    }
    static bsqparse(jv: any): TIRUnscopedBlockStatement {
        return new TIRUnscopedBlockStatement(jv[1].ops.map((op: any) => TIRStatement.bsqparse(op)));
    }
}

class TIRScopedBlockStatement extends TIRBlockStatement {
    constructor(ops: TIRStatement[], isterminal: boolean,) {
        super(ops, isterminal);
    }

    bsqemit(): any {
        return ["TreeIR::ScopedBlockStatement", this.bsqemit_blck()];
    }
    static bsqparse(jv: any): TIRScopedBlockStatement {
        return new TIRScopedBlockStatement(jv[1].ops.map((op: any) => TIRStatement.bsqparse(op)), jv[1].isterminal);
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
