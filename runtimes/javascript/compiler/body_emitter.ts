import * as assert from "assert";

import { extractLiteralStringValue, SourceInfo } from "../../../frontend/build_decls";
import { TIRAssembly, TIRFieldKey, TIRInvokeKey, TIRObjectEntityType, TIROOType, TIRRecordType, TIRType, TIRTypeKey } from "../../../frontend/tree_ir/tir_assembly";
import { TIRAccessConstMemberFieldExpression, TIRAccessEnvValueExpression, TIRAccessNamespaceConstantExpression, TIRAccessVariableExpression, TIRConstructorPrimaryCheckExpression, TIRConstructorPrimaryDirectExpression, TIRConstructorRecordExpression, TIRConstructorTupleExpression, TIRExpression, TIRExpressionTag, TIRLiteralASCIIStringExpression, TIRLiteralASCIITemplateStringExpression, TIRLiteralASCIITypedStringExpression, TIRLiteralBoolExpression, TIRLiteralFloatPointExpression, TIRLiteralIntegralExpression, TIRLiteralNoneExpression, TIRLiteralNothingExpression, TIRLiteralRationalExpression, TIRLiteralRegexExpression, TIRLiteralStringExpression, TIRLiteralTemplateStringExpression, TIRLiteralTypedPrimitiveConstructorExpression, TIRLiteralTypedPrimitiveDirectExpression, TIRLiteralTypedStringExpression, TIRLoadFieldExpression, TIRLoadFieldVirtualExpression, TIRLoadIndexExpression, TIRLoadPropertyExpression, TIRResultErrConstructorExpression, TIRResultOkConstructorExpression, TIRSomethingConstructorExpression, TIRTypedeclConstructorExpression, TIRTypedeclDirectExpression } from "../../../frontend/tree_ir/tir_body";

class BodyEmitter {
    private readonly m_assembly: TIRAssembly;

    private m_file: string;
    private m_ns: string = "[NOT SET]";
    private m_typeResolveMemo: Map<TIRTypeKey, string> = new Map<TIRTypeKey, string>();

    constructor(assembly: TIRAssembly, file: string) {
        this.m_assembly = assembly;
        this.m_file = file;
    }

    private resolveTypeMemberAccess(tt: TIRTypeKey): string {
        assert(this.m_assembly.typeMap.has(tt), `missing type name entry ${tt}`);

        if(this.m_typeResolveMemo.has(tt)) {
            return this.m_typeResolveMemo.get(tt) as string;
        }

        const ttype = this.m_assembly.typeMap.get(tt) as TIROOType;
        const samens = ttype.tname.ns === this.m_ns;
        const corens = ttype.tname.ns === "Core";

        let taccess: string = "[INVALID]";
        if(ttype instanceof TIRObjectEntityType) {
            if(ttype.binds.size !== 0) {
                taccess = (samens || corens) ? ttype.tname : ;
            }
            else {
                taccess = (samens || corens) ? : ;
            }
        }
        else if(ttype instanceof TIREnumEntityType) {

        }

        else if(ttype instanceof TIRTypedeclEntityType) {
            
        }
        else if(ttype instanceof TIRInternalEntityType) {
            
        }
        else if(ttype instanceof TIRValidatorEntityType) {
            
        }

        else if(ttype instanceof TIRStringOfEntityType) {
            
        }
        else if(ttype instanceof TIRASCIIStringOfEntityType) {
            
        }
        else if(ttype instanceof TIRPathValidatorEntityType) {
            
        }
        else if(ttype instanceof TIRPathEntityType) {
            
        }
        else if(ttype instanceof TIRPathFragmentEntityType) {
            
        }
        else if(ttype instanceof TIRPathGlobEntityType) {
            
        }
        else if(ttype instanceof TIROkEntityType) {
            
        }
        else if(ttype instanceof TIRErrEntityType) {
            
        }
        else if(ttype instanceof TIRSomethingEntityType) {
            
        }
        else if(ttype instanceof TIRMapEntryEntityType) {
            
        }

        else if(ttype instanceof TIRListEntityType) {
            
        }
        else if(ttype instanceof TIRStackEntityType) {
            
        }
        else if(ttype instanceof TIRQueueEntityType) {
            
        }
        else if(ttype instanceof TIRSetEntityType) {
            
        }
        else if(ttype instanceof TIRMapEntityType) {
            
        }

        else if(ttype instanceof TIRTaskEntityType) {
            
        }

        else if(ttype instanceof TIRConceptEntityType) {
            
        }

        else {
            assert(false, "Unknown type in resolveTypeNameAccess");
        }

        this.m_typeResolveMemo.set(tt, taccess);
        return taccess;
    }

    private getNameOfNamespaceFunction(fkey: TIRInvokeKey): string {
        assert(this.m_namespaceFunctionMap.has(fkey), `missing namespace function for ${fkey}`);

        return this.m_namespaceFunctionMap.get(fkey) as string; 
    }

    private getNameOfNamespaceConstant(ckey: TIRNamespaceConstKey): string {
        assert(this.m_namespaceConstMap.has(ckey), `missing namespace constant for ${ckey}`);

        return this.m_namespaceConstMap.get(ckey) as string; 
    }

    private getNameOfMemberFunction(fkey: TIRInvokeKey): string {
        assert(this.m_memberFunctionMap.has(fkey), `missing member function for ${fkey}`);

        return this.m_memberFunctionMap.get(fkey) as string; 
    }

    private getNameOfMemberConstant(ckey: TIRMemberConstKey): string {
        assert(this.m_memberConstMap.has(ckey), `missing member constant for ${ckey}`);

        return this.m_memberConstMap.get(ckey) as string; 
    }

    private getNameOfMemberMethod(fkey: TIRInvokeKey): string {
        assert(this.m_memberMethodMap.has(fkey), `missing member method for ${fkey}`);

        return this.m_memberMethodMap.get(fkey) as string; 
    }

    private getNameOfMemberField(fkey: TIRFieldKey): string {
        assert(this.m_memberFieldMap.has(fkey), `missing member field for ${fkey}`);

        return this.m_memberFieldMap.get(fkey) as string; 
    }

    private jsEncodeString(str: string): string {
        //
        //TODO: right now we assume there are not escaped values in the string
        //
        return `"${str}"`;
    }

    private generateError(sinfo: SourceInfo, msg: string): string {
        return `Runtime.createRuntimeError("${msg} @ ${sinfo.line} in ${this.m_file}")`;
    }

    private emitLiteralNoneExpression(exp: TIRLiteralNoneExpression): string {
        return "null";
    }

    private emitLiteralNothingExpression(exp: TIRLiteralNothingExpression): string {
        return "undefined";
    }
    private emitLiteralBoolExpression(exp: TIRLiteralBoolExpression): string {
        return exp.value ? "true" : "false";
    }

    private emitLiteralIntegralExpression(exp: TIRLiteralIntegralExpression): string {
        if(exp.etype === "Nat") {
            return exp.expstr; //n suffix makes a bigint 
        }
        else if(exp.etype === "Int") {
            return exp.expstr.slice(0, exp.expstr.length - 1) + "n"; //n suffix makes it a bigint
        }
        else if(exp.etype === "BigNat") {
            return exp.expstr.slice(0, exp.expstr.length - 1) + "n"; //n suffix makes it a bigint
        }
        else {
            assert(exp.etype === "BigInt", "Unknown type TIRLiteralIntegralExpression");
            return exp.expstr.slice(0, exp.expstr.length - 1) + "n"; //n suffix makes it a bigint
        }
    }

    private emitLiteralRationalExpression(exp: TIRLiteralRationalExpression): string {
        return `new Fraction("${exp.value.slice(0, exp.value.length - 1)}")`;
    }

    private emitLiteralFloatPointExpression(exp: TIRLiteralFloatPointExpression): string {
        if(exp.etype === "Float") {
            return exp.value.slice(0, exp.value.length - 1);
        }
        else {
            assert(exp.etype === "Decimal", "Unknown type TIRLiteralFloatPointExpression");
            return `new Decimal(${exp.value.slice(0, exp.value.length - 1)})`;
        }
    }

    private emitLiteralRegexExpression(exp: TIRLiteralRegexExpression): string {
        return exp.value.regexstr;
    }

    private emitLiteralStringExpression(exp: TIRLiteralStringExpression): string {
        return this.jsEncodeString(extractLiteralStringValue(exp.value));
    }

    private emitLiteralASCIIStringExpression(exp: TIRLiteralASCIIStringExpression): string {
        return this.jsEncodeString(extractLiteralStringValue(exp.value));
    }
    
    private emitLiteralTypedStringExpression(exp: TIRLiteralTypedStringExpression): string {
        return this.jsEncodeString(extractLiteralStringValue(exp.value));
    }

    private emitLiteralASCIITypedStringExpression(exp: TIRLiteralASCIITypedStringExpression): string {
        return this.jsEncodeString(extractLiteralStringValue(exp.value));
    }
    
    private emitLiteralTemplateStringExpression(exp: TIRLiteralTemplateStringExpression): string {
        return this.jsEncodeString(extractLiteralStringValue(exp.value));
    }

    private emitLiteralASCIITemplateStringExpression(exp: TIRLiteralASCIITemplateStringExpression): string {
        return this.jsEncodeString(extractLiteralStringValue(exp.value));
    }
    
    private emitLiteralTypedPrimitiveDirectExpression(exp: TIRLiteralTypedPrimitiveDirectExpression): string {
        return this.emitExpression(exp.value);
    }

    private emitLiteralTypedPrimitiveConstructorExpression(exp: TIRLiteralTypedPrimitiveConstructorExpression): string {
        return `${this.getNameOfType(exp.constype)}.$constructorWithChecks_basetype(${this.emitExpression(exp.value)})`;
    }

    private emitAccessEnvValueExpression(exp: TIRAccessEnvValueExpression): string {
        if(!exp.orNoneMode) {
            return `Runtime.bsq_envget(${exp.keyname}, "${exp.valtype}", ${this.generateError(exp.sinfo, "Value not of expected type")})`;
        }
        else {
            return `Runtime.bsq_envgetornone(${exp.keyname}, "${exp.valtype}", ${this.generateError(exp.sinfo, "Value not of expected type")})`;

        }
    }

    private emitAccessNamespaceConstantExpression(exp: TIRAccessNamespaceConstantExpression): string {
        return `${this.getNameOfNamespaceConstant(exp.ckey)}$get()`;
    }

    private emitAccessConstMemberFieldExpression(exp: TIRAccessConstMemberFieldExpression): string {
        return `${this.getNameOfMemberConstant(exp.ckey)}$get()`;
    }

    private emitAccessVariableExpression(exp: TIRAccessVariableExpression): string {
        return exp.name;
    }

    private emitLoadIndexExpression(exp: TIRLoadIndexExpression): string {
        return `${this.emitExpression(exp.exp)}[${exp.index}]`;
    }

    private emitLoadIndexVirtualExpression(exp: TIRLoadIndexVirtualExpression): string {
        return `${this.emitExpression(exp.exp)}[${exp.index}]`;
    }

    private emitLoadPropertyExpression(exp: TIRLoadPropertyExpression): string {
        return `${this.emitExpression(exp.exp)}.${exp.property}`;
    }

    private emitLoadPropertyVirtualExpression(exp: TIRLoadPropertyVirtualExpression): string {
        return `${this.emitExpression(exp.exp)}.${exp.property}`;
    }

    private emitLoadFieldExpression(exp: TIRLoadFieldExpression): string {
        return `${this.emitExpression(exp.exp)}.${this.getNameOfMemberField(exp.field)}`;
    }

    private emitLoadFieldVirtualExpression(exp: TIRLoadFieldVirtualExpression): string {
        return `${this.emitExpression(exp.exp)}.${this.getNameOfMemberField(exp.field)}`;
    }

    private emitConstructorPrimaryDirectExpression(exp: TIRConstructorPrimaryDirectExpression): string {
        const tname = this.getNameOfType(exp.oftype);
        const args = exp.args.map((arg) => this.emitExpression(arg));

        return `new ${tname}(${args.join(", ")})`;
    }

    private emitConstructorPrimaryCheckExpression(exp: TIRConstructorPrimaryCheckExpression): string {
        const tname = this.getNameOfType(exp.oftype);
        const args = exp.args.map((arg) => this.emitExpression(arg));
        
        return `${tname}.$constructorWithChecks(${args.join(", ")})`;
    }

    private emitConstructorTupleExpression(exp: TIRConstructorTupleExpression): string {
        return `[${exp.args.map((arg) => this.emitExpression(arg)).join(", ")}]`;
    }

    private emitConstructorRecordExpression(exp: TIRConstructorRecordExpression): string {
        const tt = this.m_assembly.getTypeAs<TIRRecordType>(exp.oftype);
        const entries = exp.args.map((arg, ii) => `${tt.entries[ii].pname}: ${this.emitExpression(arg)})`);
        return `{${entries.join(", ")}}`;
    }

    private emitConstructorEphemeralValueList(exp: TIRConstructorEphemeralValueList): string {
        return `[${exp.args.map((arg) => this.emitExpression(arg)).join(", ")}]`;
    }

    private emitCodePackInvokeExpression(exp: TIRCodePackInvokeExpression): string {
        xxxx;
    }

    private emitResultOkConstructorExpression(exp: TIRResultOkConstructorExpression): string {
        return this.emitExpression(exp.arg);
    }

    private emitResultErrConstructorExpression(exp: TIRResultErrConstructorExpression): string {
        return this.emitExpression(exp.arg);
    }

    private emitSomethingConstructorExpression(exp: TIRSomethingConstructorExpression): string {
        return this.emitExpression(exp.arg);
    }

    private emitTypedeclDirectExpression(exp: TIRTypedeclDirectExpression): string {
        return this.emitExpression(exp.arg);
    }

    private emitTypedeclConstructorExpression(exp: TIRSomethingConstructorExpression): string {
        return `${this.getNameOfType(exp.oftype)}.$constructorWithChecks_reprtype(${this.emitExpression(exp.arg)})`;
    }

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
    CoerceRefCallResultExpression = "CoerceRefCallExpression",
    CoerceTaskRefCallResultExpression = "CoerceTaskRefCallExpression",
    CoerceActionCallResultExpression = "CoerceActionCallResultExpression",

    InjectExpression = "InjectExpression",
    ExtractExpression = "ExtractExpression",
    CreateCodePackExpression = "CreateCodePackExpression",

    IsTypeCheckAlwaysExpression = "IsTypeCheckAlwaysExpression",
    IsNotTypeCheckAlwaysExpression = "IsNotTypeCheckAlwaysExpression",
    IsNoneExpression = "IsNoneExpression",
    IsNotNoneExpression = "IsNotNoneExpression",
    IsNothingExpression = "IsNothingExpression",
    IsNotNothingExpression = "IsNotNothingExpression",
    IsTypeExpression = "IsTypeExpression",
    IsNotTypeExpression = "IsNotTypeExpression",
    IsSubTypeExpression = "IsSubTypeExpression",
    IsNotSubTypeExpression = "IsNotSubTypeExpression",

    AsNoneExpression = "AsNoneExpression",
    AsNotNoneExpression = "AsNotNoneExpression",
    AsNothingExpression = "AsNothingExpression",
    AsTypeExpression = "AsTypeExpression",
    AsSubTypeExpression = "AsSubTypeExpression",

    CallMemberFunctionExpression = "CallMemberFunctionExpression",
    CallMemberFunctionDynamicExpression = "CallMemberFunctionDynamicExpression",
    CallMemberFunctionSelfRefExpression = "CallMemberFunctionSelfRefExpression",

    CallMemberFunctionTaskExpression = "CallMemberFunctionTaskExpression",
    CallMemberFunctionTaskSelfRefExpression = "CallMemberFunctionTaskSelfRefExpression",
    CallMemberActionExpression = "CallMemberActionExpression"

    public emitExpression(exp: TIRExpression, toplevel?: boolean): string {
        switch (exp.tag) {
            case TIRExpressionTag.LiteralNoneExpression: {
                return this.emitLiteralNoneExpression(exp as TIRLiteralNoneExpression);
            }
            case TIRExpressionTag.LiteralNothingExpression: {
                return this.emitLiteralNothingExpression(exp as TIRLiteralNothingExpression);
            }
            case TIRExpressionTag.LiteralBoolExpression: {
                return this.emitLiteralBoolExpression(exp as TIRLiteralBoolExpression);
            }
            case TIRExpressionTag.LiteralIntegralExpression: {
                return this.emitLiteralIntegralExpression(exp as TIRLiteralIntegralExpression);
            }
            case TIRExpressionTag.LiteralRationalExpression: {
                return this.emitLiteralRationalExpression(exp as TIRLiteralRationalExpression);
            }
            case TIRExpressionTag.LiteralFloatPointExpression: {
                return this.emitLiteralFloatPointExpression(exp as TIRLiteralFloatPointExpression);
            }
            case TIRExpressionTag.LiteralRegexExpression: {
                return this.emitLiteralRegexExpression(exp as TIRLiteralRegexExpression);
            }
            case TIRExpressionTag.LiteralStringExpression: {
                return this.emitLiteralStringExpression(exp as TIRLiteralStringExpression);
            }
            case TIRExpressionTag.LiteralASCIIStringExpression: {
                return this.emitLiteralASCIIStringExpression(exp as TIRLiteralASCIIStringExpression);
            }
            case TIRExpressionTag.LiteralTypedStringExpression: {
                return this.emitLiteralTypedStringExpression(exp as TIRLiteralTypedStringExpression);
            }
            case TIRExpressionTag.LiteralASCIITypedStringExpression: {
                return this.emitLiteralASCIITypedStringExpression(exp as TIRLiteralASCIITypedStringExpression);
            }
            case TIRExpressionTag.LiteralTemplateStringExpression: {
                return this.emitLiteralTemplateStringExpression(exp as TIRLiteralTemplateStringExpression);
            }
            case TIRExpressionTag.LiteralASCIITemplateStringExpression: {
                return this.emitLiteralASCIITemplateStringExpression(exp as TIRLiteralASCIITemplateStringExpression);
            }
            case TIRExpressionTag.LiteralTypedPrimitiveDirectExpression: {
                return this.emitLiteralTypedPrimitiveDirectExpression(exp as TIRLiteralTypedPrimitiveDirectExpression);
            }
            case TIRExpressionTag.LiteralTypedPrimitiveConstructorExpression: {
                return this.emitLiteralTypedPrimitiveConstructorExpression(exp as TIRLiteralTypedPrimitiveConstructorExpression);
            }
            case TIRExpressionTag.AccessEnvValueExpression: {
                return this.emitAccessEnvValueExpression(exp as TIRAccessEnvValueExpression);
            }
            case TIRExpressionTag.AccessNamespaceConstantExpression: {
                return this.emitAccessNamespaceConstantExpression(exp as TIRAccessNamespaceConstantExpression);
            }
            case TIRExpressionTag.TIRAccessConstMemberFieldExpression: {
                return this.emitAccessConstMemberFieldExpression(exp as TIRAccessConstMemberFieldExpression);
            }
            case TIRExpressionTag.AccessVariableExpression: {
                return this.emitAccessVariableExpression(exp as TIRAccessVariableExpression);
            }
            case TIRExpressionTag.LoadIndexExpression: {
                return this.emitLoadIndexExpression(exp as TIRLoadIndexExpression);
            }
            case TIRExpressionTag.LoadPropertyExpression: {
                return this.emitLoadPropertyExpression(exp as TIRLoadPropertyExpression);
            }
            case TIRExpressionTag.LoadFieldExpression: {
                return this.emitLoadFieldExpression(exp as TIRLoadFieldExpression);
            }
            case TIRExpressionTag.LoadFieldVirtualExpression: {
                return this.emitLoadFieldVirtualExpression(exp as TIRLoadFieldVirtualExpression);
            }
            case TIRExpressionTag.ConstructorPrimaryDirectExpression: {
                return this.emitConstructorPrimaryDirectExpression(exp as TIRConstructorPrimaryDirectExpression);
            }
            case TIRExpressionTag.ConstructorPrimaryCheckExpression: {
                return this.emitConstructorPrimaryCheckExpression(exp as TIRConstructorPrimaryCheckExpression);
            }
            case TIRExpressionTag.ConstructorTupleExpression: {
                return this.emitConstructorTupleExpression(exp as TIRConstructorTupleExpression);
            }
            case TIRExpressionTag.ConstructorRecordExpression: {
                return this.emitConstructorRecordExpression(exp as TIRConstructorRecordExpression);
            }
            case TIRExpressionTag.CodePackInvokeExpression: {
                return this.emitCodePackInvokeExpression(exp as TIRCodePackInvokeExpression);
            }
            case TIRExpressionTag.ResultOkConstructorExpression: {
                return this.emitResultOkConstructorExpression(exp as TIRResultOkConstructorExpression);
            }
            case TIRExpressionTag.ResultErrConstructorExpression: {
                return this.emitResultErrConstructorExpression(exp as TIRResultErrConstructorExpression);
            }
            case TIRExpressionTag.SomethingConstructorExpression: {
                return this.emitSomethingConstructorExpression(exp as TIRSomethingConstructorExpression);
            }
            case TIRExpressionTag.TypedeclDirectExpression: {
                return this.emitTypedeclDirectExpression(exp as TIRTypedeclDirectExpression);
            }
            case TIRExpressionTag.TypedeclConstructorExpression: {
                return this.emitTypedeclConstructorExpression(exp as TIRTypedeclConstructorExpression);
            }

            xxxx;

            default: {
                assert(false, `Unknown expression kind ${exp.tag}`);
                return `[UNKNOWN TAG ${exp.tag}]`
            }
        }
    }
}

export {
    BodyEmitter
};
