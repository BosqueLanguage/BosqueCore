import * as assert from "assert";

import { extractLiteralStringValue, SourceInfo } from "../../../frontend/build_decls";
import { TIRASCIIStringOfEntityType, TIRAssembly, TIRConceptType, TIREntityType, TIREnumEntityType, TIRInternalEntityType, TIRListEntityType, TIRMapEntityType, TIRMemberFieldDecl, TIRNamespaceFunctionDecl, TIRObjectEntityType, TIROOType, TIRPathEntityType, TIRPathFragmentEntityType, TIRPathGlobEntityType, TIRPathValidatorEntityType, TIRQueueEntityType, TIRRecordType, TIRSetEntityType, TIRStackEntityType, TIRStringOfEntityType, TIRTaskType, TIRType, TIRTypedeclEntityType, TIRTypeKey, TIRUnionType, TIRValidatorEntityType } from "../../../frontend/tree_ir/tir_assembly";
import { TIRAccessConstMemberFieldExpression, TIRAccessEnvValueExpression, TIRAccessNamespaceConstantExpression, TIRAccessVariableExpression, TIRCallNamespaceFunctionExpression, TIRCallNamespaceOperatorExpression, TIRCallStaticFunctionExpression, TIRConstructorPrimaryCheckExpression, TIRConstructorPrimaryDirectExpression, TIRConstructorRecordExpression, TIRConstructorTupleExpression, TIRExpression, TIRExpressionTag, TIRLiteralASCIIStringExpression, TIRLiteralASCIITemplateStringExpression, TIRLiteralASCIITypedStringExpression, TIRLiteralBoolExpression, TIRLiteralFloatPointExpression, TIRLiteralIntegralExpression, TIRLiteralNoneExpression, TIRLiteralNothingExpression, TIRLiteralRationalExpression, TIRLiteralRegexExpression, TIRLiteralStringExpression, TIRLiteralTemplateStringExpression, TIRLiteralTypedPrimitiveConstructorExpression, TIRLiteralTypedPrimitiveDirectExpression, TIRLiteralTypedStringExpression, TIRLoadFieldExpression, TIRLoadFieldVirtualExpression, TIRLoadIndexExpression, TIRLoadPropertyExpression, TIRLogicActionAndExpression, TIRLogicActionOrExpression, TIRPrefixNegateExpression, TIRPrefixNotExpression, TIRResultErrConstructorExpression, TIRResultOkConstructorExpression, TIRSomethingConstructorExpression, TIRTypedeclConstructorExpression, TIRTypedeclDirectExpression } from "../../../frontend/tree_ir/tir_body";

function NOT_IMPLEMENTED_EXPRESSION(tag: string): string {
    assert(false, `NOT IMEPLEMENTED -- ${tag}`);
}

class BodyEmitter {
    private readonly m_assembly: TIRAssembly;

    private m_file: string;
    private m_ns: string = "[NOT SET]";
    private m_typeResolveMemo: Map<TIRTypeKey, string> = new Map<TIRTypeKey, string>();
    private m_coreImports: Set<TIRTypeKey> = new Set<TIRTypeKey>();

    private m_activeTask: TIRTypeKey = "[NOT SET]";

    constructor(assembly: TIRAssembly, file: string) {
        this.m_assembly = assembly;
        this.m_file = file;
    }

    private typeEncodedAsUnion(tt: TIRTypeKey): boolean {
        assert(this.m_assembly.typeMap.has(tt), `missing type name entry ${tt}`);

        const ttype = this.m_assembly.typeMap.get(tt) as TIRType;
        return (ttype instanceof TIRConceptType) || (ttype instanceof TIRUnionType);
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
                taccess = (samens || corens) ? `BSQ${ttype.tname.name}` : `${ttype.tname.ns}.${ttype.tname.name}`;
                if(corens) {
                    this.m_coreImports.add(`BSQ${ttype.tname.name}`);
                }
            }
            else {
                if(corens) {
                    taccess = `$CoreTypes["${ttype.tkey}"]`;
                }
                else {
                    if(samens) {
                        taccess = `$Types["${ttype.tkey}"]`;
                    }
                    else {
                        taccess = `${ttype.tname.ns}.$Types["${ttype.tkey}"]`; 
                    }
                }
            }
        }
        else if(ttype instanceof TIREnumEntityType) {
            taccess = (samens || corens) ? `BSQ${ttype.tname.name}` : `${ttype.tname.ns}.${ttype.tname.name}`;
            if (corens) {
                this.m_coreImports.add(`BSQ${ttype.tname.name}`);
            }
        }
        else if(ttype instanceof TIRTypedeclEntityType) {
            taccess = (samens || corens) ? `BSQ${ttype.tname.name}` : `${ttype.tname.ns}.${ttype.tname.name}`;
            if (corens) {
                this.m_coreImports.add(`BSQ${ttype.tname.name}`);
            }
        }
        else if(ttype instanceof TIRInternalEntityType) {
            taccess = `BSQ${ttype.tname.name}`;
            this.m_coreImports.add(`BSQ${ttype.tname.name}`);
        }
        else if(ttype instanceof TIRValidatorEntityType) {
            if(corens) {
                taccess = `$CoreTypes["${ttype.tkey}"]`;
            }
            else {
                if(samens) {
                    taccess = `$Types["${ttype.tkey}"]`;
                }
                else {
                    taccess = `${ttype.tname.ns}.$Types["${ttype.tkey}"]`; 
                }
            }
        }
        else if((ttype instanceof TIRStringOfEntityType) || (ttype instanceof TIRASCIIStringOfEntityType)) {
            if(corens) {
                taccess = `$CoreTypes["${ttype.tkey}"]`;
            }
            else {
                if(samens) {
                    taccess = `$Types["${ttype.tkey}"]`;
                }
                else {
                    taccess = `${ttype.tname.ns}.$Types["${ttype.tkey}"]`; 
                }
            }
        }
        else if(ttype instanceof TIRPathValidatorEntityType) {
            if(corens) {
                taccess = `$CoreTypes["${ttype.tkey}"]`;
            }
            else {
                if(samens) {
                    taccess = `$Types["${ttype.tkey}"]`;
                }
                else {
                    taccess = `${ttype.tname.ns}.$Types["${ttype.tkey}"]`; 
                }
            }
        }
        else if((ttype instanceof TIRPathEntityType) || (ttype instanceof TIRPathFragmentEntityType) || (ttype instanceof TIRPathGlobEntityType)) {
            if(corens) {
                taccess = `$CoreTypes["${ttype.tkey}"]`;
            }
            else {
                if(samens) {
                    taccess = `$Types["${ttype.tkey}"]`;
                }
                else {
                    taccess = `${ttype.tname.ns}.$Types["${ttype.tkey}"]`; 
                }
            }
        }
        else if((ttype instanceof TIRListEntityType) || (ttype instanceof TIRStackEntityType) || (ttype instanceof TIRQueueEntityType) ||  (ttype instanceof TIRSetEntityType) || (ttype instanceof TIRMapEntityType)) {
            taccess = `$CoreTypes["${ttype.tkey}"]`;
        }
        else if(ttype instanceof TIRTaskType) {
            taccess = (samens || corens) ? `BSQ${ttype.tname.name}` : `${ttype.tname.ns}.${ttype.tname.name}`;
            if (corens) {
                this.m_coreImports.add(`BSQ${ttype.tname.name}`);
            }
        }
        else if(ttype instanceof TIRConceptType) {
            if(ttype.binds.size !== 0) {
                taccess = (samens || corens) ? `BSQ${ttype.tname.name}` : `${ttype.tname.ns}.${ttype.tname.name}`;
                if(corens) {
                    this.m_coreImports.add(`BSQ${ttype.tname.name}`);
                }
            }
            else {
                if(corens) {
                    taccess = `$CoreTypes["${ttype.tkey}"]`;
                }
                else {
                    if(samens) {
                        taccess = `$Types["${ttype.tkey}"]`;
                    }
                    else {
                        taccess = `${ttype.tname.ns}.$Types["${ttype.tkey}"]`; 
                    }
                }
            }   
        }
        else {
            assert(false, "Unknown type in resolveTypeNameAccess");
        }

        this.m_typeResolveMemo.set(tt, taccess);
        return taccess;
    }

    private jsEncodeString(str: string): string {
        //
        //TODO: right now we assume there are not escaped values in the string
        //
        return `"${str}"`;
    }

    private generateError(sinfo: SourceInfo, msg: string): string {
        return `$Runtime.createRuntimeError("${msg} @ ${sinfo.line} in ${this.m_file}")`;
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
        return `${this.resolveTypeMemberAccess(exp.constype)}.$constructorWithChecks_basetype(${this.emitExpression(exp.value)})`;
    }

    private emitAccessEnvValueExpression(exp: TIRAccessEnvValueExpression): string {
        if(!exp.orNoneMode) {
            return `$Runtime.BSQEnvironment.get(${this.resolveTypeMemberAccess(this.m_activeTask)}.$environment, "${exp.keyname}", "${exp.valtype}")`;
        }
        else {
            return `$Runtime.BSQEnvironment.getOrNone(${this.resolveTypeMemberAccess(this.m_activeTask)}.$environment, "${exp.keyname}", "${exp.valtype}")`;
        }
    }

    private emitAccessNamespaceConstantExpression(exp: TIRAccessNamespaceConstantExpression): string {
        return `${exp.ns}.${exp.cname}`;
    }

    private emitAccessConstMemberFieldExpression(exp: TIRAccessConstMemberFieldExpression): string {
        return `${this.resolveTypeMemberAccess(exp.tkey)}.${exp.cname}`;
    }

    private emitAccessVariableExpression(exp: TIRAccessVariableExpression): string {
        return exp.name;
    }

    private emitLoadIndexExpression(exp: TIRLoadIndexExpression): string {
        return `${this.emitExpression(exp.exp)}[${exp.index}]`;
    }

    private emitLoadPropertyExpression(exp: TIRLoadPropertyExpression): string {
        return `${this.emitExpression(exp.exp)}.${exp.property}`;
    }

    private emitLoadFieldExpression(exp: TIRLoadFieldExpression): string {
        const fname = (this.m_assembly.fieldMap.get(exp.field) as TIRMemberFieldDecl).name;
        return `${this.emitExpression(exp.exp)}.${fname}`;
    }

    private emitLoadFieldVirtualExpression(exp: TIRLoadFieldVirtualExpression): string {
        const fname = (this.m_assembly.fieldMap.get(exp.field) as TIRMemberFieldDecl).name;
        return `${this.emitExpression(exp.exp)}.${fname}`;
    }

    private emitConstructorPrimaryDirectExpression(exp: TIRConstructorPrimaryDirectExpression): string {
        const tname = this.resolveTypeMemberAccess(exp.oftype);
        const args = exp.args.map((arg) => this.emitExpression(arg));

        return `new ${tname}(${args.join(", ")})`;
    }

    private emitConstructorPrimaryCheckExpression(exp: TIRConstructorPrimaryCheckExpression): string {
        const tname = this.resolveTypeMemberAccess(exp.oftype);
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
        return `${this.resolveTypeMemberAccess(exp.oftype)}.$constructorWithChecks(${this.emitExpression(exp.arg)})`;
    }

    private emitCallNamespaceFunctionExpression(exp: TIRCallNamespaceFunctionExpression): string {
        const invk = this.m_assembly.getNamespace(exp.ns).functions.get(exp.fname) as TIRNamespaceFunctionDecl;
        const nspfx = this.m_ns !== invk.ns && invk.ns !== "Core" ? `${invk.ns}.` : "";

        if(invk.terms.length === 0) {
            if(invk.ns === "Core") {
                this.m_coreImports.add(invk.name);
            }

            return `${nspfx}${invk.name}(${exp.args.map((arg) => this.emitExpression(arg)).join(", ")})`;
        }
        else {
            if(invk.ns === "Core") {
                return `$CoreFunctions["${invk.name}"](${exp.args.map((arg) => this.emitExpression(arg)).join(", ")})`;
            }
            else {
                return `${nspfx}$Functions["${invk.ikey}"](${exp.args.map((arg) => this.emitExpression(arg)).join(", ")})`;
            }
        }
    }

    private emitCallNamespaceOperatorExpression(exp: TIRCallNamespaceOperatorExpression): string {
       return NOT_IMPLEMENTED_EXPRESSION(exp.tag);
    }
    
    private emitCallStaticFunctionExpression(exp: TIRCallStaticFunctionExpression): string {
        const ttype = this.m_assembly.typeMap.get(exp.tkey) as TIROOType;
        const invk = ttype.staticFunctions.find((sf) => sf.ikey === exp.fkey);
        assert(invk !== undefined, "emitCallStaticFunctionExpression");

        const accessterm = this.resolveTypeMemberAccess(ttype.tkey);
        if(invk.terms.length === 0) {
            return `${accessterm}.${invk.name}(${exp.args.map((arg) => this.emitExpression(arg)).join(", ")})`;
        }
        else {
            return `${accessterm}.$Functions["${invk.ikey}"](${exp.args.map((arg) => this.emitExpression(arg)).join(", ")})`;
        }
    }

    private emitLogicActionAndExpression(exp: TIRLogicActionAndExpression, toplevel: boolean): string {
       const lexp = "(" + exp.args.map((arg) => this.emitExpression(arg, false)).join(" && ") + ")";
       return toplevel ? lexp : ("(" + lexp + ")");
    }

    private emitLogicActionOrExpression(exp: TIRLogicActionOrExpression, toplevel: boolean): string {
        const lexp = "(" + exp.args.map((arg) => this.emitExpression(arg, false)).join(" || ") + ")";
        return toplevel ? lexp : ("(" + lexp + ")");
    }

    private emitPrefixNotOpExpression(exp: TIRPrefixNotExpression): string {
       xxxx;
    }

    private emitPrefixNegateOpExpression(exp: TIRPrefixNegateExpression): string {
       xxxx;
    }

    private emitBinAddExpression(exp: TIRBinAddExpression): string {
       xxxx;
    }
    private emitBinSubExpression(exp: TIRBinSubExpression): string {
       xxxx;
    }
    private emitBinMultExpression(exp: TIRBinMultExpression): string {
       xxxx;
    }
    private emitBinDivExpression(exp: TIRBinDivExpression): string {
       xxxx;
    }

    private emitBinKeyEqBothUniqueExpression(exp: TIRBinKeyEqBothUniqueExpression): string {
       xxxx;
    }
    private emitBinKeyEqOneUniqueExpression(exp: TIRBinKeyEqOneUniqueExpression): string {
       xxxx;
    }
    private emitBinKeyEqGeneralExpression(exp: TIRBinKeyEqGeneralExpression): string {
       xxxx;
    }

    private emitBinKeyNeqBothUniqueExpression(exp: TIRBinKeyNeqBothUniqueExpression): string {
       xxxx;
    }
    private emitBinKeyNeqOneUniqueExpression(exp: TIRBinKeyNeqOneUniqueExpression): string {
       xxxx;
    }
    private emitBinKeyNeqGeneralExpression(exp: TIRBinKeyNeqGeneralExpression): string {
       xxxx;
    }

    private emitBinKeyUniqueLessExpression(exp: TIRBinKeyUniqueLessExpression): string {
       xxxx;
    }
    private emitBinKeyGeneralLessExpression(exp: TIRBinKeyGeneralLessExpression): string {
       xxxx;
    }

    private emitNumericEqExpression(exp: TIRNumericEqExpression): string {
       xxxx;
    }
    private emitNumericNeqExpression(exp: TIRNumericNeqExpression): string {
       xxxx;
    }
    private emitNumericLessExpression(exp: TIRNumericLessExpression): string {
       xxxx;
    }
    private emitNumericLessEqExpression(exp: TIRNumericLessEqExpression): string {
       xxxx;
    }
    private emitNumericGreaterExpression(exp: TIRNumericGreaterExpression): string {
       xxxx;
    }
    private emitNumericGreaterEqExpression(exp: TIRNumericGreaterEqExpression): string {
       xxxx;
    }

    private emitBinLogicAndExpression(exp: TIRBinLogicAndExpression): string {
       xxxx;
    }
    private emitBinLogicOrExpression(exp: TIRBinLogicOrExpression): string {
       xxxx;
    }
    private emitBinLogicImpliesExpression(exp: TIRBinLogicImpliesExpression): string {
       xxxx;
    }

    private emitMapEntryConstructorExpression(exp: TIRMapEntryConstructorExpression): string {
       xxxx;
    }

    private emitIfExpression(exp: TIRIfExpression): string {
       xxxx;
    }
    private emitSwitchExpression(exp: TIRSwitchExpression): string {
       xxxx;
    }
    private emitMatchExpression(exp: TIRMatchExpression): string {
       xxxx;
    }

    private emitTaskSelfFieldExpression(exp: TIRTaskSelfFieldExpression): string {
       xxxx;
    }
    private emitTaskSelfControlExpression(exp: TIRTaskSelfControlExpression): string {
       xxxx;
    }
    private emitTaskGetIDExpression(exp: TIRTaskGetIDExpression): string {
       xxxx;
    }

    private emitCoerceSafeExpression(exp: TIRCoerceSafeExpression): string {
       xxxx;
    }
    private emitCoerceRefCallResultExpression(exp: TIRCoerceRefCallExpression): string {
       xxxx;
    }
    private emitCoerceTaskRefCallResultExpression(exp: TIRCoerceTaskRefCallExpression): string {
       xxxx;
    }
    private emitCoerceActionCallResultExpression(exp: TIRCoerceActionCallResultExpression): string {
       xxxx;
    }

    private emitInjectExpression(exp: TIRInjectExpression): string {
       xxxx;
    }
    private emitExtractExpression(exp: TIRExtractExpression): string {
       xxxx;
    }
    private emitCreateCodePackExpression(exp: TIRCreateCodePackExpression): string {
       xxxx;
    }

    private emitIsTypeCheckAlwaysExpression(exp: TIRIsTypeCheckAlwaysExpression): string {
       xxxx;
    }
    private emitIsNotTypeCheckAlwaysExpression(exp: TIRIsNotTypeCheckAlwaysExpression): string {
       xxxx;
    }
    private emitIsNoneExpression(exp: TIRIsNoneExpression): string {
       xxxx;
    }
    private emitIsNotNoneExpression(exp: TIRIsNotNoneExpression): string {
       xxxx;
    }
    private emitIsNothingExpression(exp: TIRIsNothingExpression): string {
       xxxx;
    }
    private emitIsNotNothingExpression(exp: TIRIsNotNothingExpression): string {
       xxxx;
    }
    private emitIsTypeExpression(exp: TIRIsTypeExpression): string {
       xxxx;
    }
    private emitIsNotTypeExpression(exp: TIRIsNotTypeExpression): string {
       xxxx;
    }
    private emitIsSubTypeExpression(exp: TIRIsSubTypeExpression): string {
       xxxx;
    }
    private emitIsNotSubTypeExpression(exp: TIRIsNotSubTypeExpression): string {
       xxxx;
    }

    private emitAsNoneExpression(exp: TIRAsNoneExpression): string {
       xxxx;
    }
    private emitAsNotNoneExpression(exp: TIRAsNotNoneExpression): string {
       xxxx;
    }
    private emitAsNothingExpression(exp: TIRAsNothingExpression): string {
       xxxx;
    }
    private emitAsTypeExpression(exp: TIRAsTypeExpression): string {
       xxxx;
    }
    private emitAsSubTypeExpression(exp: TIRAsSubTypeExpression): string {
       xxxx;
    }

    private emitCallMemberFunctionExpression(exp: TIRCallMemberFunctionExpression): string {
       xxxx;
    }
    private emitCallMemberFunctionDynamicExpression(exp: TIRCallMemberFunctionDynamicExpression): string {
       xxxx;
    }
    private emitCallMemberFunctionSelfRefExpression(exp: TIRCallMemberFunctionSelfRefExpression): string {
       xxxx;
    }

    private emitCallMemberFunctionTaskExpression(exp: TIRCallMemberFunctionTaskExpression): string {
       xxxx;
    }
    private emitCallMemberFunctionTaskSelfRefExpression(exp: TIRCallMemberFunctionTaskSelfRefExpression): string {
       xxxx;
    }
    private emitCallMemberActionExpression(exp: TIRCallMemberActionExpression): string {
        xxxx;
    }

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
