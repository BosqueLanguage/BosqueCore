import * as assert from "assert";

import { extractLiteralStringValue } from "../../../frontend/build_decls";
import { TIRASCIIStringOfEntityType, TIRAssembly, TIRConceptType, TIREnumEntityType, TIRListEntityType, TIRMapEntityType, TIRMemberFieldDecl, TIRNamespaceFunctionDecl, TIRObjectEntityType, TIROOType, TIRPathEntityType, TIRPathFragmentEntityType, TIRPathGlobEntityType, TIRPathValidatorEntityType, TIRPostConditionDecl, TIRPreConditionDecl, TIRPrimitiveInternalEntityType, TIRQueueEntityType, TIRRecordType, TIRSetEntityType, TIRStackEntityType, TIRStringOfEntityType, TIRTaskType, TIRType, TIRTypedeclEntityType, TIRTypeKey, TIRUnionType, TIRValidatorEntityType } from "../../../frontend/tree_ir/tir_assembly";
import { TIRAbortStatement, TIRAccessConstMemberFieldExpression, TIRAccessEnvValueExpression, TIRAccessNamespaceConstantExpression, TIRAccessVariableExpression, TIRAsNoneExpression, TIRAsNothingExpression, TIRAsNotNoneExpression, TIRAssertCheckStatement, TIRAsSubTypeExpression, TIRAsTypeExpression, TIRBinAddExpression, TIRBinDivExpression, TIRBinKeyEqBothUniqueExpression, TIRBinKeyEqGeneralExpression, TIRBinKeyEqOneUniqueExpression, TIRBinKeyGeneralLessExpression, TIRBinKeyNeqBothUniqueExpression, TIRBinKeyNeqGeneralExpression, TIRBinKeyNeqOneUniqueExpression, TIRBinKeyUniqueLessExpression, TIRBinLogicAndExpression, TIRBinLogicImpliesExpression, TIRBinLogicOrExpression, TIRBinMultExpression, TIRBinSubExpression, TIRCallMemberActionExpression, TIRCallMemberFunctionDynamicExpression, TIRCallMemberFunctionExpression, TIRCallMemberFunctionSelfRefExpression, TIRCallMemberFunctionTaskExpression, TIRCallMemberFunctionTaskSelfRefExpression, TIRCallNamespaceFunctionExpression, TIRCallNamespaceOperatorExpression, TIRCallStatementWAction, TIRCallStatementWRef, TIRCallStatementWTaskRef, TIRCallStaticFunctionExpression, TIRCoerceSafeActionCallResultExpression, TIRCoerceSafeExpression, TIRCoerceSafeRefCallResultExpression, TIRCoerceSafeTaskRefCallResultExpression, TIRConstructorPrimaryCheckExpression, TIRConstructorPrimaryDirectExpression, TIRConstructorRecordExpression, TIRConstructorTupleExpression, TIRDebugStatement, TIREnvironmentFreshStatement, TIREnvironmentSetStatement, TIREnvironmentSetStatementBracket, TIRExpression, TIRExpressionTag, TIRExtractExpression, TIRIfExpression, TIRIfStatement, TIRInjectExpression, TIRIsNoneExpression, TIRIsNothingExpression, TIRIsNotNoneExpression, TIRIsNotNothingExpression, TIRIsNotSubTypeExpression, TIRIsNotTypeExpression, TIRIsSubTypeExpression, TIRIsTypeExpression, TIRLiteralASCIIStringExpression, TIRLiteralASCIITemplateStringExpression, TIRLiteralASCIITypedStringExpression, TIRLiteralBoolExpression, TIRLiteralFloatPointExpression, TIRLiteralIntegralExpression, TIRLiteralNoneExpression, TIRLiteralNothingExpression, TIRLiteralRationalExpression, TIRLiteralRegexExpression, TIRLiteralStringExpression, TIRLiteralTemplateStringExpression, TIRLiteralTypedPrimitiveConstructorExpression, TIRLiteralTypedPrimitiveDirectExpression, TIRLiteralTypedStringExpression, TIRLoadFieldExpression, TIRLoadFieldVirtualExpression, TIRLoadIndexExpression, TIRLoadPropertyExpression, TIRLoggerEmitConditionalStatement, TIRLoggerEmitStatement, TIRLogicActionAndExpression, TIRLogicActionOrExpression, TIRMapEntryConstructorExpression, TIRMatchExpression, TIRMatchStatement, TIRNopStatement, TIRNumericEqExpression, TIRNumericGreaterEqExpression, TIRNumericGreaterExpression, TIRNumericLessEqExpression, TIRNumericLessExpression, TIRNumericNeqExpression, TIRPrefixNegateExpression, TIRPrefixNotExpression, TIRResultErrConstructorExpression, TIRResultOkConstructorExpression, TIRReturnStatement, TIRReturnStatementWAction, TIRReturnStatementWRef, TIRReturnStatementWTaskRef, TIRScopedBlockStatement, TIRSomethingConstructorExpression, TIRStatement, TIRStatementTag, TIRSwitchExpression, TIRSwitchStatement, TIRTaskAllStatement, TIRTaskDashStatement, TIRTaskGetIDExpression, TIRTaskMultiStatement, TIRTaskRaceStatement, TIRTaskRunStatement, TIRTaskSelfControlExpression, TIRTaskSelfFieldExpression, TIRTaskSetSelfFieldStatement, TIRTypedeclConstructorExpression, TIRTypedeclDirectExpression, TIRUnscopedBlockStatement, TIRVarAssignStatement, TIRVarAssignStatementWAction, TIRVarAssignStatementWRef, TIRVarDeclareAndAssignStatement, TIRVarDeclareAndAssignStatementWAction, TIRVarDeclareAndAssignStatementWRef, TIRVarDeclareAndAssignStatementWTaskRef, TIRVarDeclareStatement } from "../../../frontend/tree_ir/tir_body";

function NOT_IMPLEMENTED_EXPRESSION(tag: string): string {
    assert(false, `NOT IMEPLEMENTED -- ${tag}`);
}

function NOT_IMPLEMENTED_STATEMENT(tag: string): string {
    assert(false, `NOT IMEPLEMENTED -- ${tag}`);
}

class BodyEmitter {
    private readonly m_assembly: TIRAssembly;

    private readonly m_file: string;
    private readonly m_ns: string = "[NOT SET]";
    private m_typeResolveMemo: Map<TIRTypeKey, string> = new Map<TIRTypeKey, string>();
    m_coreImports: Set<TIRTypeKey> = new Set<TIRTypeKey>();

    private m_activeTask: TIRTypeKey = "[NOT SET]";

    private m_varCtr = 0;

    constructor(assembly: TIRAssembly, file: string, ns: string) {
        this.m_assembly = assembly;
        this.m_file = file;
        this.m_ns = ns;
    }

    typeEncodedAsUnion(tt: TIRTypeKey): boolean {
        assert(this.m_assembly.typeMap.has(tt), `missing type name entry ${tt}`);

        const ttype = this.m_assembly.typeMap.get(tt) as TIRType;
        return (ttype instanceof TIRConceptType) || (ttype instanceof TIRUnionType);
    }

    resolveTypeMemberAccess(tt: TIRTypeKey): string {
        assert(this.m_assembly.typeMap.has(tt), `missing type name entry ${tt}`);

        if(this.m_typeResolveMemo.has(tt)) {
            return this.m_typeResolveMemo.get(tt) as string;
        }

        const ttype = this.m_assembly.typeMap.get(tt) as TIROOType;
        const samens = ttype.tname.ns === this.m_ns;
        const corens = ttype.tname.ns === "Core";

        let taccess: string = "[INVALID]";
        if(ttype instanceof TIRObjectEntityType) {
            if(ttype.binds.size === 0) {
                taccess = (samens || corens) ? `BSQ${ttype.tname.name}` : `${ttype.tname.ns}.BSQ${ttype.tname.name}`;
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
            taccess = (samens || corens) ? `BSQ${ttype.tname.name}` : `${ttype.tname.ns}.BSQ${ttype.tname.name}`;
            if (corens) {
                this.m_coreImports.add(`BSQ${ttype.tname.name}`);
            }
        }
        else if(ttype instanceof TIRTypedeclEntityType) {
            taccess = (samens || corens) ? `BSQ${ttype.tname.name}` : `${ttype.tname.ns}.BSQ${ttype.tname.name}`;
            if (corens) {
                this.m_coreImports.add(`BSQ${ttype.tname.name}`);
            }
        }
        else if(ttype instanceof TIRPrimitiveInternalEntityType) {
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
            taccess = (samens || corens) ? `BSQ${ttype.tname.name}` : `${ttype.tname.ns}.BSQ${ttype.tname.name}`;
            if (corens) {
                this.m_coreImports.add(`BSQ${ttype.tname.name}`);
            }
        }
        else if(ttype instanceof TIRConceptType) {
            if(ttype.binds.size === 0) {
                taccess = (samens || corens) ? `BSQ${ttype.tname.name}` : `${ttype.tname.ns}.BSQ${ttype.tname.name}`;
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
    
    private emitLiteralTypedPrimitiveDirectExpression(exp: TIRLiteralTypedPrimitiveDirectExpression, toplevel: boolean): string {
        return this.emitExpression(exp.value, toplevel);
    }

    private emitLiteralTypedPrimitiveConstructorExpression(exp: TIRLiteralTypedPrimitiveConstructorExpression): string {
        return `${this.resolveTypeMemberAccess(exp.constype)}.$constructorWithChecks_basetype(${this.emitExpression(exp.value, true)})`;
    }

    private emitAccessEnvValueExpression(exp: TIRAccessEnvValueExpression): string {
        if(!exp.orNoneMode) {
            return `$Runtime.BSQEnvironment.get(${this.resolveTypeMemberAccess(this.m_activeTask)}.$environment, "${exp.keyname}", "${exp.valtype}")`;
        }
        else {
            if(this.typeEncodedAsUnion(exp.valtype)) {
                return `$Runtime.BSQEnvironment.getOrNoneDV(${this.resolveTypeMemberAccess(this.m_activeTask)}.$environment, "${exp.keyname}", "${exp.valtype}")`;
            }
            else {
                return `$Runtime.BSQEnvironment.getOrNoneUV(${this.resolveTypeMemberAccess(this.m_activeTask)}.$environment, "${exp.keyname}", "${exp.valtype}")`;
            }
        }
    }

    private emitAccessNamespaceConstantExpression(exp: TIRAccessNamespaceConstantExpression): string {
        return `${exp.ns}.${exp.cname}`;
    }

    private emitAccessConstMemberFieldExpression(exp: TIRAccessConstMemberFieldExpression): string {
        return `${this.resolveTypeMemberAccess(exp.tkey)}.${exp.cname}`;
    }

    private emitAccessVariableExpression(exp: TIRAccessVariableExpression): string {
        if(exp.name === "this") {
            return "$_this";
        }
        else if(exp.name === "$this") {
            return "$_$this";
        }
        else {
            return exp.name;
        }
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
        const args = exp.args.map((arg) => this.emitExpression(arg, true));

        return `${tname}.$constructorDirect(${args.join(", ")})`;
    }

    private emitConstructorPrimaryCheckExpression(exp: TIRConstructorPrimaryCheckExpression): string {
        const tname = this.resolveTypeMemberAccess(exp.oftype);
        const args = exp.args.map((arg) => this.emitExpression(arg, true));
        
        return `${tname}.$constructorWithChecks(${args.join(", ")})`;
    }

    private emitConstructorTupleExpression(exp: TIRConstructorTupleExpression): string {
        return `[${exp.args.map((arg) => this.emitExpression(arg, true)).join(", ")}]`;
    }

    private emitConstructorRecordExpression(exp: TIRConstructorRecordExpression): string {
        const tt = this.m_assembly.getTypeAs<TIRRecordType>(exp.oftype);
        const entries = exp.args.map((arg, ii) => `${tt.entries[ii].pname}: ${this.emitExpression(arg, true)})`);
        return `{${entries.join(", ")}}`;
    }

    private emitCodePackInvokeExpression(exp: TIRCodePackInvokeExpression): string {
        xxxx;
    }

    private emitResultOkConstructorExpression(exp: TIRResultOkConstructorExpression, toplevel: boolean): string {
        return this.emitExpression(exp.arg, toplevel);
    }

    private emitResultErrConstructorExpression(exp: TIRResultErrConstructorExpression, toplevel: boolean): string {
        return this.emitExpression(exp.arg, toplevel);
    }

    private emitSomethingConstructorExpression(exp: TIRSomethingConstructorExpression, toplevel: boolean): string {
        return this.emitExpression(exp.arg, toplevel);
    }

    private emitTypedeclDirectExpression(exp: TIRTypedeclDirectExpression, toplevel: boolean): string {
        return this.emitExpression(exp.arg, toplevel);
    }

    private emitTypedeclConstructorExpression(exp: TIRSomethingConstructorExpression): string {
        return `${this.resolveTypeMemberAccess(exp.oftype)}.$constructorWithChecks(${this.emitExpression(exp.arg, true)})`;
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
       const lexp = exp.args.map((arg) => this.emitExpression(arg)).join(" && ");
       return toplevel ? lexp : ("(" + lexp + ")");
    }

    private emitLogicActionOrExpression(exp: TIRLogicActionOrExpression, toplevel: boolean): string {
        const lexp = exp.args.map((arg) => this.emitExpression(arg)).join(" || ");
        return toplevel ? lexp : ("(" + lexp + ")");
    }

    private emitPrefixNotOpExpression(exp: TIRPrefixNotExpression, toplevel: boolean): string {
        const nexp = `!${this.emitExpression(exp.exp)}`;
        return toplevel ? nexp : ("(" + nexp + ")");
    }

    private emitPrefixNegateOpExpression(exp: TIRPrefixNegateExpression, toplevel: boolean): string {
        const nexp = `-${this.emitExpression(exp.exp)}`;
        return toplevel ? nexp : ("(" + nexp + ")");
    }

    private emitBinAddExpression(exp: TIRBinAddExpression, toplevel: boolean): string {
        const bexp = `${this.emitExpression(exp.lhs)} + ${this.emitExpression(exp.rhs)}`

        if(exp.optype === "Nat") {
            return `$Runtime.safeMath(${bexp}, 0n, FIXED_NUMBER_MAX)`;
        }
        else if(exp.optype === "Int") {
            return `$Runtime.safeMath(${bexp}, FIXED_NUMBER_MIN, FIXED_NUMBER_MAX)`;
        }
        else {
            return toplevel ? bexp : ("(" + bexp + ")");
        }
    }

    private emitBinSubExpression(exp: TIRBinSubExpression, toplevel: boolean): string {
        const bexp = `${this.emitExpression(exp.lhs)} - ${this.emitExpression(exp.rhs)}`
        
        if(exp.optype === "Nat") {
            return `$Runtime.safeMath(${bexp}, 0n, FIXED_NUMBER_MAX)`;
        }
        else if(exp.optype === "Int") {
            return `$Runtime.safeMath(${bexp}, FIXED_NUMBER_MIN, FIXED_NUMBER_MAX)`;
        }
        else if(exp.optype === "BigNat") {
            return `$Runtime.safeMathUnderflow(${bexp}, 0n)`;
        }
        else {
            return toplevel ? bexp : ("(" + bexp + ")");
        }
    }

    private emitBinMultExpression(exp: TIRBinMultExpression, toplevel: boolean): string {
        const bexp = `${this.emitExpression(exp.lhs)} * ${this.emitExpression(exp.rhs)}`
        
        if(exp.optype === "Nat") {
            return `$Runtime.safeMath(${bexp}, 0n, FIXED_NUMBER_MAX)`;
        }
        else if(exp.optype === "Int") {
            return `$Runtime.safeMath(${bexp}, FIXED_NUMBER_MIN, FIXED_NUMBER_MAX)`;
        }
        else {
            return toplevel ? bexp : ("(" + bexp + ")");
        }
    }

    private emitBinDivExpression(exp: TIRBinDivExpression, toplevel: boolean): string {
        const lexp = this.emitExpression(exp.lhs);
        const rexp = this.emitExpression(exp.rhs);

        if(exp.optype === "Nat") {
            return `$Runtime.safeMathDiv((a, b) => a / b, (b) => b === 0n, ${lexp}, ${rexp})`;
        }
        else if(exp.optype === "Int") {
            return `$Runtime.safeMathDiv((a, b) => a / b, (b) => b === 0n, ${lexp}, ${rexp})`;
        }
        else if(exp.optype === "BigNat") {
            return `$Runtime.safeMathDiv((a, b) => a / b, (b) => b === 0n, ${lexp}, ${rexp})`;
        }
        else if(exp.optype === "BigInt") {
            return `$Runtime.safeMathDiv((a, b) => a / b, (b) => b === 0n, ${lexp}, ${rexp})`;
        }
        else if(exp.optype === "Rational") {
            return NOT_IMPLEMENTED_EXPRESSION(exp.tag + "--Rational");
        }
        else if(exp.optype === "Decimal") {
            return NOT_IMPLEMENTED_EXPRESSION(exp.tag + "--Decimal");
        }
        else {
            return `$Runtime.safeMathDiv((a, b) => a / b, (b) => b === 0.0, ${lexp}, ${rexp})`;
        }
    }

    private emitBinKeyEqBothUniqueExpression(exp: TIRBinKeyEqBothUniqueExpression): string {
        return `($KeyEqualOps.get("${exp.optype}"))(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)})`;
    }

    private emitBinKeyEqOneUniqueExpression(exp: TIRBinKeyEqOneUniqueExpression): string {
        return `$KeyEqualMixed("${exp.oftype}", ${this.emitExpression(exp.uarg, true)}, ${this.emitExpression(exp.garg, true)})`;
    }
    
    private emitBinKeyEqGeneralExpression(exp: TIRBinKeyEqGeneralExpression): string {
        return `$KeyEqualGeneral(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)})`;
    }

    private emitBinKeyNeqBothUniqueExpression(exp: TIRBinKeyNeqBothUniqueExpression, toplevel: boolean): string {
        const rr = `($KeyEqualOps.get("${exp.optype}"))(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)})`;
        return toplevel ? rr : "(" + rr + ")";
    }

    private emitBinKeyNeqOneUniqueExpression(exp: TIRBinKeyNeqOneUniqueExpression, toplevel: boolean): string {
        const rr = `$KeyEqualMixed("${exp.oftype}", ${this.emitExpression(exp.uarg, true)}, ${this.emitExpression(exp.garg, true)})`;
        return toplevel ? rr : "(" + rr + ")";
    }
    
    private emitBinKeyNeqGeneralExpression(exp: TIRBinKeyNeqGeneralExpression, toplevel: boolean): string {
        const rr = `$KeyEqualGeneral(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)})`;
        return toplevel ? rr : "(" + rr + ")";
    }

    private emitBinKeyUniqueLessExpression(exp: TIRBinKeyUniqueLessExpression): string {
        return `($KeyLessOps.get("${exp.optype}"))(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)})`;
    }

    private emitBinKeyGeneralLessExpression(exp: TIRBinKeyGeneralLessExpression): string {
        return `$KeyLessGeneral(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)})`;
    }

    private emitNumericEqExpression(exp: TIRNumericEqExpression, toplevel: boolean): string {
        const lexp = this.emitExpression(exp.lhs);
        const rexp = this.emitExpression(exp.rhs);

        let cmp = "[MISSING]";
        if(exp.optype === "Nat" || exp.optype === "Int") {
            cmp = `${lexp} === ${rexp}`;
        }
        else if(exp.optype === "BigNat" || exp.optype === "BigInt") {
            cmp = `${lexp} === ${rexp}`;
        }
        else if(exp.optype === "Rational") {
            cmp = NOT_IMPLEMENTED_EXPRESSION(exp.tag + "--Rational");
        }
        else if(exp.optype === "Float") {
            cmp = `${lexp} === ${rexp}`;
        }
        else {
            cmp = NOT_IMPLEMENTED_EXPRESSION(exp.tag + "--Decmial");
        }

        return toplevel ? cmp : "(" + cmp + ")";
    }

    private emitNumericNeqExpression(exp: TIRNumericNeqExpression, toplevel: boolean): string {
        const lexp = this.emitExpression(exp.lhs);
        const rexp = this.emitExpression(exp.rhs);

        let cmp = "[MISSING]";
        if(exp.optype === "Nat" || exp.optype === "Int") {
            cmp = `${lexp} !== ${rexp}`;
        }
        else if(exp.optype === "BigNat" || exp.optype === "BigInt") {
            cmp = `${lexp} !== ${rexp}`;
        }
        else if(exp.optype === "Rational") {
            cmp = NOT_IMPLEMENTED_EXPRESSION(exp.tag + "--Rational");
        }
        else if(exp.optype === "Float") {
            cmp = `${lexp} !== ${rexp}`;
        }
        else {
            cmp = NOT_IMPLEMENTED_EXPRESSION(exp.tag + "--Decmial");
        }

        return toplevel ? cmp : "(" + cmp + ")";
    }

    private emitNumericLessExpression(exp: TIRNumericLessExpression, toplevel: boolean): string {
        const lexp = this.emitExpression(exp.lhs);
        const rexp = this.emitExpression(exp.rhs);

        let cmp = "[MISSING]";
        if(exp.optype === "Nat" || exp.optype === "Int") {
            cmp = `${lexp} < ${rexp}`;
        }
        else if(exp.optype === "BigNat" || exp.optype === "BigInt") {
            cmp = `${lexp} < ${rexp}`;
        }
        else if(exp.optype === "Rational") {
            cmp = NOT_IMPLEMENTED_EXPRESSION(exp.tag + "--Rational");
        }
        else if(exp.optype === "Float") {
            cmp = `${lexp} < ${rexp}`;
        }
        else {
            cmp = NOT_IMPLEMENTED_EXPRESSION(exp.tag + "--Decmial");
        }

        return toplevel ? cmp : "(" + cmp + ")";
    }

    private emitNumericLessEqExpression(exp: TIRNumericLessEqExpression, toplevel: boolean): string {
        const lexp = this.emitExpression(exp.lhs);
        const rexp = this.emitExpression(exp.rhs);

        let cmp = "[MISSING]";
        if(exp.optype === "Nat" || exp.optype === "Int") {
            cmp = `${lexp} <= ${rexp}`;
        }
        else if(exp.optype === "BigNat" || exp.optype === "BigInt") {
            cmp = `${lexp} <= ${rexp}`;
        }
        else if(exp.optype === "Rational") {
            cmp = NOT_IMPLEMENTED_EXPRESSION(exp.tag + "--Rational");
        }
        else if(exp.optype === "Float") {
            cmp = `${lexp} <= ${rexp}`;
        }
        else {
            cmp = NOT_IMPLEMENTED_EXPRESSION(exp.tag + "--Decmial");
        }

        return toplevel ? cmp : "(" + cmp + ")";
    }

    private emitNumericGreaterExpression(exp: TIRNumericGreaterExpression, toplevel: boolean): string {
        const lexp = this.emitExpression(exp.lhs);
        const rexp = this.emitExpression(exp.rhs);

        let cmp = "[MISSING]";
        if(exp.optype === "Nat" || exp.optype === "Int") {
            cmp = `${lexp} > ${rexp}`;
        }
        else if(exp.optype === "BigNat" || exp.optype === "BigInt") {
            cmp = `${lexp} > ${rexp}`;
        }
        else if(exp.optype === "Rational") {
            cmp = NOT_IMPLEMENTED_EXPRESSION(exp.tag + "--Rational");
        }
        else if(exp.optype === "Float") {
            cmp = `${lexp} > ${rexp}`;
        }
        else {
            cmp = NOT_IMPLEMENTED_EXPRESSION(exp.tag + "--Decmial");
        }

        return toplevel ? cmp : "(" + cmp + ")";
    }

    private emitNumericGreaterEqExpression(exp: TIRNumericGreaterEqExpression, toplevel: boolean): string {
        const lexp = this.emitExpression(exp.lhs);
        const rexp = this.emitExpression(exp.rhs);

        let cmp = "[MISSING]";
        if(exp.optype === "Nat" || exp.optype === "Int") {
            cmp = `${lexp} >= ${rexp}`;
        }
        else if(exp.optype === "BigNat" || exp.optype === "BigInt") {
            cmp = `${lexp} >= ${rexp}`;
        }
        else if(exp.optype === "Rational") {
            cmp = NOT_IMPLEMENTED_EXPRESSION(exp.tag + "--Rational");
        }
        else if(exp.optype === "Float") {
            cmp = `${lexp} >= ${rexp}`;
        }
        else {
            cmp = NOT_IMPLEMENTED_EXPRESSION(exp.tag + "--Decmial");
        }

        return toplevel ? cmp : "(" + cmp + ")";
    }

    private emitBinLogicAndExpression(exp: TIRBinLogicAndExpression, toplevel: boolean): string {
        const rr = `${this.emitExpression(exp.lhs)} && ${this.emitExpression(exp.rhs)}`;
        return toplevel ? rr : "(" + rr + ")";
    }

    private emitBinLogicOrExpression(exp: TIRBinLogicOrExpression, toplevel: boolean): string {
        const rr = `${this.emitExpression(exp.lhs)} || ${this.emitExpression(exp.rhs)}`;
        return toplevel ? rr : "(" + rr + ")";
    }

    private emitBinLogicImpliesExpression(exp: TIRBinLogicImpliesExpression, toplevel: boolean): string {
        const rr = `!${this.emitExpression(exp.lhs)} || ${this.emitExpression(exp.rhs)}`;
        return toplevel ? rr : "(" + rr + ")";
    }

    private emitMapEntryConstructorExpression(exp: TIRMapEntryConstructorExpression): string {
        return `[${this.emitExpression(exp.kexp, true)}, ${this.emitExpression(exp.vexp, true)}]`;
    }

    private emitIfExpression(exp: TIRIfExpression, toplevel: boolean): string {
        let rstr = `${this.emitExpression(exp.ifentry.test)} ? ${this.emitExpression(exp.ifentry.value)} : `;
        for(let i = 0; i < exp.elifentries.length; ++i){
            rstr += `${this.emitExpression(exp.elifentries[i].test)} ? ${this.emitExpression(exp.elifentries[i].value)} : `
        }
        rstr += this.emitExpression(exp.elseentry);

        return toplevel ? rstr : "(" + rstr + ")";
    }

    private emitSwitchExpression(exp: TIRSwitchExpression, toplevel: boolean): string {
        return NOT_IMPLEMENTED_EXPRESSION(exp.tag);
    }
    
    private emitMatchExpression(exp: TIRMatchExpression, toplevel: boolean): string {
        return NOT_IMPLEMENTED_EXPRESSION(exp.tag);
    }

    private emitTaskSelfFieldExpression(exp: TIRTaskSelfFieldExpression): string {
        return `self.${exp.fname}`;
    }

    private emitTaskSelfControlExpression(exp: TIRTaskSelfControlExpression): string {
        return "self.$CNTL";
    }

    private emitTaskGetIDExpression(exp: TIRTaskGetIDExpression): string {
        return "self.$ID";
    }

    private emitCoerceSafeExpression(exp: TIRCoerceSafeExpression, toplevel: boolean): string {
        const srcunion = this.typeEncodedAsUnion(exp.exp.etype);
        const trgtunion = this.typeEncodedAsUnion(exp.totype);

        if(srcunion === trgtunion) {
            return this.emitExpression(exp.exp, toplevel);
        }
        else if(trgtunion) {
            const bval = `new UnionValue("${exp.fromtype}", ${this.emitExpression(exp.exp)})`;
            return toplevel ? bval : "(" + bval + ")";
        }
        else {
            const bval = `${this.emitExpression(exp.exp)}.value`;
            return toplevel ? bval : "(" + bval + ")";
        }
    }

    private emitCoerceRefCallResultExpression(exp: TIRCoerceSafeRefCallResultExpression, toplevel: boolean): string {
        const srcunion = this.typeEncodedAsUnion(exp.exp.etype);
        const trgtunion = this.typeEncodedAsUnion(exp.totype);

        if(srcunion === trgtunion) {
            return this.emitExpression(exp.exp, toplevel);
        }
        else if(trgtunion) {
            const bval = `((__expval__) => [__expval__[0], new UnionValue("${exp.fromtype}", __expval__[1])])(${this.emitExpression(exp.exp)})`;
            return toplevel ? bval : "(" + bval + ")";
        }
        else {
            const bval = `((__expval__) => [__expval__[0], __expval__[1].value])(${this.emitExpression(exp.exp)})`;
            return toplevel ? bval : "(" + bval + ")";
        }
    }

    private emitCoerceTaskRefCallResultExpression(exp: TIRCoerceSafeTaskRefCallResultExpression, toplevel: boolean): string {
        const srcunion = this.typeEncodedAsUnion(exp.exp.etype);
        const trgtunion = this.typeEncodedAsUnion(exp.totype);

        if(srcunion === trgtunion) {
            return this.emitExpression(exp.exp, toplevel);
        }
        else if(trgtunion) {
            const bval = `((__expval__) => [__expval__[0], new UnionValue("${exp.fromtype}", __expval__[1])])(${this.emitExpression(exp.exp)})`;
            return toplevel ? bval : "(" + bval + ")";
        }
        else {
            const bval = `((__expval__) => [__expval__[0], __expval__[1].value])(${this.emitExpression(exp.exp)})`;
            return toplevel ? bval : "(" + bval + ")";
        }
    }

    private emitCoerceActionCallResultExpression(exp: TIRCoerceSafeActionCallResultExpression, toplevel: boolean): string {
        const srcunion = this.typeEncodedAsUnion(exp.exp.etype);
        const trgtunion = this.typeEncodedAsUnion(exp.totype);

        if(srcunion === trgtunion) {
            return this.emitExpression(exp.exp, toplevel);
        }
        else if(trgtunion) {
            const bval = `((__expval__) => [__expval__[0], new UnionValue("${exp.fromtype}", __expval__[1])])(${this.emitExpression(exp.exp)})`;
            return toplevel ? bval : "(" + bval + ")";
        }
        else {
            const bval = `((__expval__) => [__expval__[0], __expval__[1].value])(${this.emitExpression(exp.exp)})`;
            return toplevel ? bval : "(" + bval + ")";
        }
    }

    private emitInjectExpression(exp: TIRInjectExpression, toplevel: boolean): string {
       return this.emitExpression(exp.exp, toplevel);
    }

    private emitExtractExpression(exp: TIRExtractExpression, toplevel: boolean): string {
       return this.emitExpression(exp.exp, toplevel);
    }
    
    private emitCreateCodePackExpression(exp: TIRCreateCodePackExpression): string {
       xxxx;
    }

    private emitIsNoneExpression(exp: TIRIsNoneExpression, toplevel: boolean): string {
       assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");

       const bval = `${this.emitExpression(exp.exp)}.tkey === "None"`;
       return toplevel ? bval : "(" + bval + ")";
    }

    private emitIsNotNoneExpression(exp: TIRIsNotNoneExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");

        const bval = `${this.emitExpression(exp.exp)}.tkey !== "None"`;
        return toplevel ? bval : "(" + bval + ")";
    }

    private emitIsNothingExpression(exp: TIRIsNothingExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");

        const bval = `${this.emitExpression(exp.exp)}.tkey === "Nothing"`;
        return toplevel ? bval : "(" + bval + ")";
    }

    private emitIsNotNothingExpression(exp: TIRIsNotNothingExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");

        const bval = `${this.emitExpression(exp.exp)}.tkey !== "Nothing"`;
        return toplevel ? bval : "(" + bval + ")";
    }

    private emitIsTypeExpression(exp: TIRIsTypeExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");
        assert(!this.typeEncodedAsUnion(exp.oftype), "this should be a subtype then");

        const bval = `${this.emitExpression(exp.exp)}.tkey === "${exp.oftype}"`;
        return toplevel ? bval : "(" + bval + ")";
    }

    private emitIsNotTypeExpression(exp: TIRIsNotTypeExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");
        assert(!this.typeEncodedAsUnion(exp.oftype), "this should be a subtype then");

        const bval = `${this.emitExpression(exp.exp)}.tkey !== "${exp.oftype}"`;
        return toplevel ? bval : "(" + bval + ")";
    }

    private emitIsSubTypeExpression(exp: TIRIsSubTypeExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");
        assert(this.typeEncodedAsUnion(exp.oftype), "this should be a oftype then");

        const bval = `($Runtime.subtypeMap.get("${exp.oftype}")).has(${this.emitExpression(exp.exp)}.tkey)`;
        return toplevel ? bval : "(" + bval + ")";
    }

    private emitIsNotSubTypeExpression(exp: TIRIsNotSubTypeExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");
        assert(this.typeEncodedAsUnion(exp.oftype), "this should be a oftype then");

        const bval = `!($Runtime.subtypeMap.get("${exp.oftype}")).has(${this.emitExpression(exp.exp)}.tkey)`;
        return toplevel ? bval : "(" + bval + ")";
    }

    private emitAsNoneExpression(exp: TIRAsNoneExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");

        const bval = `(${this.emitExpression(exp.exp)}.tkey === "None") ? undefined : raiseRuntimeError("cannot convert value to None")`;
        return toplevel ? bval : "(" + bval + ")";
    }
    
    private emitAsNotNoneExpression(exp: TIRAsNotNoneExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");

        let bval = "[NOT SET]";
        if(this.typeEncodedAsUnion(exp.oftype)) {
            bval = `((__expval__) => (__expval__.tkey !== "None") ? __expval__ : raiseRuntimeError("cannot convert value to Some"))(${this.emitExpression(exp.exp)})`;
        }
        else {
            bval = `((__expval__) => (__expval__.tkey !== "None") ? __expval__.value : raiseRuntimeError("cannot convert value to Some"))(${this.emitExpression(exp.exp)})`;
        }

        return toplevel ? bval : "(" + bval + ")";
    }

    private emitAsNothingExpression(exp: TIRAsNothingExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");

        const bval = `(${this.emitExpression(exp.exp)}.tkey === "None") ? null : raiseRuntimeError("cannot convert value to Nothing")`;
        return toplevel ? bval : "(" + bval + ")";
    }

    private emitAsTypeExpression(exp: TIRAsTypeExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");
        assert(!this.typeEncodedAsUnion(exp.oftype), "this should be a subtype then");

        const bval = `((__expval__) => (__expval__.tkey === "${exp.oftype}") ? __expval__ : raiseRuntimeError("cannot convert value to ${exp.oftype}"))(${this.emitExpression(exp.exp)})`;
        return toplevel ? bval : "(" + bval + ")";
    }
    
    private emitAsSubTypeExpression(exp: TIRAsSubTypeExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");
        assert(this.typeEncodedAsUnion(exp.oftype), "this should be a oftype then");

        const bval = `((__expval__) => $Runtime.subtypeMap.get("${exp.oftype}")).has(__expval__.tkey) ? __expval__ : raiseRuntimeError("cannot convert value to ${exp.oftype}"))(${this.emitExpression(exp.exp)})`;
        return toplevel ? bval : "(" + bval + ")";
    }

    private emitCallMemberFunctionExpression(exp: TIRCallMemberFunctionExpression, toplevel: boolean): string {
        const aargs = [this.emitExpression(exp.thisarg, true), ...exp.args.map((arg) => this.emitExpression(arg, true))];

        const ttype = this.m_assembly.typeMap.get(exp.tkey) as TIROOType;
        const invk = ttype.memberMethods.find((mm) => mm.ikey === exp.fkey);
        assert(invk !== undefined, "emitCallMemberFunctionExpression");

        const fexp = `${this.resolveTypeMemberAccess(exp.tkey)}`;
        let meexp = "[NOT SET]";
        if(invk.terms.length === 0) {
            meexp = `.${exp.fname}`;
        }
        else {
            meexp = `.$Methods["${exp.fkey}"]`;
        }
        
        const eexp = `${fexp}${meexp}(${aargs.join(", ")})`;

        return toplevel ? eexp : "(" + eexp + ")";
    }

    private emitCallMemberFunctionDynamicExpression(exp: TIRCallMemberFunctionDynamicExpression, toplevel: boolean): string {
        const thisarg = this.emitExpression(exp.thisarg, true);
        
        if(exp.inferfkey !== undefined) {

        }
        else {
            const thisunion = this.typeEncodedAsUnion(exp.thisarg.etype);
            const declunion = this.typeEncodedAsUnion(exp.tkey);
            let thisargas = "[NOT SET]";
            if (thisunion === declunion) {
                thisargas = "__expval__";
            }
            else {
                if (thisunion) {
                    thisargas = "__expval__.value";
                }
                else {
                    thisargas = `new UnionValue("${exp.thisarg.etype}", __expval__)`;
                }
            }

            let vtable = "[NOT SET]";
            if(thisunion) {
                vtable = `$Runtime.vtablemap.get(__expval__.tkey).$VTable["${exp.fkey}"]`
            }
            else {
                vtable = `${this.resolveTypeMemberAccess(exp.thisarg.etype)}.$VTable["${exp.fkey}"]`;
            }
            

            const aargs = exp.args.map((arg) => this.emitExpression(arg, true));
            const eexp = `((__expval__) => ${vtable}(${[thisargas, ...aargs].join(", ")}))(${thisarg})`;

            return toplevel ? eexp : "(" + eexp + ")";
        }
    }
    
    private emitCallMemberFunctionSelfRefExpression(exp: TIRCallMemberFunctionSelfRefExpression, toplevel: boolean): string {
        const aargs = [this.emitExpression(exp.thisarg, true), ...exp.args.map((arg) => this.emitExpression(arg, true))];

        const ttype = this.m_assembly.typeMap.get(exp.tkey) as TIROOType;
        const invk = ttype.memberMethods.find((mm) => mm.ikey === exp.fkey);
        assert(invk !== undefined, "emitCallMemberFunctionExpression");

        const fexp = `${this.resolveTypeMemberAccess(exp.tkey)}`;
        let meexp = "[NOT SET]";
        if(invk.terms.length === 0) {
            meexp = `.${exp.fname}`;
        }
        else {
            meexp = `.$Methods["${exp.fkey}"]`;
        }

        const eexp = `${fexp}${meexp}(${aargs.join(", ")})`;

        return toplevel ? eexp : "(" + eexp + ")";
    }

    private emitCallMemberFunctionTaskExpression(exp: TIRCallMemberFunctionTaskExpression, toplevel: boolean): string {
        const aargs = ["self", ...exp.args.map((arg) => this.emitExpression(arg, true))];

        const ttype = this.m_assembly.typeMap.get(exp.tsktype) as TIRTaskType;
        const invk = ttype.memberMethods.find((mm) => mm.ikey === exp.fkey);
        assert(invk !== undefined, "emitCallMemberFunctionExpression");

        const fexp = `${this.resolveTypeMemberAccess(exp.tsktype)}`;
        let meexp = "[NOT SET]";
        if(invk.terms.length === 0) {
            meexp = `.${exp.fname}`;
        }
        else {
            meexp = `.$Methods["${exp.fkey}"]`;
        }

        const eexp = `${fexp}${meexp}(${aargs.join(", ")})`;

        return toplevel ? eexp : "(" + eexp + ")";
    }

    private emitCallMemberFunctionTaskSelfRefExpression(exp: TIRCallMemberFunctionTaskSelfRefExpression, toplevel: boolean): string {
        const aargs = ["self", ...exp.args.map((arg) => this.emitExpression(arg, true))];

        const ttype = this.m_assembly.typeMap.get(exp.tsktype) as TIRTaskType;
        const invk = ttype.memberMethods.find((mm) => mm.ikey === exp.fkey);
        assert(invk !== undefined, "emitCallMemberFunctionExpression");

        const fexp = `${this.resolveTypeMemberAccess(exp.tsktype)}`;
        let meexp = "[NOT SET]";
        if(invk.terms.length === 0) {
            meexp = `.${exp.fname}`;
        }
        else {
            meexp = `.$Methods["${exp.fkey}"]`;
        }

        const eexp = `${fexp}${meexp}(${aargs.join(", ")})`;

        return toplevel ? eexp : "(" + eexp + ")";
    }

    private emitCallMemberActionExpression(exp: TIRCallMemberActionExpression, toplevel: boolean): string {
        const aargs = ["self", ...exp.args.map((arg) => this.emitExpression(arg, true))];
        const fexp = `${this.resolveTypeMemberAccess(exp.tsktype)}.${exp.fname}`;
        const eexp = `${fexp}(${aargs.join(", ")})`;

        return toplevel ? eexp : "(" + eexp + ")";
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
                return this.emitLiteralTypedPrimitiveDirectExpression(exp as TIRLiteralTypedPrimitiveDirectExpression, toplevel || false);
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
                return this.emitResultOkConstructorExpression(exp as TIRResultOkConstructorExpression, toplevel || false);
            }
            case TIRExpressionTag.ResultErrConstructorExpression: {
                return this.emitResultErrConstructorExpression(exp as TIRResultErrConstructorExpression, toplevel || false);
            }
            case TIRExpressionTag.SomethingConstructorExpression: {
                return this.emitSomethingConstructorExpression(exp as TIRSomethingConstructorExpression, toplevel || false);
            }
            case TIRExpressionTag.TypedeclDirectExpression: {
                return this.emitTypedeclDirectExpression(exp as TIRTypedeclDirectExpression, toplevel || false);
            }
            case TIRExpressionTag.TypedeclConstructorExpression: {
                return this.emitTypedeclConstructorExpression(exp as TIRTypedeclConstructorExpression);
            }
            case TIRExpressionTag.CallNamespaceFunctionExpression: {
                return this.emitCallNamespaceFunctionExpression(exp as TIRCallNamespaceFunctionExpression);
            }
            case TIRExpressionTag.CallNamespaceOperatorExpression: {
                return this.emitCallNamespaceOperatorExpression(exp as TIRCallNamespaceOperatorExpression);
            }
            case TIRExpressionTag.CallStaticFunctionExpression: {
                return this.emitCallStaticFunctionExpression(exp as TIRCallStaticFunctionExpression);
            }
            case TIRExpressionTag.LogicActionAndExpression: {
                return this.emitLogicActionAndExpression(exp as TIRLogicActionAndExpression, toplevel || false);
            }
            case TIRExpressionTag.LogicActionOrExpression: {
                return this.emitLogicActionOrExpression(exp as TIRLogicActionOrExpression, toplevel || false);
            }
            case TIRExpressionTag.PrefixNotExpression: {
                return this.emitPrefixNotOpExpression(exp as TIRPrefixNotExpression, toplevel || false);
            }
            case TIRExpressionTag.PrefixNegateExpression: {
                return this.emitPrefixNegateOpExpression(exp as TIRPrefixNegateExpression, toplevel || false);
            }
            case TIRExpressionTag.BinAddExpression: {
                return this.emitBinAddExpression(exp as TIRBinAddExpression, toplevel || false);
            }
            case TIRExpressionTag.BinSubExpression: {
                return this.emitBinSubExpression(exp as TIRBinSubExpression, toplevel || false);
            }
            case TIRExpressionTag.BinMultExpression: {
                return this.emitBinMultExpression(exp as TIRBinMultExpression, toplevel || false);
            }
            case TIRExpressionTag.BinDivExpression: {
                return this.emitBinDivExpression(exp as TIRBinDivExpression, toplevel || false);
            }
            case TIRExpressionTag.BinKeyEqBothUniqueExpression: {
                return this.emitBinKeyEqBothUniqueExpression(exp as TIRBinKeyEqBothUniqueExpression);
            }
            case TIRExpressionTag.BinKeyEqOneUniqueExpression: {
                return this.emitBinKeyEqOneUniqueExpression(exp as TIRBinKeyEqOneUniqueExpression);
            }
            case TIRExpressionTag.BinKeyEqGeneralExpression: {
                return this.emitBinKeyEqGeneralExpression(exp as TIRBinKeyEqGeneralExpression);
            }
            case TIRExpressionTag.BinKeyNeqBothUniqueExpression: {
                return this.emitBinKeyNeqBothUniqueExpression(exp as TIRBinKeyNeqBothUniqueExpression, toplevel || false);
            }
            case TIRExpressionTag.BinKeyNeqOneUniqueExpression: {
                return this.emitBinKeyNeqOneUniqueExpression(exp as TIRBinKeyNeqOneUniqueExpression, toplevel || false);
            }
            case TIRExpressionTag.BinKeyNeqGeneralExpression: {
                return this.emitBinKeyNeqGeneralExpression(exp as TIRBinKeyNeqGeneralExpression, toplevel || false);
            }
            case TIRExpressionTag.BinKeyUniqueLessExpression: {
                return this.emitBinKeyUniqueLessExpression(exp as TIRBinKeyUniqueLessExpression);
            }
            case TIRExpressionTag.BinKeyGeneralLessExpression: {
                return this.emitBinKeyGeneralLessExpression(exp as TIRBinKeyGeneralLessExpression);
            }
            case TIRExpressionTag.NumericEqExpression: {
                return this.emitNumericEqExpression(exp as TIRNumericEqExpression, toplevel || false);
            }
            case TIRExpressionTag.NumericNeqExpression: {
                return this.emitNumericNeqExpression(exp as TIRNumericNeqExpression, toplevel || false);
            }
            case TIRExpressionTag.NumericLessExpression: {
                return this.emitNumericLessExpression(exp as TIRNumericLessExpression, toplevel || false);
            }
            case TIRExpressionTag.NumericLessEqExpression: {
                return this.emitNumericLessEqExpression(exp as TIRNumericLessEqExpression, toplevel || false);
            }
            case TIRExpressionTag.NumericGreaterExpression: {
                return this.emitNumericGreaterExpression(exp as TIRNumericGreaterExpression, toplevel || false);
            }
            case TIRExpressionTag.NumericGreaterEqExpression: {
                return this.emitNumericGreaterEqExpression(exp as TIRNumericGreaterEqExpression, toplevel || false);
            }
            case TIRExpressionTag.BinLogicAndExpression: {
                return this.emitBinLogicAndExpression(exp as TIRBinLogicAndExpression, toplevel || false);
            }
            case TIRExpressionTag.BinLogicOrExpression: {
                return this.emitBinLogicOrExpression(exp as TIRBinLogicOrExpression, toplevel || false);
            }
            case TIRExpressionTag.BinLogicImpliesExpression: {
                return this.emitBinLogicImpliesExpression(exp as TIRBinLogicImpliesExpression, toplevel || false);
            }
            case TIRExpressionTag.MapEntryConstructorExpression: {
                return this.emitMapEntryConstructorExpression(exp as TIRMapEntryConstructorExpression);
            }
            case TIRExpressionTag.IfExpression: {
                return this.emitIfExpression(exp as TIRIfExpression, toplevel || false);
            }
            case TIRExpressionTag.SwitchExpression: {
                return this.emitSwitchExpression(exp as TIRSwitchExpression, toplevel || false);
            }
            case TIRExpressionTag.MatchExpression: {
                return this.emitMatchExpression(exp as TIRMatchExpression, toplevel || false);
            }
            case TIRExpressionTag.TaskSelfFieldExpression: {
                return this.emitTaskSelfFieldExpression(exp as TIRTaskSelfFieldExpression);
            }
            case TIRExpressionTag.TaskSelfControlExpression: {
                return this.emitTaskSelfControlExpression(exp as TIRTaskSelfControlExpression);
            }
            case TIRExpressionTag.TaskGetIDExpression: {
                return this.emitTaskGetIDExpression(exp as TIRTaskGetIDExpression);
            }
            case TIRExpressionTag.CoerceSafeExpression: {
                return this.emitCoerceSafeExpression(exp as TIRCoerceSafeExpression, toplevel || false);
            }
            case TIRExpressionTag.CoerceRefCallResultExpression: {
                return this.emitCoerceRefCallResultExpression(exp as TIRCoerceSafeRefCallResultExpression, toplevel || false);
            }
            case TIRExpressionTag.CoerceTaskRefCallResultExpression: {
                return this.emitCoerceTaskRefCallResultExpression(exp as TIRCoerceSafeTaskRefCallResultExpression, toplevel || false);
            }
            case TIRExpressionTag.CoerceActionCallResultExpression: {
                return this.emitCoerceActionCallResultExpression(exp as TIRCoerceSafeActionCallResultExpression, toplevel || false);
            }
            case TIRExpressionTag.InjectExpression: {
                return this.emitInjectExpression(exp as TIRInjectExpression, toplevel || false);
            }
            case TIRExpressionTag.ExtractExpression: {
                return this.emitExtractExpression(exp as TIRExtractExpression, toplevel || false);
            }
            case TIRExpressionTag.CreateCodePackExpression: {
                return this.emitCreateCodePackExpression(exp as TIRCreateCodePackExpression);
            }
            case TIRExpressionTag.IsNoneExpression: {
                return this.emitIsNoneExpression(exp as TIRIsNoneExpression, toplevel || false);
            }
            case TIRExpressionTag.IsNotNoneExpression: {
                return this.emitIsNotNoneExpression(exp as TIRIsNotNoneExpression, toplevel || false);
            }
            case TIRExpressionTag.IsNothingExpression: {
                return this.emitIsNothingExpression(exp as TIRIsNothingExpression, toplevel || false);
            }
            case TIRExpressionTag.IsNotNothingExpression: {
                return this.emitIsNotNothingExpression(exp as TIRIsNotNothingExpression, toplevel || false);
            }
            case TIRExpressionTag.IsTypeExpression: {
                return this.emitIsTypeExpression(exp as TIRIsTypeExpression, toplevel || false);
            }
            case TIRExpressionTag.IsNotTypeExpression: {
                return this.emitIsNotTypeExpression(exp as TIRIsNotTypeExpression, toplevel || false);
            }
            case TIRExpressionTag.IsSubTypeExpression: {
                return this.emitIsSubTypeExpression(exp as TIRIsSubTypeExpression, toplevel || false);
            }
            case TIRExpressionTag.IsNotSubTypeExpression: {
                return this.emitIsNotSubTypeExpression(exp as TIRIsNotSubTypeExpression, toplevel || false);
            }
            case TIRExpressionTag.AsNoneExpression: {
                return this.emitAsNoneExpression(exp as TIRAsNoneExpression, toplevel || false);
            }
            case TIRExpressionTag.AsNotNoneExpression: {
                return this.emitAsNotNoneExpression(exp as TIRAsNotNoneExpression, toplevel || false);
            }
            case TIRExpressionTag.AsNothingExpression: {
                return this.emitAsNothingExpression(exp as TIRAsNothingExpression, toplevel || false);
            }
            case TIRExpressionTag.AsTypeExpression: {
                return this.emitAsTypeExpression(exp as TIRAsTypeExpression, toplevel || false);
            }
            case TIRExpressionTag.AsSubTypeExpression: {
                return this.emitAsSubTypeExpression(exp as TIRAsSubTypeExpression, toplevel || false);
            }
            case TIRExpressionTag.CallMemberFunctionExpression: {
                return this.emitCallMemberFunctionExpression(exp as TIRCallMemberFunctionExpression, toplevel || false);
            }
            case TIRExpressionTag.CallMemberFunctionDynamicExpression: {
                return this.emitCallMemberFunctionDynamicExpression(exp as TIRCallMemberFunctionDynamicExpression, toplevel || false);
            }
            case TIRExpressionTag.CallMemberFunctionSelfRefExpression: {
                return this.emitCallMemberFunctionSelfRefExpression(exp as TIRCallMemberFunctionSelfRefExpression, toplevel || false);
            }
            case TIRExpressionTag.CallMemberFunctionTaskExpression: {
                return this.emitCallMemberFunctionTaskExpression(exp as TIRCallMemberFunctionTaskExpression, toplevel || false);
            }
            case TIRExpressionTag.CallMemberFunctionTaskSelfRefExpression: {
                return this.emitCallMemberFunctionTaskSelfRefExpression(exp as TIRCallMemberFunctionTaskSelfRefExpression, toplevel || false);
            }
            case TIRExpressionTag.CallMemberActionExpression: {
                return this.emitCallMemberActionExpression(exp as TIRCallMemberActionExpression, toplevel || false);
            }
            default: {
                assert(false, `Unknown expression kind ${exp.tag}`);
                return `[UNKNOWN TAG ${exp.tag}]`
            }
        }
    }

    private emitNopStatement(stmt: TIRNopStatement): string {
        return "; //nop";
    }

    private emitAbortStatement(stmt: TIRAbortStatement): string {
        return `$Runtime.raiseUserAssert("${stmt.msg}" + "-- ${this.m_file}@${stmt.sinfo.line}");`;
    }

    private emitAssertCheckStatement(stmt: TIRAssertCheckStatement): string {
        return `$Runtime.raiseUserAssertIf(!${this.emitExpression(stmt.cond, true)}, "${stmt.msg}" + "-- ${this.m_file}@${stmt.sinfo.line}");`;
    }

    private emitDebugStatement(stmt: TIRDebugStatement): string {
        return `try { console.log(${this.emitExpression(stmt.value, true)}); } catch(ex) { console.log("__debug(${stmt.value.expstr}) evaluation failed"); }`;
    }

    private emitVarDeclareStatement(stmt: TIRVarDeclareStatement): string {
        return `let ${stmt.vname};`;
    }

    private emitVarDeclareAndAssignStatement(stmt: TIRVarDeclareAndAssignStatement): string {
        return (stmt.isConst ? "const " : "let ") + `${stmt.vname} = ${this.emitExpression(stmt.vexp, true)};`;
    }

    private emitVarAssignStatement(stmt: TIRVarAssignStatement): string {
        return `${stmt.vname} = ${this.emitExpression(stmt.vexp, true)};`;
    }

    private emitVarDeclareAndAssignStatementWRef(stmt: TIRVarDeclareAndAssignStatementWRef): string {
        const tmpv = `$_tmp_${this.m_varCtr++}`; 
        return (stmt.isConst ? "const " : "let ") + `[${tmpv}, ${stmt.vname}] = ${this.emitExpression(stmt.vexp, true)}; ${stmt.refvar} = ${tmpv};`;
    }

    private emitVarAssignStatementWRef(stmt: TIRVarAssignStatementWRef): string {
        return `[${stmt.refvar}, ${stmt.vname}] = ${this.emitExpression(stmt.vexp)};`;
    }

    private emitVarDeclareAndAssignStatementWTaskRef(stmt: TIRVarDeclareAndAssignStatementWTaskRef): string {
        const tmpv = `$_tmp_${this.m_varCtr++}`; 
        return (stmt.isConst ? "const " : "let ") + `[${tmpv}, ${stmt.vname}] = ${this.emitExpression(stmt.vexp, true)}; self = ${tmpv};`;
    }

    private emitVarAssignStatementWTaskRef(stmt: TIRVarDeclareAndAssignStatementWTaskRef): string {
        return `[self, ${stmt.vname}] = ${this.emitExpression(stmt.vexp)};`;
    }

    private emitVarDeclareAndAssignStatementWAction(stmt: TIRVarDeclareAndAssignStatementWAction): string {
        const tmpv = `$_tmp_${this.m_varCtr++}`; 
        return (stmt.isConst ? "const " : "let ") + `[${tmpv}, ${stmt.vname}] = ${this.emitExpression(stmt.vexp, true)}; self = ${tmpv};`;
    }

    private emitVarAssignStatementWAction(stmt:  TIRVarAssignStatementWAction): string {
        return `[self, ${stmt.vname}] = ${this.emitExpression(stmt.vexp)};`;
    }

    private emitCallStatementWRef(stmt: TIRCallStatementWRef): string {
        return `[${stmt.refvar}] = ${this.emitExpression(stmt.vexp, true)};`;
    }

    private emitCallStatementWTaskRef(stmt: TIRCallStatementWTaskRef): string {
        return `[self] = ${this.emitExpression(stmt.vexp, true)};`;
    }

    private emitCallStatementWAction(stmt: TIRCallStatementWAction): string {
        return `[self] = ${this.emitExpression(stmt.vexp, true)};`;
    }

    private emitReturnStatement(stmt: TIRReturnStatement): string {
        return `return ${this.emitExpression(stmt.value, true)};`;
    }

    private emitReturnStatementWRef(stmt: TIRReturnStatementWRef): string {
        return `return [$_this, ${this.emitExpression(stmt.value, true)}];`;
    }

    private emitReturnStatementWTaskRef(stmt: TIRReturnStatementWTaskRef): string {
        return `return [self, ${this.emitExpression(stmt.value, true)}];`;
    }

    private emitReturnStatementWAction(stmt: TIRReturnStatementWAction): string {
        return `return [self, ${this.emitExpression(stmt.value, true)}];`;
    }   

    private emitIfStatement(stmt: TIRIfStatement, indent: string): string {
        let sstr = `if(${this.emitExpression(stmt.ifentry.test, true)}) ${this.emitScopedBlock(stmt.ifentry.value, indent)}\n`;

        for(let i = 0; i < stmt.elifentries.length; ++i) {
            sstr += indent + `else if(${this.emitExpression(stmt.elifentries[i].test, true)}) ${this.emitScopedBlock(stmt.elifentries[i].value, indent)}\n`;
        }

        sstr += indent + `else ${this.emitScopedBlock(stmt.elseentry, indent)}\n`;

        return sstr;
    }

    private emitSwitchStatement(stmt: TIRSwitchStatement, indent: string): string {
        let sstr = `if(${this.emitExpression(stmt.clauses[0].match, true)}) ${this.emitScopedBlock(stmt.clauses[0].value, indent)}\n`;

        for(let i = 1; i < stmt.clauses.length; ++i) {
            sstr += indent + `else if(${this.emitExpression(stmt.clauses[i].match, true)}) ${this.emitScopedBlock(stmt.clauses[i].value, indent)}\n`;
        }

        if(stmt.edefault !== undefined) {
            sstr += indent + `else ${this.emitScopedBlock(stmt.edefault, indent)}\n`;
        }
        else {
            sstr += indent + "else {\n"
            if(stmt.isexhaustive) {
                sstr += indent + "    ;\n";
            }
            else {
                sstr += indent + "    " + `$Runtime.raiseRuntimeError("Non-exhaustive switch statement" + -- "${this.m_file} @ ${stmt.sinfo.line}")` + ";\n"
            }
            sstr += indent + "}\n";
        }

        return sstr;
    }

    private emitMatchStatement(stmt: TIRMatchStatement, indent: string): string {
        let sstr = `if(${this.emitExpression(stmt.clauses[0].match, true)}) ${this.emitScopedBlock(stmt.clauses[0].value, indent)}\n`;

        for(let i = 1; i < stmt.clauses.length; ++i) {
            sstr += indent + `else if(${this.emitExpression(stmt.clauses[i].match, true)}) ${this.emitScopedBlock(stmt.clauses[i].value, indent)}\n`;
        }

        if(stmt.edefault !== undefined) {
            sstr += indent + `else ${this.emitScopedBlock(stmt.edefault, indent)}\n`;
        }
        else {
            sstr += indent + "else {\n"
            if(stmt.isexhaustive) {
                sstr += indent + "    ;\n";
            }
            else {
                sstr += indent + "    " + `$Runtime.raiseRuntimeError("Non-exhaustive match statement" + -- "${this.m_file} @ ${stmt.sinfo.line}")` + ";\n"
            }
            sstr += indent + "}\n";
        }

        return sstr;
    }

    private emitEnvironmentFreshStatement(stmt: TIREnvironmentFreshStatement): string {
        const binds = stmt.assigns.map((asgn) => `["${asgn.keyname}", {tkey: "${asgn.valexp[0]}", value: ${this.emitExpression(asgn.valexp[1], true)}}]`);
        return `self.$environment = new $Runtime.BSQEnvironment(undefined, ${binds.join(", ")});`
    }

    private emitEnvironmentSetStatement(stmt: TIREnvironmentSetStatement): string {
        const binds = stmt.assigns.map((asgn) => {
            if(asgn.valexp === undefined) {
                return `$Runtime.BSQEnvironment.clear(self.$environment, "${asgn.keyname}");`
            }
            else {
                return `$Runtime.BSQEnvironment.set(self.$environment, "${asgn.keyname}", ${this.emitExpression(asgn.valexp[1], true)}, "${asgn.valexp[0]}");`
            }
        });

        return binds.join(" ");
    }

    private emitEnvironmentSetStatementBracket(stmt: TIREnvironmentSetStatementBracket, indent: string): string {
        let sstr = "";
        let tmpe = `$_tmpenv_${this.m_varCtr++}`;
        if(stmt.isFresh) {
            sstr = `const ${tmpe} = self.$environment; self.$environment = new $Runtime.BSQEnvironment(undefined);`;
        }
        else {
            sstr = `self.$environment = $Runtime.BSQEnvironment.push(self.$environment);`;
        }

        const binds = stmt.assigns.map((asgn) => {
            if(asgn.valexp === undefined) {
                return `$Runtime.BSQEnvironment.clear(self.$environment, "${asgn.keyname}");`
            }
            else {
                return `$Runtime.BSQEnvironment.set(self.$environment, "${asgn.keyname}", ${this.emitExpression(asgn.valexp[1], true)}, "${asgn.valexp[0]}");`
            }
        });
        sstr += (binds.length !== 0) ? ("\n" + indent + binds.join(" ")) : ""

        if(stmt.block instanceof TIRScopedBlockStatement) {
            sstr += this.emitScopedBlock(stmt.block, indent);
        }
        else {
            sstr += this.emitUnscopedBlock(stmt.block, indent);
        }

        if(stmt.isFresh) {
            sstr += `self.$environment = ${tmpe}\n`;
        }
        else {
            sstr += `self.$environment = $Runtime.BSQEnvironment.pop(self.$environment);\n`;
        }

        return sstr;
    }

    private emitTaskRunStatement(stmt: TIRTaskRunStatement): string {
        const taskaccess = this.resolveTypeMemberAccess(stmt.task);
        const vdcl = stmt.isdefine ? (stmt.isconst ? `let ${stmt.vtrgt.name}` : `var ${stmt.vtrgt.name}`) : stmt.vtrgt.name;

        const execargs = `{${stmt.taskargs.map((earg) => earg.argn + ": " + this.emitExpression(earg.argv, true)).join(", ")}}`;
        const consarg = this.emitExpression(stmt.consarg.rarg, true);
        const callargs = stmt.args.map((arg) => this.emitExpression(arg, true));

        return `${vdcl} = await ${taskaccess}.$mainfunc(${execargs}, ${consarg}, ${callargs});`;
    }

    private emitTaskMultiStatement(stmt: TIRTaskMultiStatement): string {
        return NOT_IMPLEMENTED_STATEMENT(stmt.tag);
    }

    private emitTaskDashStatement(stmt: TIRTaskDashStatement): string {
        return NOT_IMPLEMENTED_STATEMENT(stmt.tag);
    }

    private emitTaskAllStatement(stmt: TIRTaskAllStatement): string {
        return NOT_IMPLEMENTED_STATEMENT(stmt.tag);
    }

    private emitTaskRaceStatement(stmt: TIRTaskRaceStatement): string {
        return NOT_IMPLEMENTED_STATEMENT(stmt.tag);
    }

    private emitTaskSetSelfFieldStatement(stmt: TIRTaskSetSelfFieldStatement): string {
        return `self.${stmt.fname} = ${this.emitExpression(stmt.value, true)};`;
    }

    private emitLoggerEmitStatement(stmt: TIRLoggerEmitStatement): string {
        const fmt = `${stmt.fmt.namespace}.${stmt.fmt}`; 
        const args = stmt.args.map((arg) => this.emitExpression(arg)).join(", ")

        return `if($Runtime.checkloglevel(${stmt.level})) { $Runtime.log(${stmt.level}, ${fmt}, ${args}); }`
    }

    private emitLoggerEmitConditionalStatement(stmt: TIRLoggerEmitConditionalStatement): string {
        const fmt = `${stmt.fmt.namespace}.${stmt.fmt}`; 
        const args = stmt.args.map((arg) => this.emitExpression(arg)).join(", ")
        
        const test = this.emitExpression(stmt.cond);
        return `if($Runtime.checkloglevel(${stmt.level} && ${test})) { $Runtime.log(${stmt.level}, ${fmt}, ${args}); }`
    }

    emitScopedBlock(blck: TIRScopedBlockStatement, indent: string): string {
        const stmts = blck.ops.map((op) => indent + "    " + this.emitStatement(op, indent + "    ")).join("\n");

        return indent + "{\n" + stmts + "\n" + indent + "}";
    }

    emitUnscopedBlock(blck: TIRUnscopedBlockStatement, indent: string): string {
        const stmts = blck.ops.map((op) => indent + "    " + this.emitStatement(op, indent + "    ")).join("\n");

        return indent + "/*{|*/\n" + stmts + "\n" + indent + "/*|}/*";
    }

    private emitStatement(stmt: TIRStatement, indent: string): string {
        switch(stmt.tag) {
            case TIRStatementTag.NopStatement: {
                return this.emitNopStatement(stmt as TIRNopStatement);
            }
            case TIRStatementTag.AbortStatement: {
                return this.emitAbortStatement(stmt as TIRAbortStatement);
            }
            case TIRStatementTag.AssertCheckStatement: {
                return this.emitAssertCheckStatement(stmt as TIRAssertCheckStatement);
            }
            case TIRStatementTag.DebugStatement: {
                return this.emitDebugStatement(stmt as TIRDebugStatement);
            }
            case TIRStatementTag.VarDeclareStatement: {
                return this.emitVarDeclareStatement(stmt as TIRVarDeclareStatement);
            }
            case TIRStatementTag.VarDeclareAndAssignStatement: {
                return this.emitVarDeclareAndAssignStatement(stmt as TIRVarDeclareAndAssignStatement);
            }
            case TIRStatementTag.VarAssignStatement: {
                return this.emitVarAssignStatement(stmt as TIRVarAssignStatement);
            }
            case TIRStatementTag.VarDeclareAndAssignStatementWRef: {
                return this.emitVarDeclareAndAssignStatementWRef(stmt as TIRVarDeclareAndAssignStatementWRef);
            }
            case TIRStatementTag.VarAssignStatementWRef: {
                return this.emitVarAssignStatementWRef(stmt as TIRVarAssignStatementWRef);
            }
            case TIRStatementTag.VarDeclareAndAssignStatementWTaskRef: {
                return this.emitVarDeclareAndAssignStatementWTaskRef(stmt as TIRVarDeclareAndAssignStatementWTaskRef);
            }
            case TIRStatementTag.VarAssignStatementWTaskRef: {
                return this.emitVarAssignStatementWTaskRef(stmt as TIRVarDeclareAndAssignStatementWTaskRef);
            }
            case TIRStatementTag.VarDeclareAndAssignStatementWAction: {
                return this.emitVarDeclareAndAssignStatementWAction(stmt as TIRVarDeclareAndAssignStatementWAction);
            }
            case TIRStatementTag.VarAssignStatementWAction: {
                return this.emitVarAssignStatementWAction(stmt as TIRVarAssignStatementWAction);
            }
            case TIRStatementTag.CallStatementWRef: {
                return this.emitCallStatementWRef(stmt as TIRCallStatementWRef);
            }
            case TIRStatementTag.CallStatementWTaskRef: {
                return this.emitCallStatementWTaskRef(stmt as TIRCallStatementWTaskRef);
            }
            case TIRStatementTag.CallStatementWAction: {
                return this.emitCallStatementWAction(stmt as TIRCallStatementWAction);
            }
            case TIRStatementTag.ReturnStatement: {
                return this.emitReturnStatement(stmt as TIRReturnStatement);
            }
            case TIRStatementTag.ReturnStatementWRef: {
                return this.emitReturnStatementWRef(stmt as TIRReturnStatementWRef);
            }
            case TIRStatementTag.ReturnStatementWTaskRef: {
                return this.emitReturnStatementWTaskRef(stmt as TIRReturnStatementWTaskRef);
            }
            case TIRStatementTag.ReturnStatementWAction: {
                return this.emitReturnStatementWAction(stmt as TIRReturnStatementWAction);
            }
            case TIRStatementTag.IfStatement: {
                return this.emitIfStatement(stmt as TIRIfStatement, indent);
            }
            case TIRStatementTag.SwitchStatement: {
                return this.emitSwitchStatement(stmt as TIRSwitchStatement, indent);
            }
            case TIRStatementTag.MatchStatement: {
                return this.emitMatchStatement(stmt as TIRMatchStatement, indent);
            }
            case TIRStatementTag.EnvironmentFreshStatement: {
                return this.emitEnvironmentFreshStatement(stmt as TIREnvironmentFreshStatement);
            }
            case TIRStatementTag.EnvironmentSetStatement: {
                return this.emitEnvironmentSetStatement(stmt as TIREnvironmentSetStatement);
            }
            case TIRStatementTag.EnvironmentSetStatementBracket: {
                return this.emitEnvironmentSetStatementBracket(stmt as TIREnvironmentSetStatementBracket, indent);
            }
            case TIRStatementTag.TaskRunStatement: {
                return this.emitTaskRunStatement(stmt as TIRTaskRunStatement);
            }
            case TIRStatementTag.TaskMultiStatement: {
                return this.emitTaskMultiStatement(stmt as TIRTaskMultiStatement);
            }
            case TIRStatementTag.TaskDashStatement: {
                return this.emitTaskDashStatement(stmt as TIRTaskDashStatement);
            }
            case TIRStatementTag.TaskAllStatement: {
                return this.emitTaskAllStatement(stmt as TIRTaskAllStatement);
            }
            case TIRStatementTag.TaskRaceStatement: {
                return this.emitTaskRaceStatement(stmt as TIRTaskRaceStatement);
            }
            case TIRStatementTag.TaskSetSelfFieldStatement: {
                return this.emitTaskSetSelfFieldStatement(stmt as TIRTaskSetSelfFieldStatement);
            }
            case TIRStatementTag.LoggerEmitStatement: {
                return this.emitLoggerEmitStatement(stmt as TIRLoggerEmitStatement);
            }
            case TIRStatementTag.LoggerEmitConditionalStatement: {
                return this.emitLoggerEmitConditionalStatement(stmt as TIRLoggerEmitConditionalStatement);
            }
            default: {
                assert(false, `Unknown statement kind ${stmt.tag}`);
                return `[UNKNOWN TAG ${stmt.tag}]`
            }
        }
    }

    emitBodyStatementList(body: TIRStatement[], preconds: TIRPreConditionDecl[], postconds: TIRPostConditionDecl[], indent: string, fname: string, extractres: boolean): string {
        const bodyindent = indent + "    ";
        let rconds = "";

        if(preconds.length !== 0) {
            rconds = bodyindent + preconds.map((pc) => `$Runtime.raiseUserAssertIf(!${this.emitExpression(pc.exp)}, "Failed precondition ${fname} -- ${pc.exp.expstr}");`).join("\n" + bodyindent) + "\n" + bodyindent;
        }

        if(postconds.length === 0) {
            return `{\n${rconds}${body.map((stmt) => this.emitStatement(stmt, bodyindent)).join("\n" + bodyindent)}\n${indent}}`;
        }
        else {
            const wbodyindent = bodyindent + "    ";
            const bstr = `{\n${body.map((stmt) => this.emitStatement(stmt, wbodyindent)).join("\n" + wbodyindent)}\n${bodyindent}}`;

            const econds = bodyindent + postconds.map((pc) => `$Runtime.raiseUserAssertIf(!${this.emitExpression(pc.exp)}, "Failed postcondition ${fname} -- ${pc.exp.expstr}");`).join("\n" + bodyindent);

            return `{\n${rconds}const $$return" = (() => ${bstr})();\n${bodyindent}$return = ${extractres ? "$$return[1]" : "$$return"};\n${econds}\n${bodyindent}return $$return;\n${indent}}`;
        }
    }
}

export {
    BodyEmitter
};
