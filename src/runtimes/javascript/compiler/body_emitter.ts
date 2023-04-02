import { extractLiteralASCIIStringValue, extractLiteralStringValue } from "../../../frontend/build_decls";
import { TIRASCIIStringOfEntityType, TIRAssembly, TIRConceptType, TIREnumEntityType, TIRListEntityType, TIRMapEntityType, TIRMapEntryEntityType, TIRMemberFieldDecl, TIRMemberMethodDecl, TIRNamespaceFunctionDecl, TIRObjectEntityType, TIROOType, TIRPathEntityType, TIRPathFragmentEntityType, TIRPathGlobEntityType, TIRPathValidatorEntityType, TIRPostConditionDecl, TIRPreConditionDecl, TIRPrimitiveInternalEntityType, TIRQueueEntityType, TIRRecordType, TIRSetEntityType, TIRStackEntityType, TIRStaticFunctionDecl, TIRStringOfEntityType, TIRTaskType, TIRType, TIRTypedeclEntityType, TIRTypeKey, TIRUnionType, TIRValidatorEntityType } from "../../../frontend/tree_ir/tir_assembly";
import { TIRAbortStatement, TIRAccessCapturedVariableExpression, TIRAccessConstMemberFieldExpression, TIRAccessEnvValueExpression, TIRAccessNamespaceConstantExpression, TIRAccessScratchIndexExpression, TIRAccessScratchSingleValueExpression, TIRAccessVariableExpression, TIRAsEqualToLiteralExpression, TIRAsErrSpecialExpression, TIRAsNoneSpecialExpression, TIRAsNotEqualToLiteralExpression, TIRAsNothingSpecialExpression, TIRAsNotSubTypeExpression, TIRAsNotTypeExpression, TIRAsOkSpecialExpression, TIRAssertCheckStatement, TIRAsSomeSpecialExpression, TIRAsSomethingSpecialExpression, TIRAsSubTypeExpression, TIRAsTypeExpression, TIRBinAddExpression, TIRBinDivExpression, TIRBinKeyEqBothUniqueExpression, TIRBinKeyEqGeneralExpression, TIRBinKeyEqOneUniqueExpression, TIRBinKeyGeneralLessExpression, TIRBinKeyNeqBothUniqueExpression, TIRBinKeyNeqGeneralExpression, TIRBinKeyNeqOneUniqueExpression, TIRBinKeyUniqueLessExpression, TIRBinLogicAndExpression, TIRBinLogicImpliesExpression, TIRBinLogicOrExpression, TIRBinMultExpression, TIRBinSubExpression, TIRCallMemberActionExpression, TIRCallMemberFunctionDynamicExpression, TIRCallMemberFunctionExpression, TIRCallMemberFunctionSelfRefExpression, TIRCallMemberFunctionTaskExpression, TIRCallMemberFunctionTaskSelfRefExpression, TIRCallNamespaceFunctionExpression, TIRCallNamespaceOperatorExpression, TIRCallStatementWAction, TIRCallStatementWRef, TIRCallStatementWTaskRef, TIRCallStaticFunctionExpression, TIRCodePackInvokeExpression, TIRCoerceSafeExpression, TIRConstructorListExpression, TIRConstructorMapExpression, TIRConstructorPrimaryCheckExpression, TIRConstructorPrimaryDirectExpression, TIRConstructorRecordExpression, TIRConstructorTupleExpression, TIRCreateCodePackExpression, TIRDebugStatement, TIREnvironmentFreshStatement, TIREnvironmentSetStatement, TIREnvironmentSetStatementBracket, TIRExpression, TIRExpressionTag, TIRExtractExpression, TIRIfExpression, TIRIfStatement, TIRInjectExpression, TIRIsEqualToLiteralExpression, TIRIsErrSpecialExpression, TIRIsNoneSpecialExpression, TIRIsNotEqualToLiteralExpression, TIRIsNothingSpecialExpression, TIRIsNotSubTypeExpression, TIRIsNotTypeExpression, TIRIsOkSpecialExpression, TIRIsSomeSpecialExpression, TIRIsSomethingSpecialExpression, TIRIsSubTypeExpression, TIRIsTypeExpression, TIRLiteralASCIIStringExpression, TIRLiteralASCIITemplateStringExpression, TIRLiteralASCIITypedStringExpression, TIRLiteralBoolExpression, TIRLiteralFloatPointExpression, TIRLiteralIntegralExpression, TIRLiteralNoneExpression, TIRLiteralNothingExpression, TIRLiteralRationalExpression, TIRLiteralRegexExpression, TIRLiteralStringExpression, TIRLiteralTemplateStringExpression, TIRLiteralTypedPrimitiveConstructorExpression, TIRLiteralTypedPrimitiveDirectExpression, TIRLiteralTypedStringExpression, TIRLoadFieldExpression, TIRLoadFieldVirtualExpression, TIRLoadIndexExpression, TIRLoadPropertyExpression, TIRLoggerEmitConditionalStatement, TIRLoggerEmitStatement, TIRLoggerSetPrefixStatement, TIRLogicActionAndExpression, TIRLogicActionOrExpression, TIRMapEntryConstructorExpression, TIRMatchExpression, TIRMatchStatement, TIRNopStatement, TIRNumericEqExpression, TIRNumericGreaterEqExpression, TIRNumericGreaterExpression, TIRNumericLessEqExpression, TIRNumericLessExpression, TIRNumericNeqExpression, TIRPrefixNegateExpression, TIRPrefixNotExpression, TIRResultErrConstructorExpression, TIRResultOkConstructorExpression, TIRReturnStatement, TIRReturnStatementWAction, TIRReturnStatementWRef, TIRReturnStatementWTaskRef, TIRScopedBlockStatement, TIRScratchSCStatement, TIRSomethingConstructorExpression, TIRStatement, TIRStatementTag, TIRStoreToScratch, TIRSwitchExpression, TIRSwitchStatement, TIRTaskAllStatement, TIRTaskDashStatement, TIRTaskGetIDExpression, TIRTaskMultiStatement, TIRTaskRaceStatement, TIRTaskRefAssignFromScratch, TIRTaskRunStatement, TIRTaskSelfControlExpression, TIRTaskSelfFieldExpression, TIRTaskSetSelfFieldStatement, TIRTypedeclConstructorExpression, TIRTypedeclDirectExpression, TIRUnscopedBlockStatement, TIRVarAssignStatement, TIRVarDeclareAndAssignStatement, TIRVarDeclareStatement, TIRVariableRetypeStatement, TIRVariableSCRetypeStatement, TIRVarRefAssignFromScratch } from "../../../frontend/tree_ir/tir_body";

function assert(cond: boolean, msg?: string) {
    if(!cond) {
        throw new Error((msg || "error")  + " -- body_emitter.ts");
    }
} 

function NOT_IMPLEMENTED_EXPRESSION(tag: string): string {
    assert(false, `NOT IMEPLEMENTED -- ${tag}`);
    return "[NOT IMPLEMENTED]";
}

function NOT_IMPLEMENTED_STATEMENT(tag: string): string {
    assert(false, `NOT IMEPLEMENTED -- ${tag}`);
    return "[NOT IMPLEMENTED]";
}

class BodyEmitter {
    private readonly m_assembly: TIRAssembly;

    private readonly m_file: string;
    private readonly m_ns: string;
    private m_typeResolveMemo: Map<TIRTypeKey, string> = new Map<TIRTypeKey, string>();

    private m_activeTask: TIRTypeKey = "[NOT SET]";

    private m_hasScratch = false;
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

        let taccess: string = "[INVALID]";
        if(ttype instanceof TIRObjectEntityType) {
            if(ttype.binds.size === 0) {
                taccess = samens ? `BSQ${ttype.tname.name}` : `${ttype.tname.ns}.BSQ${ttype.tname.name}`;
            }
            else {
                if (samens) {
                    taccess = `$Types["${ttype.tkey}"]`;
                }
                else {
                    taccess = `${ttype.tname.ns}.$Types["${ttype.tkey}"]`;
                }
            }
        }
        else if(ttype instanceof TIREnumEntityType) {
            taccess = samens ? `BSQ${ttype.tname.name}` : `${ttype.tname.ns}.BSQ${ttype.tname.name}`;
        }
        else if(ttype instanceof TIRTypedeclEntityType) {
            taccess = samens ? `BSQ${ttype.tname.name}` : `${ttype.tname.ns}.BSQ${ttype.tname.name}`;
        }
        else if(ttype instanceof TIRPrimitiveInternalEntityType) {
            taccess =  samens ? `BSQ${ttype.tname.name}` : `${ttype.tname.ns}.BSQ${ttype.tname.name}`;
        }
        else if (ttype instanceof TIRValidatorEntityType) {
            if (samens) {
                taccess = `$Types["${ttype.tkey}"]`;
            }
            else {
                taccess = `${ttype.tname.ns}.$Types["${ttype.tkey}"]`;
            }
        }
        else if ((ttype instanceof TIRStringOfEntityType) || (ttype instanceof TIRASCIIStringOfEntityType)) {
            if (samens) {
                taccess = `$Types["${ttype.tkey}"]`;
            }
            else {
                taccess = `${ttype.tname.ns}.$Types["${ttype.tkey}"]`;
            }
        }
        else if (ttype instanceof TIRPathValidatorEntityType) {
            if (samens) {
                taccess = `$Types["${ttype.tkey}"]`;
            }
            else {
                taccess = `${ttype.tname.ns}.$Types["${ttype.tkey}"]`;

            }
        }
        else if ((ttype instanceof TIRPathEntityType) || (ttype instanceof TIRPathFragmentEntityType) || (ttype instanceof TIRPathGlobEntityType)) {
            if (samens) {
                taccess = `$Types["${ttype.tkey}"]`;
            }
            else {
                taccess = `${ttype.tname.ns}.$Types["${ttype.tkey}"]`;
            }
        }
        else if(ttype instanceof TIRMapEntryEntityType) {
            taccess = `Core.$Types["${ttype.tkey}"]`;
        }
        else if((ttype instanceof TIRListEntityType) || (ttype instanceof TIRStackEntityType) || (ttype instanceof TIRQueueEntityType) ||  (ttype instanceof TIRSetEntityType) || (ttype instanceof TIRMapEntityType)) {
            taccess = `Core.$Types["${ttype.tkey}"]`;
        }
        else if(ttype instanceof TIRTaskType) {
            taccess = samens ? `BSQ${ttype.tname.name}` : `${ttype.tname.ns}.BSQ${ttype.tname.name}`;
        }
        else if(ttype instanceof TIRConceptType) {
            if(ttype.binds.size === 0) {
                taccess = samens ? `BSQ${ttype.tname.name}` : `${ttype.tname.ns}.BSQ${ttype.tname.name}`;
            }
            else {
                if (samens) {
                    taccess = `$Types["${ttype.tkey}"]`;
                }
                else {
                    taccess = `${ttype.tname.ns}.$Types["${ttype.tkey}"]`;
                }
            }
        }
        else {
            assert(false, "Unknown type in resolveTypeNameAccess");
        }

        this.m_typeResolveMemo.set(tt, taccess);
        return taccess;
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
        return `new $Runtime.Fraction("${exp.value.slice(0, exp.value.length - 1)}")`;
    }

    private emitLiteralFloatPointExpression(exp: TIRLiteralFloatPointExpression): string {
        if(exp.etype === "Float") {
            return exp.value.slice(0, exp.value.length - 1);
        }
        else {
            assert(exp.etype === "Decimal", "Unknown type TIRLiteralFloatPointExpression");
            return `new $Runtime.Decimal(${exp.value.slice(0, exp.value.length - 1)})`;
        }
    }

    private emitLiteralRegexExpression(exp: TIRLiteralRegexExpression): string {
        return exp.value.regexstr;
    }

    private emitLiteralStringExpression(exp: TIRLiteralStringExpression): string {
        return extractLiteralStringValue(exp.value, false);
    }

    private emitLiteralASCIIStringExpression(exp: TIRLiteralASCIIStringExpression): string {
        return extractLiteralASCIIStringValue(exp.value, false);
    }
    
    private emitLiteralTypedStringExpression(exp: TIRLiteralTypedStringExpression): string {
        return extractLiteralStringValue(exp.value, false);
    }

    private emitLiteralASCIITypedStringExpression(exp: TIRLiteralASCIITypedStringExpression): string {
        return extractLiteralASCIIStringValue(exp.value, false);
    }
    
    private emitLiteralTemplateStringExpression(exp: TIRLiteralTemplateStringExpression): string {
        return extractLiteralStringValue(exp.value, false);
    }

    private emitLiteralASCIITemplateStringExpression(exp: TIRLiteralASCIITemplateStringExpression): string {
        return extractLiteralASCIIStringValue(exp.value, false);
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
        if(exp.ns === this.m_ns) {
            return `${exp.cname}()`;
        }
        else {
            return `${exp.ns}.${exp.cname}()`;
        }
    }

    private emitAccessConstMemberFieldExpression(exp: TIRAccessConstMemberFieldExpression): string {
        const ttype = this.m_assembly.typeMap.get(exp.tkey) as TIRType;
        if(ttype instanceof TIREnumEntityType) {
            return `${this.resolveTypeMemberAccess(exp.tkey)}.${exp.cname}`;
        }
        else {
            return `${this.resolveTypeMemberAccess(exp.tkey)}.${exp.cname}()`;
        }
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

    private emitAccessCapturedVariableExpression(exp: TIRAccessCapturedVariableExpression): string {
        return `$CodePack.${exp.name}`;
    }

    private emitAccessScratchSingleValueExpression(exp: TIRAccessScratchSingleValueExpression): string {
        this.m_hasScratch = true;
        return `$$scratch[${exp.sidx}]`;
    }

    private emitAccessScratchIndexExpression(exp: TIRAccessScratchIndexExpression): string {
        this.m_hasScratch = true;
        return `$$scratch[${exp.sidx}][${exp.index}]`
    }

    private emitLoadIndexExpression(exp: TIRLoadIndexExpression): string {
        return `${this.emitExpression(exp.exp)}[${exp.index}]`;
    }

    private emitLoadPropertyExpression(exp: TIRLoadPropertyExpression): string {
        return `${this.emitExpression(exp.exp)}.${exp.property}`;
    }

    private emitLoadFieldExpression(exp: TIRLoadFieldExpression): string {
        const fname = (this.m_assembly.fieldMap.get(exp.fieldkey) as TIRMemberFieldDecl).name;
        return `${this.emitExpression(exp.exp)}.${fname}`;
    }

    private emitLoadFieldVirtualExpression(exp: TIRLoadFieldVirtualExpression): string {
        const fname = (this.m_assembly.fieldMap.get(exp.fieldkey) as TIRMemberFieldDecl).name;
        const bexp = (this.typeEncodedAsUnion(exp.exp.etype) ? `${this.emitExpression(exp.exp)}.value` : this.emitExpression(exp.exp));

        return `${bexp}.${fname}`;
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
        const entries = exp.args.map((arg, ii) => `${tt.entries[ii].pname}: ${this.emitExpression(arg, true)}`);
        return `{${entries.join(", ")}}`;
    }

    private emitConstructorListExpression(exp: TIRConstructorListExpression): string {
        return `$CoreLibs.$ListOps.create(${exp.args.map((arg) => this.emitExpression(arg, true)).join(", ")})`;
    }

    private emitConstructorMapExpression(exp: TIRConstructorMapExpression): string {
        return `$CoreLibs.$MapOps.create("${exp.etype}", ${exp.args.map((arg) => this.emitExpression(arg, true)).join(", ")})`;
    }

    private emitCodePackInvokeExpression(exp: TIRCodePackInvokeExpression): string {
        return `($Runtime.lambdas.get("${exp.cpack.invk}"))(${[...exp.args.map((arg) => this.emitExpression(arg, true))].join(", ")})`;
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
        const invks = this.m_assembly.getNamespace(exp.ns).functions.get(exp.fname) as TIRNamespaceFunctionDecl[];
        const invk = invks.find((ii) => ii.ikey === exp.fkey) as TIRNamespaceFunctionDecl;

        const ins = (invk.ns !== this.m_ns) ? `${invk.ns}.` : "";

        if(invk.invoke.tbinds.size === 0 && invk.invoke.pcodes.size === 0) {
            return `${ins}${invk.name}(${exp.args.map((arg) => this.emitExpression(arg)).join(", ")})`;
        }
        else {
            return `${ins}$Functions["${invk.ikey}"](${exp.args.map((arg) => this.emitExpression(arg)).join(", ")})`;
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
        if((invk as TIRStaticFunctionDecl).invoke.tbinds.size === 0 && (invk as TIRStaticFunctionDecl).invoke.pcodes.size === 0) {
            return `${accessterm}.${(invk as TIRStaticFunctionDecl).name}(${exp.args.map((arg) => this.emitExpression(arg)).join(", ")})`;
        }
        else {
            return `${accessterm}.$Functions["${(invk as TIRStaticFunctionDecl).ikey}"](${exp.args.map((arg) => this.emitExpression(arg)).join(", ")})`;
        }
    }

    private emitLogicActionAndExpression(exp: TIRLogicActionAndExpression, toplevel: boolean): string {
       const lexp = "[" + exp.args.map((arg) => this.emitExpression(arg)).join(", ") + "].every((arg) => arg)";
       return toplevel ? lexp : ("(" + lexp + ")");
    }

    private emitLogicActionOrExpression(exp: TIRLogicActionOrExpression, toplevel: boolean): string {
        const lexp = "[" + exp.args.map((arg) => this.emitExpression(arg)).join(", ") + "].some((arg) => arg)";
        return toplevel ? lexp : ("(" + lexp + ")");
    }

    private emitPrefixNotOpExpression(exp: TIRPrefixNotExpression, toplevel: boolean): string {
        const nexp = `!${this.emitExpression(exp.exp)}`;
        return toplevel ? nexp : ("(" + nexp + ")");
    }

    private processArithOpResult(restype: TIRTypeKey, dataop: string): string {
        const ttype = this.m_assembly.typeMap.get(restype);
        if(ttype instanceof TIRTypedeclEntityType) {
            if(ttype.consinvariantsall.length === 0) {
                return dataop;
            }
            else {
                return `${this.resolveTypeMemberAccess(restype)}.$constructorWithChecks_basetype(${dataop})`;
            }
        }
        else {
            return dataop;
        }
    }

    private emitPrefixNegateOpExpression(exp: TIRPrefixNegateExpression, toplevel: boolean): string {
        let nexp = "[NOT SET]";
        if(exp.etype === "Rational") {
            nexp = `${this.emitExpression(exp.exp)}.neg()`;
        }
        else if(exp.etype === "Decimal") {
            nexp = `${this.emitExpression(exp.exp)}.neg()`;
        }
        else {
            nexp = `-${this.emitExpression(exp.exp)}`;
        }

        return this.processArithOpResult(exp.etype, toplevel ? nexp : ("(" + nexp + ")"));
    }

    private emitBinAddExpression(exp: TIRBinAddExpression, toplevel: boolean): string {
        let bexp = "[NOT SET]";
        if(exp.optype === "Rational") {
            bexp = `${this.emitExpression(exp.lhs)}.add(${this.emitExpression(exp.rhs, true)})`;
        }
        else if(exp.optype === "Decimal") {
            bexp = `${this.emitExpression(exp.lhs)}.plus(${this.emitExpression(exp.rhs, true)})`;
        }
        else {
            bexp = `${this.emitExpression(exp.lhs)} + ${this.emitExpression(exp.rhs)}`;
        }

        let dataop = "[NOT SET]"
        if(exp.optype === "Nat") {
            dataop = `$Runtime.safeMath(${bexp}, 0n, $Runtime.FIXED_NUMBER_MAX)`;
        }
        else if(exp.optype === "Int") {
            dataop = `$Runtime.safeMath(${bexp}, $Runtime.FIXED_NUMBER_MIN, $Runtime.FIXED_NUMBER_MAX)`;
        }
        else {
            dataop = toplevel ? bexp : ("(" + bexp + ")");
        }

        return this.processArithOpResult(exp.etype, dataop);
    }

    private emitBinSubExpression(exp: TIRBinSubExpression, toplevel: boolean): string {
        let bexp = "[NOT SET]";
        if(exp.optype === "Rational") {
            bexp = `${this.emitExpression(exp.lhs)}.sub(${this.emitExpression(exp.rhs, true)})`;
        }
        else if(exp.optype === "Decimal") {
            bexp = `${this.emitExpression(exp.lhs)}.minus(${this.emitExpression(exp.rhs, true)})`;
        }
        else {
            bexp = `${this.emitExpression(exp.lhs)} - ${this.emitExpression(exp.rhs)}`;
        }
        
        let dataop = "[NOT SET]"
        if(exp.optype === "Nat") {
            dataop = `$Runtime.safeMath(${bexp}, 0n, $Runtime.FIXED_NUMBER_MAX)`;
        }
        else if(exp.optype === "Int") {
            dataop = `$Runtime.safeMath(${bexp}, $Runtime.FIXED_NUMBER_MIN, $Runtime.FIXED_NUMBER_MAX)`;
        }
        else if(exp.optype === "BigNat") {
            dataop = `$Runtime.safeMathUnderflow(${bexp}, 0n)`;
        }
        else {
            dataop = toplevel ? bexp : ("(" + bexp + ")");
        }

        return this.processArithOpResult(exp.etype, dataop);
    }

    private emitBinMultExpression(exp: TIRBinMultExpression, toplevel: boolean): string {
        let bexp = "[NOT SET]";
        if(exp.optype === "Rational") {
            bexp = `${this.emitExpression(exp.lhs)}.mul(${this.emitExpression(exp.rhs, true)})`;
        }
        else if(exp.optype === "Decimal") {
            bexp = `${this.emitExpression(exp.lhs)}.times(${this.emitExpression(exp.rhs, true)})`;
        }
        else {
            bexp = `${this.emitExpression(exp.lhs)} * ${this.emitExpression(exp.rhs)}`;
        }
        
        let dataop = "[NOT SET]"
        if(exp.optype === "Nat") {
            dataop = `$Runtime.safeMath(${bexp}, 0n, $Runtime.FIXED_NUMBER_MAX)`;
        }
        else if(exp.optype === "Int") {
            dataop = `$Runtime.safeMath(${bexp}, $Runtime.FIXED_NUMBER_MIN, $Runtime.FIXED_NUMBER_MAX)`;
        }
        else {
            dataop = toplevel ? bexp : ("(" + bexp + ")");
        }

        return this.processArithOpResult(exp.etype, dataop);
    }

    private emitBinDivExpression(exp: TIRBinDivExpression, toplevel: boolean): string {
        const lexp = this.emitExpression(exp.lhs);
        const rexp = this.emitExpression(exp.rhs);

        let dataop = "[NOT SET]"
        if(exp.optype === "Nat") {
            dataop = `$Runtime.safeMathDiv((a, b) => a / b, (b) => b === 0n, ${lexp}, ${rexp})`;
        }
        else if(exp.optype === "Int") {
            dataop = `$Runtime.safeMathDiv((a, b) => a / b, (b) => b === 0n, ${lexp}, ${rexp})`;
        }
        else if(exp.optype === "BigNat") {
            dataop = `$Runtime.safeMathDiv((a, b) => a / b, (b) => b === 0n, ${lexp}, ${rexp})`;
        }
        else if(exp.optype === "BigInt") {
            dataop = `$Runtime.safeMathDiv((a, b) => a / b, (b) => b === 0n, ${lexp}, ${rexp})`;
        }
        else if(exp.optype === "Rational") {
            dataop = `$Runtime.safeMathDiv((a, b) => a.div(b), (b) => b.equals(new $Runtime.Fraction(0.0)), ${lexp}, ${rexp})`;
        }
        else if(exp.optype === "Decimal") {
            dataop = `$Runtime.safeMathDiv((a, b) => a.dividedBy(b), (b) => b.equals(new $Runtime.Decimal(0.0)), ${lexp}, ${rexp})`;
        }
        else {
            dataop = `$Runtime.safeMathDiv((a, b) => a / b, (b) => b === 0.0, ${lexp}, ${rexp})`;
        }

        return this.processArithOpResult(exp.etype, dataop);
    }

    private emitBinKeyEqBothUniqueExpression(exp: TIRBinKeyEqBothUniqueExpression): string {
        return `($CoreLibs.$KeyEqualOps.get("${exp.optype}"))(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)})`;
    }

    private emitBinKeyEqOneUniqueExpression(exp: TIRBinKeyEqOneUniqueExpression): string {
        return `$CoreLibs.$KeyEqualMixed(${this.emitExpression(exp.uarg, true)}, ${this.emitExpression(exp.garg, true)}, "${exp.oftype}")`;
    }
    
    private emitBinKeyEqGeneralExpression(exp: TIRBinKeyEqGeneralExpression): string {
        return `$CoreLibs.$KeyEqualGeneral(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)})`;
    }

    private emitBinKeyNeqBothUniqueExpression(exp: TIRBinKeyNeqBothUniqueExpression, toplevel: boolean): string {
        const rr = `!($CoreLibs.$KeyEqualOps.get("${exp.optype}"))(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)})`;
        return toplevel ? rr : "(" + rr + ")";
    }

    private emitBinKeyNeqOneUniqueExpression(exp: TIRBinKeyNeqOneUniqueExpression, toplevel: boolean): string {
        const rr = `!$CoreLibs.$KeyEqualMixed(${this.emitExpression(exp.uarg, true)}, ${this.emitExpression(exp.garg, true)}, "${exp.oftype}")`;
        return toplevel ? rr : "(" + rr + ")";
    }
    
    private emitBinKeyNeqGeneralExpression(exp: TIRBinKeyNeqGeneralExpression, toplevel: boolean): string {
        const rr = `!$CoreLibs.$KeyEqualGeneral(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)})`;
        return toplevel ? rr : "(" + rr + ")";
    }

    private emitBinKeyUniqueLessExpression(exp: TIRBinKeyUniqueLessExpression): string {
        return `($CoreLibs.$KeyLessOps.get("${exp.optype}"))(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)})`;
    }

    private emitBinKeyGeneralLessExpression(exp: TIRBinKeyGeneralLessExpression): string {
        return `$CoreLibs.$KeyLessGeneral(${this.emitExpression(exp.lhs, true)}, ${this.emitExpression(exp.rhs, true)})`;
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
            cmp = `${lexp}.equals(${rexp})`;
        }
        else if(exp.optype === "Float") {
            cmp = `${lexp} === ${rexp}`;
        }
        else {
            cmp = `${lexp}.equals(${rexp})`;
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
            cmp = `!(${lexp}.equals(${rexp}))`;
        }
        else if(exp.optype === "Float") {
            cmp = `${lexp} !== ${rexp}`;
        }
        else {
            cmp = `!(${lexp}.equals(${rexp}))`;
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
            cmp = `(${lexp}.compare(${rexp}) < 0)`;
        }
        else if(exp.optype === "Float") {
            cmp = `${lexp} < ${rexp}`;
        }
        else {
            cmp = `${lexp}.lessThan(${rexp})`;
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
            cmp = `(${lexp}.compare(${rexp}) <= 0)`;
        }
        else if(exp.optype === "Float") {
            cmp = `${lexp} <= ${rexp}`;
        }
        else {
            cmp = `${lexp}.lessThanOrEqualTo(${rexp})`;
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
            cmp = `(${lexp}.compare(${rexp}) > 0)`;
        }
        else if(exp.optype === "Float") {
            cmp = `${lexp} > ${rexp}`;
        }
        else {
            cmp = `${lexp}.greaterThan(${rexp})`;
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
            cmp = `(${lexp}.compare(${rexp}) >= 0)`;
        }
        else if(exp.optype === "Float") {
            cmp = `${lexp} >= ${rexp}`;
        }
        else {
            cmp = `${lexp}.greaterThanOrEqualTo(${rexp})`;
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
        let rstr = "";
        if(exp.ifentry.binderinfo === undefined) {
            rstr = `${this.emitExpression(exp.ifentry.test)} ? ${this.emitExpression(exp.ifentry.value)} : `;
        }
        else {
            this.m_hasScratch = true;
            const tstr = `($Runtime.setScratchValue($$scratch, ${exp.ifentry.binderinfo[1]}, ${this.emitExpression(exp.ifentry.binderinfo[0])}) || ${this.emitExpression(exp.ifentry.test)})`;
            const texp = `((${exp.ifentry.binderinfo[3]}) => ${this.emitExpression(exp.ifentry.value)})(${this.emitExpression(exp.ifentry.binderinfo[2])})`;
            rstr = `${tstr} ? ${texp} : `;
        } 

        for(let i = 0; i < exp.elifentries.length; ++i){
            const eii = exp.elifentries[i];

            if(eii.binderinfo === undefined) {
                rstr += `${this.emitExpression(eii.test)} ? ${this.emitExpression(eii.value)} : `
            }
            else {
                this.m_hasScratch = true;
                const tstr = `($Runtime.setScratchValue($$scratch, ${eii.binderinfo[1]}, ${this.emitExpression(eii.binderinfo[0])}) || ${this.emitExpression(eii.test)})`;
                const texp = `((${eii.binderinfo[3]}) => ${this.emitExpression(eii.value)})(${this.emitExpression(eii.binderinfo[2])})`;
                rstr += `${tstr} ? ${texp} : `;
            }
        }

        if(exp.elseentry.binderinfo === undefined) {
            rstr += this.emitExpression(exp.elseentry.value);
        }
        else {
            this.m_hasScratch = true;
            const tstr = `$Runtime.setScratchValue($$scratch, ${exp.elseentry.binderinfo[1]}, ${this.emitExpression(exp.elseentry.binderinfo[0])})`;
            const texp = `((${exp.elseentry.binderinfo[3]}) => ${this.emitExpression(exp.elseentry.value)})(${this.emitExpression(exp.elseentry.binderinfo[2])})`;
            rstr += `(${tstr} || ${texp})`;
        }

        return toplevel ? rstr : "(" + rstr + ")";
    }

    private emitSwitchExpression(exp: TIRSwitchExpression, toplevel: boolean): string {
        this.m_hasScratch = true;
        let sstr = `$Runtime.setScratchValue($$scratch, ${exp.scratchidx}, ${this.emitExpression(exp.exp, true)}) || `;

        if(exp.clauses[0].binderinfo === undefined) {
            sstr += `${this.emitExpression(exp.clauses[0].match, false)} ? ${this.emitExpression(exp.clauses[0].value, false)} : `;
        }
        else {
            sstr += `${this.emitExpression(exp.clauses[0].match, false)} ? ((${exp.clauses[0].binderinfo[1]}) => ${this.emitExpression(exp.clauses[0].value, true)})(${this.emitExpression(exp.clauses[0].binderinfo[0], true)}) : `;
        }

        for(let i = 1; i < exp.clauses.length; ++i) {
            if(exp.clauses[i].binderinfo === undefined) {
                sstr += `${this.emitExpression(exp.clauses[i].match, false)} ? ${this.emitExpression(exp.clauses[i].value, false)} : `;
            }
            else {
                const binfo = exp.clauses[i].binderinfo as [TIRExpression, string];
                sstr += `${this.emitExpression(exp.clauses[i].match, false)} ? ((${binfo[1]}) => ${this.emitExpression(exp.clauses[i].value, true)})(${this.emitExpression(binfo[0], true)}) : `;
            }
        }

        if(exp.edefault !== undefined) {
            if(exp.edefault.binderinfo === undefined) {
                sstr += `${this.emitExpression(exp.edefault.value, false)}\n`;
            }
            else {
                sstr += `((${exp.edefault.binderinfo[1]}) => ${this.emitExpression(exp.edefault.value, true)})(${this.emitExpression(exp.edefault.binderinfo[0], true)})`;
            }
        }
        else {
            //we just ignore exp.isexhaustive -- maybe want to be more optimized in the future
            sstr += `$Runtime.raiseRuntimeError("Non-exhaustive switch statement" + " -- ${this.m_file} @ line ${exp.sinfo.line}")`;
        }

        return toplevel ? sstr : ("(" + sstr + ")");
    }
    
    private emitMatchExpression(exp: TIRMatchExpression, toplevel: boolean): string {
        this.m_hasScratch = true;
        let sstr = `$Runtime.setScratchValue($$scratch, ${exp.scratchidx}, ${this.emitExpression(exp.exp, true)}) || `;

        if(exp.clauses[0].binderinfo === undefined) {
            sstr += `${this.emitExpression(exp.clauses[0].match, false)} ? ${this.emitExpression(exp.clauses[0].value, false)} : `;
        }
        else {
            sstr += `${this.emitExpression(exp.clauses[0].match, false)} ? ((${exp.clauses[0].binderinfo[1]}) => ${this.emitExpression(exp.clauses[0].value, true)})(${this.emitExpression(exp.clauses[0].binderinfo[0], true)}) : `;
        }

        for(let i = 1; i < exp.clauses.length; ++i) {
            if(exp.clauses[i].binderinfo === undefined) {
                sstr += `${this.emitExpression(exp.clauses[i].match, false)} ? ${this.emitExpression(exp.clauses[i].value, false)} : `;
            }
            else {
                const binfo = exp.clauses[i].binderinfo as [TIRExpression, string];
                sstr += `${this.emitExpression(exp.clauses[i].match, false)} ? ((${binfo[1]}) => ${this.emitExpression(exp.clauses[i].value, true)})(${this.emitExpression(binfo[0], true)}) : `;
            }
        }

        if(exp.edefault !== undefined) {
            if(exp.edefault.binderinfo === undefined) {
                sstr += `${this.emitExpression(exp.edefault.value, false)}\n`;
            }
            else {
                sstr += `((${exp.edefault.binderinfo[1]}) => ${this.emitExpression(exp.edefault.value, true)})(${this.emitExpression(exp.edefault.binderinfo[0], true)})`;
            }
        }
        else {
            //we just ignore exp.isexhaustive -- maybe want to be more optimized in the future
            sstr += `$Runtime.raiseRuntimeError("Non-exhaustive match statement" + " -- ${this.m_file} @ line ${exp.sinfo.line}")`;
        }

        return toplevel ? sstr : ("(" + sstr + ")");
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
            const bval = `$Runtime.UnionValue.create("${exp.fromtype}", ${this.emitExpression(exp.exp)})`;
            return toplevel ? bval : "(" + bval + ")";
        }
        else {
            const bval = `${this.emitExpression(exp.exp)}.value`;
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
        const capturepcdirect = exp.capturepackdirect.map((pcc) => `${pcc}: ${pcc}`);
        const capturepcindirect = exp.capturepackindirect.map((pcc) => `${pcc}: $CodePack.${pcc}`);
        const capturevvdirect = exp.capturedirect.map((pcc) => `${pcc}: ${pcc === "this" ? "$_this" : pcc}`);
        const capturevvindirect = exp.captureindirect.map((pcc) => `${pcc}: $CodePack.${pcc}`);

        return `{${[...capturevvdirect, ...capturevvindirect, ...capturepcdirect, ...capturepcindirect].join(", ")}}`;
    }

    private emitIsNoneSpecialExpression(exp: TIRIsNoneSpecialExpression, toplevel: boolean): string {
       assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");

       const bval = `${this.emitExpression(exp.exp)}.tkey === "None"`;
       return toplevel ? bval : "(" + bval + ")";
    }

    private emitIsSomeSpecialExpression(exp: TIRIsSomeSpecialExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");

        const bval = `${this.emitExpression(exp.exp)}.tkey !== "None"`;
        return toplevel ? bval : "(" + bval + ")";
    }

    private emitIsNothingSpecialExpression(exp: TIRIsNothingSpecialExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");

        const bval = `${this.emitExpression(exp.exp)}.tkey === "Nothing"`;
        return toplevel ? bval : "(" + bval + ")";
    }

    private emitIsSomethingSpecialExpression(exp: TIRIsSomethingSpecialExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");

        const bval = `${this.emitExpression(exp.exp)}.tkey !== "Nothing"`;
        return toplevel ? bval : "(" + bval + ")";
    }

    private emitIsOkSpecialExpression(exp: TIRIsOkSpecialExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");

        const bval = `${this.emitExpression(exp.exp)}.tkey === "${exp.oktype}"`;
        return toplevel ? bval : "(" + bval + ")";
    }

    private emitIsErrSpecialExpression(exp: TIRIsErrSpecialExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");

        const bval = `${this.emitExpression(exp.exp)}.tkey === "${exp.errtype}"`;
        return toplevel ? bval : "(" + bval + ")";
    }

    private emitIsEqualToLiteralExpression(exp: TIRIsEqualToLiteralExpression, toplevel: boolean): string {
        if(this.typeEncodedAsUnion(exp.exp.etype)) {
            const rr = `$CoreLibs.$KeyEqualMixed(${this.emitExpression(exp.literal.exp, true)}, ${this.emitExpression(exp.exp, true)}, "${exp.literal.exp.etype}")`;
            return toplevel ? rr : "(" + rr + ")";
        }
        else {
            const rr = `($CoreLibs.$KeyEqualOps.get("${exp.literal.exp.etype}"))(${this.emitExpression(exp.literal.exp, true)}, ${this.emitExpression(exp.exp, true)})`;
            return toplevel ? rr : "(" + rr + ")";
        }
    }

    private emitIsNotEqualToLiteralExpression(exp: TIRIsNotEqualToLiteralExpression, toplevel: boolean): string {
        if(this.typeEncodedAsUnion(exp.exp.etype)) {
            const rr = `!$CoreLibs.$KeyEqualMixed(${this.emitExpression(exp.literal.exp, true)}, ${this.emitExpression(exp.exp, true)}, "${exp.literal.exp.etype}")`;
            return toplevel ? rr : "(" + rr + ")";
        }
        else {
            const rr = `!($CoreLibs.$KeyEqualOps.get("${exp.literal.exp.etype}"))(${this.emitExpression(exp.literal.exp, true)}, ${this.emitExpression(exp.exp, true)})`;
            return toplevel ? rr : "(" + rr + ")";
        }
    }

    private emitIsTypeExpression(exp: TIRIsTypeExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");
        assert(!this.typeEncodedAsUnion(exp.ttype), "this should be a subtype then");

        const bval = `${this.emitExpression(exp.exp)}.tkey === "${exp.ttype}"`;
        return toplevel ? bval : "(" + bval + ")";
    }

    private emitIsNotTypeExpression(exp: TIRIsNotTypeExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");
        assert(!this.typeEncodedAsUnion(exp.ttype), "this should be a subtype then");

        const bval = `${this.emitExpression(exp.exp)}.tkey !== "${exp.ttype}"`;
        return toplevel ? bval : "(" + bval + ")";
    }

    private emitIsSubTypeExpression(exp: TIRIsSubTypeExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");
        assert(this.typeEncodedAsUnion(exp.ttype), "this should be a oftype then");

        const bval = `$Runtime.isSubtype(${this.emitExpression(exp.exp, true)}.tkey, "${exp.ttype}")`;
        return toplevel ? bval : "(" + bval + ")";
    }

    private emitIsNotSubTypeExpression(exp: TIRIsNotSubTypeExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");
        assert(this.typeEncodedAsUnion(exp.ttype), "this should be a oftype then");

        const bval = `!$Runtime.isSubtype(${this.emitExpression(exp.exp, true)}.tkey, "${exp.ttype}")`;
        return toplevel ? bval : "(" + bval + ")";
    }

    private emitAsNoneSpecialExpression(exp: TIRAsNoneSpecialExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");

        const bval = `(${this.emitExpression(exp.exp)}.tkey === "None") ? undefined : $Runtime.raiseRuntimeError("cannot convert value to None")`;
        return toplevel ? bval : "(" + bval + ")";
    }
    
    private emitAsSomeSpecialExpression(exp: TIRAsSomeSpecialExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");

        let bval = "[NOT SET]";
        if(this.typeEncodedAsUnion(exp.etype)) {
            bval = `((__expval__) => (__expval__.tkey !== "None") ? __expval__ : $Runtime.raiseRuntimeError("cannot convert value to Some"))(${this.emitExpression(exp.exp)})`;
        }
        else {
            bval = `((__expval__) => (__expval__.tkey !== "None") ? __expval__.value : $Runtime.raiseRuntimeError("cannot convert value to Some"))(${this.emitExpression(exp.exp)})`;
        }

        return toplevel ? bval : "(" + bval + ")";
    }

    private emitAsNothingSpecialExpression(exp: TIRAsNothingSpecialExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");

        const bval = `(${this.emitExpression(exp.exp)}.tkey === "Nothing") ? null : $Runtime.raiseRuntimeError("cannot convert value to Nothing")`;
        return toplevel ? bval : "(" + bval + ")";
    }

    private emitAsSomethingSpecialExpression(exp: TIRAsSomethingSpecialExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");

        const bval = `((__expval__) => (__expval__.tkey !== "Nothing") ? __expval__.value : $Runtime.raiseRuntimeError("cannot convert value to Something"))(${this.emitExpression(exp.exp)})`;
        return toplevel ? bval : "(" + bval + ")";
    }

    private emitAsOkSpecialExpression(exp: TIRAsOkSpecialExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");

        const bval = `((__expval__) => (${this.emitExpression(exp.exp)}.tkey === "${exp.etype}") ? __expval__.value : $Runtime.raiseRuntimeError("cannot convert value to ok"))(${this.emitExpression(exp.exp)})`;
        return toplevel ? bval : "(" + bval + ")";
    }

    private emitAsErrSpecialExpression(exp: TIRAsErrSpecialExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");

        const bval = `((__expval__) => (${this.emitExpression(exp.exp)}.tkey === "${exp.etype}") ? __expval__.value : $Runtime.raiseRuntimeError("cannot convert value to err"))(${this.emitExpression(exp.exp)})`;
        return toplevel ? bval : "(" + bval + ")";
    }

    private emitAsEqualToLiteralExpression(exp: TIRAsEqualToLiteralExpression, toplevel: boolean): string {
        if(this.typeEncodedAsUnion(exp.exp.etype)) {
            const rr = `$CoreLibs.$KeyEqualMixed(${this.emitExpression(exp.literal.exp, true)}, __expval__, "${exp.literal.exp.etype}")`;
            const bval = `((__expval__) => ${rr} ? ${this.emitExpression(exp.literal.exp, true)} : $Runtime.raiseRuntimeError("cannot convert value to literal"))(${this.emitExpression(exp.exp)})`;
            return toplevel ? bval : "(" + bval + ")";
        }
        else {
            const rr = `($CoreLibs.$KeyEqualOps.get("${exp.literal.exp.etype}"))(${this.emitExpression(exp.literal.exp, true)}, __expval__)`;
            const bval = `((__expval__) => ${rr} ? ${this.emitExpression(exp.literal.exp, true)} : $Runtime.raiseRuntimeError("cannot convert value to literal"))(${this.emitExpression(exp.exp)})`;
            return toplevel ? bval : "(" + bval + ")";
        }
    }

    private emitAsNotEqualToLiteralExpression(exp: TIRAsNotEqualToLiteralExpression, toplevel: boolean): string {
        if(this.typeEncodedAsUnion(exp.exp.etype)) {
            const rr = `!$CoreLibs.$KeyEqualMixed(${this.emitExpression(exp.literal.exp, true)}, __expval__, "${exp.literal.exp.etype}")`;
            const bval = `((__expval__) => ${rr} ? __expval__${!this.typeEncodedAsUnion(exp.etype) ? ".value" : ""} : $Runtime.raiseRuntimeError("cannot convert value to literal"))(${this.emitExpression(exp.exp)})`;
            return toplevel ? bval : "(" + bval + ")";
        }
        else {
            const rr = `!($CoreLibs.$KeyEqualOps.get("${exp.literal.exp.etype}"))(${this.emitExpression(exp.literal.exp, true)}, __expval__)`;
            const bval = `((__expval__) => ${rr} ? ${this.emitExpression(exp.literal.exp, true)} : $Runtime.raiseRuntimeError("cannot convert value to literal"))(${this.emitExpression(exp.exp)})`;
            return toplevel ? bval : "(" + bval + ")";
        }
    }

    private emitAsTypeExpression(exp: TIRAsTypeExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");
        assert(!this.typeEncodedAsUnion(exp.ttype), "this should be a subtype then");

        const bval = `((__expval__) => (__expval__.tkey === "${exp.ttype}") ? __expval__.value : $Runtime.raiseRuntimeError("cannot convert value to ${exp.etype}"))(${this.emitExpression(exp.exp, true)})`;
        return toplevel ? bval : "(" + bval + ")";
    }

    private emitAsNotTypeExpression(exp: TIRAsNotTypeExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");
        assert(!this.typeEncodedAsUnion(exp.ttype), "this should be a subtype then");

        const bval = `((__expval__) => (__expval__.tkey === "${exp.ttype}") ? __expval__${!this.typeEncodedAsUnion(exp.etype) ? ".value" : ""} : $Runtime.raiseRuntimeError("cannot convert value to ${exp.etype}"))(${this.emitExpression(exp.exp, true)})`;
        return toplevel ? bval : "(" + bval + ")";
    }
    
    private emitAsSubTypeExpression(exp: TIRAsSubTypeExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");
        assert(this.typeEncodedAsUnion(exp.ttype), "this should be a oftype then");

        const bval = `((__expval__) => $Runtime.isSubtype(__expval__.tkey, "${exp.ttype}") ? __expval__ : $Runtime.raiseRuntimeError("cannot convert value to ${exp.ttype}"))(${this.emitExpression(exp.exp, true)})`;
        return toplevel ? bval : "(" + bval + ")";
    }

    private emitAsNotSubTypeExpression(exp: TIRAsNotSubTypeExpression, toplevel: boolean): string {
        assert(this.typeEncodedAsUnion(exp.exp.etype), "Why are we doing this test then?");
        assert(this.typeEncodedAsUnion(exp.ttype), "this should be a oftype then");

        const bval = `((__expval__) => $Runtime.isSubtype(__expval__.tkey, "${exp.ttype}") ? __expval__${!this.typeEncodedAsUnion(exp.etype) ? ".value" : ""} : $Runtime.raiseRuntimeError("cannot convert value to ${exp.ttype}"))(${this.emitExpression(exp.exp, true)})`;
        return toplevel ? bval : "(" + bval + ")";
    }

    private emitCallMemberFunctionExpression(exp: TIRCallMemberFunctionExpression, toplevel: boolean): string {
        const aargs = [this.emitExpression(exp.thisarg, true), ...exp.args.map((arg) => this.emitExpression(arg, true))];

        const ttype = this.m_assembly.typeMap.get(exp.tkey) as TIROOType;
        const invk = ttype.memberMethods.find((mm) => mm.ikey === exp.fkey);
        assert(invk !== undefined, "emitCallMemberFunctionExpression");

        const fexp = `${this.resolveTypeMemberAccess(exp.tkey)}`;
        let meexp = "[NOT SET]";
        if((invk as TIRMemberMethodDecl).invoke.tbinds.size === 0 && (invk as TIRMemberMethodDecl).invoke.pcodes.size === 0) {
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
        const thisunion = this.typeEncodedAsUnion(exp.thisarg.etype);

        const aargs = exp.args.map((arg) => this.emitExpression(arg, true));

        let vtable = "[NOT SET]";
        if (thisunion) {
            vtable = `$Runtime.invmap.get($Runtime.vtablemap.get(__expval__.tkey).get("${exp.fname}")).op`
        }
        else {
            vtable = `$Runtime.invmap.get($Runtime.vtablemap.get("${exp.thisarg.etype}").get("${exp.fname}")).op`;
        }

        let thisargas = "[NOT SET]";
        if(thisunion) {
            thisargas = `($Runtime.invmap.get($Runtime.vtablemap.get(__expval__.tkey).get("${exp.fname}")).isatom ? __expval__.value : __expval__)`;
        }
        else {
            thisargas = `($Runtime.invmap.get($Runtime.vtablemap.get(__expval__.tkey).get("${exp.fname}")).isatom ? __expval__ : $Runtime.UnionValue.create("${exp.thisarg.etype}", ${thisarg}))`;
        }

        const eexp = `((__expval__) => ${vtable}(${[thisargas, ...aargs].join(", ")}))(${thisarg})`;

        return toplevel ? eexp : "(" + eexp + ")";
    }
    
    private emitCallMemberFunctionSelfRefExpression(exp: TIRCallMemberFunctionSelfRefExpression, toplevel: boolean): string {
        const aargs = [this.emitExpression(exp.thisarg, true), ...exp.args.map((arg) => this.emitExpression(arg, true))];

        const ttype = this.m_assembly.typeMap.get(exp.tkey) as TIROOType;
        const invk = ttype.memberMethods.find((mm) => mm.ikey === exp.fkey);
        assert(invk !== undefined, "emitCallMemberFunctionExpression");

        const fexp = `${this.resolveTypeMemberAccess(exp.tkey)}`;
        let meexp = "[NOT SET]";
        if((invk as TIRMemberMethodDecl).invoke.tbinds.size === 0 && (invk as TIRMemberMethodDecl).invoke.pcodes.size === 0) {
            meexp = `.${exp.fname}`;
        }
        else {
            meexp = `.$Methods["${exp.fkey}"]`;
        }

        this.m_hasScratch = true;
        return `$Runtime.setScratchValue($$scratch, ${exp.scidx}, ${fexp}${meexp}(${aargs.join(", ")}));`;
    }

    private emitCallMemberFunctionTaskExpression(exp: TIRCallMemberFunctionTaskExpression, toplevel: boolean): string {
        const aargs = ["self", ...exp.args.map((arg) => this.emitExpression(arg, true))];

        const ttype = this.m_assembly.typeMap.get(exp.tsktype) as TIRTaskType;
        const invk = ttype.memberMethods.find((mm) => mm.ikey === exp.fkey);
        assert(invk !== undefined, "emitCallMemberFunctionExpression");

        const fexp = `${this.resolveTypeMemberAccess(exp.tsktype)}`;
        let meexp = "[NOT SET]";
        if((invk as TIRMemberMethodDecl).invoke.tbinds.size === 0 && (invk as TIRMemberMethodDecl).invoke.pcodes.size === 0) {
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
        if((invk as TIRMemberMethodDecl).invoke.tbinds.size === 0 && (invk as TIRMemberMethodDecl).invoke.pcodes.size === 0) {
            meexp = `.${exp.fname}`;
        }
        else {
            meexp = `.$Methods["${exp.fkey}"]`;
        }

        this.m_hasScratch = true;
        return `$Runtime.setScratchValue($$scratch, ${exp.scidx}, ${fexp}${meexp}(${aargs.join(", ")}));`;
    }

    private emitCallMemberActionExpression(exp: TIRCallMemberActionExpression, toplevel: boolean): string {
        const aargs = ["self", ...exp.args.map((arg) => this.emitExpression(arg, true))];
        const fexp = `${this.resolveTypeMemberAccess(exp.tsktype)}.${exp.fname}`;

        this.m_hasScratch = true;
        return `$Runtime.setScratchValue($$scratch, ${exp.scidx}, ${fexp}(${aargs.join(", ")}));`;
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
            case TIRExpressionTag.AccessConstMemberFieldExpression: {
                return this.emitAccessConstMemberFieldExpression(exp as TIRAccessConstMemberFieldExpression);
            }
            case TIRExpressionTag.AccessVariableExpression: {
                return this.emitAccessVariableExpression(exp as TIRAccessVariableExpression);
            }
            case TIRExpressionTag.AccessCapturedVariableExpression: {
                return this.emitAccessCapturedVariableExpression(exp as TIRAccessCapturedVariableExpression);
            }
            case TIRExpressionTag.AccessScratchSingleValueExpression: {
                return this.emitAccessScratchSingleValueExpression(exp as TIRAccessScratchSingleValueExpression);
            }
            case TIRExpressionTag.AccessScratchIndexExpression: {
                return this.emitAccessScratchIndexExpression(exp as TIRAccessScratchIndexExpression);
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
            case TIRExpressionTag.ConstructorListExpression : {
                return this.emitConstructorListExpression(exp as TIRConstructorListExpression);
            }
            case TIRExpressionTag.ConstructorMapExpression: {
                return this.emitConstructorMapExpression(exp as TIRConstructorMapExpression);
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
            case TIRExpressionTag.InjectExpression: {
                return this.emitInjectExpression(exp as TIRInjectExpression, toplevel || false);
            }
            case TIRExpressionTag.ExtractExpression: {
                return this.emitExtractExpression(exp as TIRExtractExpression, toplevel || false);
            }
            case TIRExpressionTag.CreateCodePackExpression: {
                return this.emitCreateCodePackExpression(exp as TIRCreateCodePackExpression);
            }
            case TIRExpressionTag.IsNoneSpecialExpression: {
                return this.emitIsNoneSpecialExpression(exp as TIRIsNoneSpecialExpression, toplevel || false);
            }
            case TIRExpressionTag.IsSomeSpecialExpression: {
                return this.emitIsSomeSpecialExpression(exp as TIRIsSomeSpecialExpression, toplevel || false);
            }
            case TIRExpressionTag.IsNothingSpecialExpression: {
                return this.emitIsNothingSpecialExpression(exp as TIRIsNothingSpecialExpression, toplevel || false);
            }
            case TIRExpressionTag.IsSomethingSpecialExpression: {
                return this.emitIsSomethingSpecialExpression(exp as TIRIsSomethingSpecialExpression, toplevel || false);
            }
            case TIRExpressionTag.IsOkSpecialExpression: {
                return this.emitIsOkSpecialExpression(exp as TIRIsOkSpecialExpression, toplevel || false);
            }
            case TIRExpressionTag.IsErrSpecialExpression: {
                return this.emitIsErrSpecialExpression(exp as TIRIsErrSpecialExpression, toplevel || false);
            }
            case TIRExpressionTag.IsEqualToLiteralExpression: {
                return this.emitIsEqualToLiteralExpression(exp as TIRIsEqualToLiteralExpression, toplevel || false);
            }
            case TIRExpressionTag.IsNotEqualToLiteralExpression: {
                return this.emitIsNotEqualToLiteralExpression(exp as TIRIsNotEqualToLiteralExpression, toplevel || false);
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
            case TIRExpressionTag.AsNoneSpecialExpression: {
                return this.emitAsNoneSpecialExpression(exp as TIRAsNoneSpecialExpression, toplevel || false);
            }
            case TIRExpressionTag.AsSomeSpecialExpression: {
                return this.emitAsSomeSpecialExpression(exp as TIRAsSomeSpecialExpression, toplevel || false);
            }
            case TIRExpressionTag.AsNothingSpecialExpression: {
                return this.emitAsNothingSpecialExpression(exp as TIRAsNothingSpecialExpression, toplevel || false);
            }
            case TIRExpressionTag.AsSomethingSpecialExpression: {
                return this.emitAsSomethingSpecialExpression(exp as TIRAsSomethingSpecialExpression, toplevel || false);
            }
            case TIRExpressionTag.AsOkSpecialExpression: {
                return this.emitAsOkSpecialExpression(exp as TIRAsOkSpecialExpression, toplevel || false);
            }
            case TIRExpressionTag.AsErrSpecialExpression: {
                return this.emitAsErrSpecialExpression(exp as TIRAsErrSpecialExpression, toplevel || false);
            }
            case TIRExpressionTag.AsEqualToLiteralExpression: {
                return this.emitAsEqualToLiteralExpression(exp as TIRAsEqualToLiteralExpression, toplevel || false);
            }
            case TIRExpressionTag.AsNotEqualToLiteralExpression: {
                return this.emitAsNotEqualToLiteralExpression(exp as TIRAsNotEqualToLiteralExpression, toplevel || false);
            }
            case TIRExpressionTag.AsTypeExpression: {
                return this.emitAsTypeExpression(exp as TIRAsTypeExpression, toplevel || false);
            }
            case TIRExpressionTag.AsNotTypeExpression: {
                return this.emitAsNotTypeExpression(exp as TIRAsNotTypeExpression, toplevel || false);
            }
            case TIRExpressionTag.AsSubTypeExpression: {
                return this.emitAsSubTypeExpression(exp as TIRAsSubTypeExpression, toplevel || false);
            }
            case TIRExpressionTag.AsNotSubTypeExpression: {
                return this.emitAsNotSubTypeExpression(exp as TIRAsNotSubTypeExpression, toplevel || false);
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
        return `$Runtime.raiseUserAssert("${stmt.msg}");`;
    }

    private emitAssertCheckStatement(stmt: TIRAssertCheckStatement): string {
        return `$Runtime.raiseUserAssertIf(!((() => { try { return ${this.emitExpression(stmt.cond, true)}; } catch (ex) { $Runtime.log("warn", "AssertEvalFailure", "condition failure"); return true; } })()), "${stmt.msg}");`;
    }

    private emitDebugStatement(stmt: TIRDebugStatement): string {
        return `try { console.log(${this.emitExpression(stmt.value, true)}); } catch(ex) { console.log("__debug(${stmt.value.expstr}) evaluation failed"); }`;
    }

    private emitVarDeclareStatement(stmt: TIRVarDeclareStatement): string {
        return `let ${stmt.vname};`;
    }

    private emitVarDeclareAndAssignStatement(stmt: TIRVarDeclareAndAssignStatement): string {
        return `let ${stmt.vname} = ${this.emitExpression(stmt.vexp, true)};`;
    }

    private emitVarAssignStatement(stmt: TIRVarAssignStatement): string {
        if(stmt.vname !== "this") {
            return `${stmt.vname} = ${this.emitExpression(stmt.vexp, true)};`;
        }
        else {
            return `$_this = ${this.emitExpression(stmt.vexp, true)};`;
        }
    }

    private emitStoreToScratch(stmt: TIRStoreToScratch): string {
        this.m_hasScratch = true;
        return `$Runtime.setScratchValue($$scratch, ${stmt.scidx}, ${this.emitExpression(stmt.exp, true)});`;
    }

    private emitVarRefAssignFromScratch(stmt: TIRVarRefAssignFromScratch): string {
        if(stmt.vname !== "this") {
            return `${stmt.vname} = $$scratch[${stmt.scidx}][0];`;
        }
        else {
            return `$_this = $$scratch[${stmt.scidx}][0];`;
        }
    }

    private emitTaskRefAssignFromScratch(stmt: TIRTaskRefAssignFromScratch): string {
        return `self = $$scratch[${stmt.scidx}];`;
    }

    private emitCallStatementWRef(stmt: TIRCallStatementWRef): string {
        return this.emitExpression(stmt.vexp, true);
    }

    private emitCallStatementWTaskRef(stmt: TIRCallStatementWTaskRef): string {
        return this.emitExpression(stmt.vexp, true);
    }

    private emitCallStatementWAction(stmt: TIRCallStatementWAction): string {
        return this.emitExpression(stmt.vexp, true);
    }

    private emitVariableRetypeStatement(stmt: TIRVariableRetypeStatement): string {
       return `${stmt.vname} = ${this.emitExpression(stmt.asconv, true)};`
    }

    private emitVariableSCRetypeStatement(stmt: TIRVariableSCRetypeStatement): string {
        const binder = stmt.binderinfo !== undefined ? ` ${stmt.binderinfo[1]} = ${this.emitExpression(stmt.binderinfo[0], true)};` : ""
        return `if(${this.emitExpression(stmt.test, true)}) { ${stmt.vname} = ${this.emitExpression(stmt.asconv, true)}; } else {${binder} return ${this.emitExpression(stmt.resexp, true)}; }`
    }

    private emitScratchSCStatement(stmt: TIRScratchSCStatement): string {
        assert(false, "NOT IMPLEMENTED -- TIRScratchSCStatement");
        return "NOT IMPLEMENTED -- TIRScratchSCStatement";
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
        let sstr = "";
        if(stmt.ifentry.binderinfo === undefined) {
            const poststr = stmt.ifentry.recasttypes.length !== 0 ? stmt.ifentry.recasttypes.map((rct) => `${rct.vname} = ${this.emitExpression(rct.cast, true)};`).join(" ") : undefined;
            sstr = `if(${this.emitExpression(stmt.ifentry.test, true)}) ${this.emitScopedBlock(stmt.ifentry.value, indent, undefined, poststr)}\n`;
        }
        else {
            this.m_hasScratch = true;
            const tstr = `($Runtime.setScratchValue($$scratch, ${stmt.ifentry.binderinfo[1]}, ${this.emitExpression(stmt.ifentry.binderinfo[0])}) || ${this.emitExpression(stmt.ifentry.test)})`;
            const prestr = `var ${stmt.ifentry.binderinfo[3]} = ${this.emitExpression(stmt.ifentry.binderinfo[2], true)};`
            const poststr = stmt.ifentry.recasttypes.length !== 0 ? stmt.ifentry.recasttypes.map((rct) => `${rct.vname} = ${this.emitExpression(rct.cast, true)};`).join(" ") : undefined;
            sstr = `if(${tstr}) ${this.emitScopedBlock(stmt.ifentry.value, indent, prestr, poststr)}\n`;
        } 

        for (let i = 0; i < stmt.elifentries.length; ++i) {
            const eei = stmt.elifentries[i];
            const poststr = stmt.ifentry.recasttypes.length !== 0 ? eei.recasttypes.map((rct) => `${rct.vname} = ${this.emitExpression(rct.cast, true)};`).join(" ") : undefined;

            if (eei.binderinfo === undefined) {
                sstr += indent + `else if(${this.emitExpression(eei.test, true)}) ${this.emitScopedBlock(eei.value, indent, undefined, poststr)}\n`;
            }
            else {
                this.m_hasScratch = true;
                const tstr = `($Runtime.setScratchValue($$scratch, ${eei.binderinfo[1]}, ${this.emitExpression(eei.binderinfo[0], true)}) || ${this.emitExpression(eei.test)})`;
                const prestr = `var ${eei.binderinfo[3]} = ${this.emitExpression(eei.binderinfo[2], true)};`
                sstr += `if(${tstr}) ${this.emitScopedBlock(eei.value, indent, prestr, poststr)}\n`;
            }
        }

        if(stmt.elseentry.binderinfo === undefined) {
            const poststr = stmt.ifentry.recasttypes.length !== 0 ? stmt.elseentry.recasttypes.map((rct) => `${rct.vname} = ${this.emitExpression(rct.cast, true)};`).join(" ") : undefined;
            sstr += indent + `else ${this.emitScopedBlock(stmt.elseentry.value, indent, undefined, poststr)}\n`;
        }
        else {
            this.m_hasScratch = true;
            const poststr = stmt.ifentry.recasttypes.length !== 0 ? stmt.elseentry.recasttypes.map((rct) => `${rct.vname} = ${this.emitExpression(rct.cast, true)};`).join(" ") : undefined;
            const prestr = `$Runtime.setScratchValue($$scratch, ${stmt.elseentry.binderinfo[1]}, ${this.emitExpression(stmt.elseentry.binderinfo[0], true)}); var ${stmt.elseentry.binderinfo[3]} = ${this.emitExpression(stmt.elseentry.binderinfo[2], true)};`
            sstr += indent + `else ${this.emitScopedBlock(stmt.elseentry.value, indent, prestr, poststr)}\n`;
        }

        return sstr;
    }

    private emitSwitchStatement(stmt: TIRSwitchStatement, indent: string): string {
        assert(false, "NOT IMPLEMENTED -- TIRSwitchStatement");
        return "NOT IMPLEMENTED -- TIRSwitchStatement";

        /*
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
                sstr += indent + "    " + `$Runtime.raiseRuntimeError("Non-exhaustive switch statement" + " -- ${this.m_file} @ line ${stmt.sinfo.line}")` + ";\n"
            }
            sstr += indent + "}\n";
        }

        return sstr;
        */
    }

    private emitMatchStatement(stmt: TIRMatchStatement, indent: string): string {
        this.m_hasScratch = true;
        let sstr = `$Runtime.setScratchValue($$scratch, ${stmt.scratchidx}, ${this.emitExpression(stmt.exp, true)});\n\n`;

        if(stmt.clauses[0].binderinfo === undefined) {
            const poststr = stmt.clauses[0].recasttypes.length !== 0 ? stmt.clauses[0].recasttypes.map((rct) => `${rct.vname} = ${this.emitExpression(rct.cast, true)};`).join(" ") : undefined;
            sstr += indent + `if(${this.emitExpression(stmt.clauses[0].match, true)}) ${this.emitScopedBlock(stmt.clauses[0].value, indent, undefined, poststr)}\n`;
        }
        else {
            const prestr = `var ${stmt.clauses[0].binderinfo[1]} = ${this.emitExpression(stmt.clauses[0].binderinfo[0], true)};`
            const poststr = stmt.clauses[0].recasttypes.length !== 0 ? stmt.clauses[0].recasttypes.map((rct) => `${rct.vname} = ${this.emitExpression(rct.cast, true)};`).join(" ") : undefined;
            sstr += indent + `if(${this.emitExpression(stmt.clauses[0].match, true)}) ${this.emitScopedBlock(stmt.clauses[0].value, indent, prestr, poststr)}\n`;
        }

        for(let i = 1; i < stmt.clauses.length; ++i) {
            if(stmt.clauses[i].binderinfo === undefined) {
                const poststr = stmt.clauses[i].recasttypes.length !== 0 ? stmt.clauses[i].recasttypes.map((rct) => `${rct.vname} = ${this.emitExpression(rct.cast, true)};`).join(" ") : undefined;
                sstr += indent + `else if(${this.emitExpression(stmt.clauses[i].match, true)}) ${this.emitScopedBlock(stmt.clauses[i].value, indent, undefined, poststr)}\n`;
            }
            else {
                const binfo = stmt.clauses[i].binderinfo as [TIRExpression, string];

                const prestr = `var ${binfo[1]} = ${this.emitExpression(binfo[0], true)};`
                const poststr = stmt.clauses[i].recasttypes.length !== 0 ? stmt.clauses[i].recasttypes.map((rct) => `${rct.vname} = ${this.emitExpression(rct.cast, true)};`).join(" ") : undefined;
                sstr += indent + `else if(${this.emitExpression(stmt.clauses[i].match, true)}) ${this.emitScopedBlock(stmt.clauses[i].value, indent, prestr, poststr)}\n`;
            }
        }

        if(stmt.edefault !== undefined) {
            if(stmt.edefault.binderinfo === undefined) {
                const poststr = stmt.edefault.recasttypes.length !== 0 ? stmt.edefault.recasttypes.map((rct) => `${rct.vname} = ${this.emitExpression(rct.cast, true)};`).join(" ") : undefined;
                sstr += indent + `else ${this.emitScopedBlock(stmt.edefault.value, indent, undefined, poststr)}\n`;
            }
            else {
                const prestr = `var ${stmt.edefault.binderinfo[1]} = ${this.emitExpression(stmt.edefault.binderinfo[0], true)};`
                const poststr = stmt.edefault.recasttypes.length !== 0 ? stmt.edefault.recasttypes.map((rct) => `${rct.vname} = ${this.emitExpression(rct.cast, true)};`).join(" ") : undefined;
                sstr += indent + `else ${this.emitScopedBlock(stmt.edefault.value, indent, prestr, poststr)}\n`;
            }
        }
        else {
            sstr += indent + "else {\n"
            if(stmt.isexhaustive) {
                sstr += indent + "    ;\n";
            }
            else {
                sstr += indent + "    " + `$Runtime.raiseRuntimeError("Non-exhaustive match statement" + " -- ${this.m_file} @ line ${stmt.sinfo.line}")` + ";\n"
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
        const fmt = `${stmt.fmt.ns}.${stmt.fmt}`; 
        const args = stmt.args.map((arg) => this.emitExpression(arg)).join(", ")

        return `if($Runtime.checkloglevel(${stmt.level})) { try { $Runtime.log("${fmt}", ${stmt.level}, ${fmt}, ${args}); } catch(ex) { $Runtime.log("LoggerError", "error", "[[logging failure -- ${this.m_file}@${stmt.sinfo.line}]]"); } }`;
    }

    private emitLoggerEmitConditionalStatement(stmt: TIRLoggerEmitConditionalStatement): string {
        const fmt = `${stmt.fmt.ns}.${stmt.fmt}`; 
        const args = stmt.args.map((arg) => this.emitExpression(arg)).join(", ")
        
        const test = this.emitExpression(stmt.cond);
        return `if($Runtime.checkloglevel(${stmt.level} && ${test})) { try { $Runtime.log("${fmt}", ${stmt.level}, ${fmt}, ${args}); } catch(ex) { $Runtime.log("LoggerError", "error", "[[logging failure -- ${this.m_file}@${stmt.sinfo.line}]]"); } }`
    }

    private emitLoggerSetPrefixStatement(stmt: TIRLoggerSetPrefixStatement, indent: string): string {
        const fmt = `${stmt.fmt.ns}.${stmt.fmt}`; 
        const args = stmt.args.map((arg) => this.emitExpression(arg)).join(", ")
        
        const bblock = (stmt.block instanceof TIRScopedBlockStatement) ? this.emitScopedBlock(stmt.block, indent) : this.emitUnscopedBlock(stmt.block, indent);

        //TODO: unscoped block needs some work here!
        return `$Runtime.pushlogprefix(${fmt}, ${args}); try ${bblock}\n${indent}catch(ex) { $Runtime.log("LoggerError", "error", "[[logging failure -- ${this.m_file}@${stmt.sinfo.line}]]"); } \n${indent}$Runtime.poplogprefix();`
    }

    emitScopedBlock(blck: TIRScopedBlockStatement, indent: string, prestr?: string | undefined, poststr?: string | undefined): string {
        const stmts = blck.ops.map((op) => indent + "    " + this.emitStatement(op, indent + "    ")).join("\n");

        return " {\n" + (prestr !== undefined ? `${indent + "    "}${prestr}\n` : "") + stmts + "\n" + (poststr !== undefined ? `${indent + "    "}${poststr}\n` : "") + indent + "}";
    }

    emitUnscopedBlock(blck: TIRUnscopedBlockStatement, indent: string): string {
        //TODO: need to declare vars as let before block so we can support things like -- LoggerSetPrefix that need to wrap the block as a try{...}catch{...}
        return NOT_IMPLEMENTED_STATEMENT("TIRUnscopedBLock");
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
            case TIRStatementTag.StoreToScratch: {
                return this.emitStoreToScratch(stmt as TIRStoreToScratch);
            }
            case TIRStatementTag.VarRefAssignFromScratch: {
                return this.emitVarRefAssignFromScratch(stmt as TIRVarRefAssignFromScratch);
            }
            case TIRStatementTag.TaskRefAssignFromScratch: {
                return this.emitTaskRefAssignFromScratch(stmt as TIRTaskRefAssignFromScratch);
            }
            case TIRStatementTag.CallWRefStatement: {
                return this.emitCallStatementWRef(stmt as TIRCallStatementWRef);
            }
            case TIRStatementTag.CallStatementWTaskRef: {
                return this.emitCallStatementWTaskRef(stmt as TIRCallStatementWTaskRef);
            }
            case TIRStatementTag.CallStatementWTaskAction: {
                return this.emitCallStatementWAction(stmt as TIRCallStatementWAction);
            }
            case TIRStatementTag.VariableRetypeStatement: {
                return this.emitVariableRetypeStatement(stmt as TIRVariableRetypeStatement);
            }
            case TIRStatementTag.VariableSCRetypeStatement: {
                return this.emitVariableSCRetypeStatement(stmt as TIRVariableSCRetypeStatement);
            }
            case TIRStatementTag.ScratchSCStatement: {
                return this.emitScratchSCStatement(stmt as TIRScratchSCStatement);
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
            case TIRStatementTag.LoggerSetPrefixStatement: {
                return this.emitLoggerSetPrefixStatement(stmt as TIRLoggerSetPrefixStatement, indent);
            }
            default: {
                assert(false, `Unknown statement kind ${stmt.tag}`);
                return `[UNKNOWN TAG ${stmt.tag}]`
            }
        }
    }

    emitBodyStatementList(body: TIRStatement[], preconds: TIRPreConditionDecl[], postconds: TIRPostConditionDecl[], indent: string, fname: string, extractres: boolean): string {
        const bodyindent = indent + "    ";
        const wbodyindent = bodyindent + "    ";
        let rconds = "";

        if(preconds.length !== 0) {
            rconds = bodyindent + preconds.map((pc) => `$Runtime.raiseUserAssertIf(!((() => { try { return ${this.emitExpression(pc.exp)}; } catch (ex) { $Runtime.log("warn", "PreCondEvalFailure", "condition failure"); return true; } })()), "Failed precondition ${fname} -- ${pc.exp.expstr}");`).join("\n" + bodyindent) + "\n";
        }

        const bstmts = body.map((stmt) => this.emitStatement(stmt, postconds.length === 0 ? bodyindent : wbodyindent));
        const scratch = this.m_hasScratch ? `${bodyindent}let $$scratch = [];\n` : "";

        if(postconds.length === 0) {
            return `{\n${scratch}${rconds}${bodyindent}${bstmts.join("\n" + bodyindent)}\n${indent}}`;
        }
        else {
            const bstr = `{\n${bstmts.join("\n" + wbodyindent)}\n${bodyindent}}`;
            const econds = bodyindent + postconds.map((pc) => `$Runtime.raiseUserAssertIf(!((() => { try { return ${this.emitExpression(pc.exp)}; } catch (ex) { $Runtime.log("warn", "PreCondEvalFailure", "condition failure"); return true; } })()), "Failed postcondition ${fname} -- ${pc.exp.expstr}");`).join("\n" + bodyindent);

            return `{\n${scratch}${rconds}const $$return" = (() => ${bstr})();\n${bodyindent}$return = ${extractres ? "$$return[1]" : "$$return"};\n${econds}\n${bodyindent}return $$return;\n${indent}}`;
        }
    }
}

export {
    BodyEmitter
};
