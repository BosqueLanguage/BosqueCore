
import { ResolvedFunctionType, ResolvedType, TemplateBindScope } from "./resolved_type";
import { TIRCodePack, TIRExpression, TIRInvalidExpression } from "../tree_ir/tir_body";
import { SourceInfo } from "../build_decls";

class VarInfo {
    readonly declaredType: ResolvedType;

    readonly isConst: boolean;
    readonly isCaptured: boolean;
    readonly mustDefined: boolean;

    constructor(dtype: ResolvedType,isConst: boolean, isCaptured: boolean, mustDefined: boolean) {
        this.declaredType = dtype;

        this.isConst = isConst;
        this.isCaptured = isCaptured;
        this.mustDefined = mustDefined;
    }
}

class ExpressionTypeEnvironment {
    readonly binds: TemplateBindScope;
    readonly pcodes: Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>;

    readonly frozenVars: Set<string>;
    readonly args: Map<string, VarInfo>;
    readonly locals: Map<string, VarInfo>[];

    readonly expressionResult: TIRExpression;
    readonly trepr: ResolvedType; //The type of the expression (value representation)

    private constructor(binds: TemplateBindScope, pcodes: Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>, frozenVars: Set<string>, args: Map<string, VarInfo>, locals: Map<string, VarInfo>[], expressionResult: TIRExpression, trepr: ResolvedType) {
        this.binds = binds;
        this.pcodes = pcodes;

        this.frozenVars = frozenVars;
        this.args = args;
        this.locals = locals;

        this.expressionResult = expressionResult;
        this.trepr = trepr;
    }

    getLocalVarInfo(name: string): VarInfo | undefined {
        const locals = this.locals as Map<string, VarInfo>[];
        for (let i = locals.length - 1; i >= 0; --i) {
            if (locals[i].has(name)) {
                return (locals[i].get(name) as VarInfo);
            }
        }

        return undefined;
    }

    isVarNameDefined(name: string): boolean {
        return this.getLocalVarInfo(name) !== undefined || (this.args as Map<string, VarInfo>).has(name);
    }

    lookupVar(name: string): VarInfo | null {
        return this.getLocalVarInfo(name) || (this.args as Map<string, VarInfo>).get(name) || null;
    }

    static createInitialEnvForExpressionEval(binds: TemplateBindScope, pcodes: Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>, frozenVars: Set<string>, args: Map<string, VarInfo>, locals: Map<string, VarInfo>[]): ExpressionTypeEnvironment {
        return new ExpressionTypeEnvironment(binds, pcodes, frozenVars, args, locals, new TIRInvalidExpression(SourceInfo.implicitSourceInfo(), "None"), ResolvedType.createInvalid());
    }

    static createInitialEnvForEvalStandalone(binds: TemplateBindScope): ExpressionTypeEnvironment {
        return new ExpressionTypeEnvironment(binds, new Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>(), new Set<string>(), new Map<string, VarInfo>(), [], new TIRInvalidExpression(SourceInfo.implicitSourceInfo(), "None"), ResolvedType.createInvalid());
    }

    static createInitialEnvForEvalWArgs(binds: TemplateBindScope, args: Map<string, VarInfo>): ExpressionTypeEnvironment {
        return new ExpressionTypeEnvironment(binds, new Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>(), new Set<string>(), args, [], new TIRInvalidExpression(SourceInfo.implicitSourceInfo(), "None"), ResolvedType.createInvalid());
    }

    static createInitialEnvForEvalWArgsPCodes(binds: TemplateBindScope, pcodes: Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>, args: Map<string, VarInfo>): ExpressionTypeEnvironment {
        return new ExpressionTypeEnvironment(binds, pcodes, new Set<string>(), args, [], new TIRInvalidExpression(SourceInfo.implicitSourceInfo(), "None"), ResolvedType.createInvalid());
    }

    static createInitialEnvForLiteralEval(binds: TemplateBindScope): ExpressionTypeEnvironment {
        return new ExpressionTypeEnvironment(binds, new Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>(), new Set<string>(), new Map<string, VarInfo>(), [], new TIRInvalidExpression(SourceInfo.implicitSourceInfo(), "None"), ResolvedType.createInvalid());
    }

    createFreshEnvExpressionFrom(): ExpressionTypeEnvironment {
        return new ExpressionTypeEnvironment(this.binds, this.pcodes, this.frozenVars, this.args, this.locals, new TIRInvalidExpression(SourceInfo.implicitSourceInfo(), "None"), ResolvedType.createInvalid());
    }

    setResultExpressionInfo(exp: TIRExpression, trepr: ResolvedType): ExpressionTypeEnvironment {
       return new ExpressionTypeEnvironment(this.binds, this.pcodes, this.frozenVars, this.args, this.locals, exp, trepr);
    }

    pushBinderFrame(binder: string, btype: ResolvedType): ExpressionTypeEnvironment {
        const nframe = new Map<string, VarInfo>([[binder, new VarInfo(btype, true, false, true)]]);
        return new ExpressionTypeEnvironment(this.binds, this.pcodes, this.frozenVars, this.args, [...this.locals, nframe], new TIRInvalidExpression(SourceInfo.implicitSourceInfo(), "None"), ResolvedType.createInvalid());
    }

    popBinderFrame() {
        return new ExpressionTypeEnvironment(this.binds, this.pcodes, this.frozenVars, this.args, this.locals.slice(0, this.locals.length - 1), this.expressionResult, this.trepr);
    }
}

class StatementTypeEnvironment {
    readonly binds: TemplateBindScope;
    readonly pcodes: Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>;

    readonly frozenVars: Set<string>;
    readonly args: Map<string, VarInfo>;
    readonly locals: Map<string, VarInfo>[];
    
    readonly isDeadFlow: boolean;

    private constructor(binds: TemplateBindScope, pcodes: Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>, frozenVars: Set<string>, args: Map<string, VarInfo>, locals: Map<string, VarInfo>[], isDeadFlow: boolean) {
        this.binds = binds;
        this.pcodes = pcodes;

        this.frozenVars = frozenVars;
        this.args = args;
        this.locals = locals;

        this.isDeadFlow = isDeadFlow;
    }

    getDefVarInfo(): string[] {
        const args = [...this.args].sort((a, b) => a[0].localeCompare(b[0])).map((vv) => vv[0]);
        const locals = this.locals.map((ll) => [...ll].sort((a, b) => a[0].localeCompare(b[0])).map((vv) => vv[0]));

        return args.concat(...locals);
    }

    addVar(name: string, isConst: boolean, dtype: ResolvedType, isDefined: boolean): StatementTypeEnvironment {
        let localcopy = (this.locals as Map<string, VarInfo>[]).map((frame) => new Map<string, VarInfo>(frame));
        localcopy[localcopy.length - 1].set(name, new VarInfo(dtype, isConst, false, isDefined));

        return new StatementTypeEnvironment(this.binds, this.pcodes, this.frozenVars, this.args, localcopy, false);
    }

    setVar(name: string): StatementTypeEnvironment {
        const oldv = this.lookupVar(name) as VarInfo;

        let localcopy = (this.locals as Map<string, VarInfo>[]).map((frame) => new Map<string, VarInfo>(frame));
        localcopy[localcopy.length - 1].set(name, new VarInfo(oldv.declaredType, false, false, true));
           
        return new StatementTypeEnvironment(this.binds, this.pcodes, this.frozenVars, this.args, localcopy, false);
    }

    endOfExecution(): StatementTypeEnvironment {
        return new StatementTypeEnvironment(this.binds, this.pcodes, this.frozenVars, this.args, this.locals, true);
    }

    getLocalVarInfo(name: string): VarInfo | undefined {
        const locals = this.locals as Map<string, VarInfo>[];
        for (let i = locals.length - 1; i >= 0; --i) {
            if (locals[i].has(name)) {
                return (locals[i].get(name) as VarInfo);
            }
        }

        return undefined;
    }

    isVarNameDefined(name: string): boolean {
        return this.getLocalVarInfo(name) !== undefined || (this.args as Map<string, VarInfo>).has(name);
    }

    lookupVar(name: string): VarInfo | null {
        return this.getLocalVarInfo(name) || (this.args as Map<string, VarInfo>).get(name) || null;
    }

    hasNormalFlow(): boolean {
        return !this.isDeadFlow;
    }

    static createInitialEnvForStatementEval(binds: TemplateBindScope, pcodes: Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>, frozenVars: Set<string>, args: Map<string, VarInfo>, locals: Map<string, VarInfo>[]): StatementTypeEnvironment {
        return new StatementTypeEnvironment(binds, pcodes, frozenVars, args, locals, false);
    }

    createInitialEnvForExpressionEval(): ExpressionTypeEnvironment {
        return ExpressionTypeEnvironment.createInitialEnvForExpressionEval(this.binds, this.pcodes, this.frozenVars, this.args, this.locals);
    }

    pushLocalScope(): StatementTypeEnvironment {
        const localscopy = [...(this.locals as Map<string, VarInfo>[]), new Map<string, VarInfo>()];
        return new StatementTypeEnvironment(this.binds, this.pcodes, this.frozenVars, this.args, localscopy, this.isDeadFlow);
    }

    popLocalScope(): StatementTypeEnvironment {
        const localscopy = (this.locals as Map<string, VarInfo>[]).slice(0, -1);
        return new StatementTypeEnvironment(this.binds, this.pcodes, this.frozenVars, this.args, localscopy, this.isDeadFlow);
    }
}

export {
    VarInfo, ExpressionTypeEnvironment, StatementTypeEnvironment
};
