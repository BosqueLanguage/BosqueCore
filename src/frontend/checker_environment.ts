import {strict as assert} from "assert";

import { TypeSignature } from "./type";

class VarInfo {
    readonly declaredType: TypeSignature;

    readonly isConst: boolean;
    readonly mustDefined: boolean;

    constructor(dtype: TypeSignature, isConst: boolean, mustDefined: boolean) {
        this.declaredType = dtype;

        this.isConst = isConst;
        this.mustDefined = mustDefined;
    }
}

class TemplateBindingScope {
    readonly typebinds: Map<string, TypeSignature>;
    readonly invokebinds: Map<string, TypeSignature>;

    constructor(typebinds: Map<string, TypeSignature>, invokebinds: Map<string, TypeSignature>) {
        this.typebinds = typebinds;
        this.invokebinds = invokebinds;
    }

    static createEmptyScope(): TemplateBindingScope {
        return new TemplateBindingScope(new Map<string, TypeSignature>(), new Map<string, TypeSignature>());
    }

    resolveTypeBinding(name: string): TypeSignature | undefined {
        let rtype: TypeSignature | undefined = undefined;

        if(this.invokebinds.has(name)) {
            rtype = this.invokebinds.get(name);
        }

        if(this.typebinds.has(name)) {
            rtype = this.typebinds.get(name);
        }

        return rtype;
    }
}

class ExpressionTypeEnvironment {
    readonly binds: TemplateBindingScope;
    readonly capturedpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>;
    readonly capturedvars: Map<string, VarInfo>;

    readonly argpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>;
    readonly args: Map<string, VarInfo>;
    readonly locals: Map<string, VarInfo>[];

    readonly trepr: ResolvedType; //The type of the expression (value representation)

    private constructor(binds: TemplateBindScope, capturedpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>, capturedvars: Map<string, VarInfo>, argpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>, args: Map<string, VarInfo>, locals: Map<string, VarInfo>[], expressionResult: TIRExpression, trepr: ResolvedType) {
        this.binds = binds;
        this.capturedpcodes = capturedpcodes;
        this.capturedvars = capturedvars;

        this.argpcodes = argpcodes;
        this.args = args;
        this.locals = locals;

        this.expressionResult = expressionResult;
        this.trepr = trepr;
    }

    private getLocalVarInfo(name: string): VarInfo | undefined {
        const locals = this.locals as Map<string, VarInfo>[];
        for (let i = locals.length - 1; i >= 0; --i) {
            if (locals[i].has(name)) {
                return (locals[i].get(name) as VarInfo);
            }
        }

        return undefined;
    }

    lookupLocalVar(name: string): VarInfo | null {
        return this.getLocalVarInfo(name) || (this.args.get(name) || null);
    }

    lookupCapturedVar(name: string): VarInfo | null {
        return this.capturedvars.get(name) || null;
    }

    lookupArgPCode(name: string): {pcode: TIRCodePack, ftype: ResolvedFunctionType} | null {
        return this.argpcodes.get(name) || null;
    }

    lookupCapturedPCode(name: string): {pcode: TIRCodePack, ftype: ResolvedFunctionType} | null {
        return this.capturedpcodes.get(name) || null;
    }

    static createInitialEnvForExpressionEval(binds: TemplateBindScope, capturedpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>, capturedvars: Map<string, VarInfo>, argpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>, args: Map<string, VarInfo>, locals: Map<string, VarInfo>[]): ExpressionTypeEnvironment {
        return new ExpressionTypeEnvironment(binds, capturedpcodes, capturedvars, argpcodes, args, locals, new TIRInvalidExpression(SourceInfo.implicitSourceInfo(), "None"), ResolvedType.createInvalid());
    }

    static createInitialEnvForEvalStandalone(binds: TemplateBindScope): ExpressionTypeEnvironment {
        return new ExpressionTypeEnvironment(binds, new Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>(), new Map<string, VarInfo>(), new Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>(), new Map<string, VarInfo>(), [], new TIRInvalidExpression(SourceInfo.implicitSourceInfo(), "None"), ResolvedType.createInvalid());
    }

    static createInitialEnvForEvalWArgs(binds: TemplateBindScope, args: Map<string, VarInfo>): ExpressionTypeEnvironment {
        return new ExpressionTypeEnvironment(binds, new Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>(), new Map<string, VarInfo>(), new Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>(), args, [], new TIRInvalidExpression(SourceInfo.implicitSourceInfo(), "None"), ResolvedType.createInvalid());
    }

    static createInitialEnvForEvalWArgsAndPCodeArgs(binds: TemplateBindScope, argpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>, args: Map<string, VarInfo>): ExpressionTypeEnvironment {
        return new ExpressionTypeEnvironment(binds, new Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>(), new Map<string, VarInfo>(), argpcodes, args, [], new TIRInvalidExpression(SourceInfo.implicitSourceInfo(), "None"), ResolvedType.createInvalid());
    }

    static createInitialEnvForLiteralEval(binds: TemplateBindScope): ExpressionTypeEnvironment {
        return new ExpressionTypeEnvironment(binds, new Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>(), new Map<string, VarInfo>(), new Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>(), new Map<string, VarInfo>(), [], new TIRInvalidExpression(SourceInfo.implicitSourceInfo(), "None"), ResolvedType.createInvalid());
    }

    createFreshEnvExpressionFrom(): ExpressionTypeEnvironment {
        return new ExpressionTypeEnvironment(this.binds, this.capturedpcodes, this.capturedvars, this.argpcodes, this.args, this.locals, new TIRInvalidExpression(SourceInfo.implicitSourceInfo(), "None"), ResolvedType.createInvalid());
    }

    setResultExpressionInfo(exp: TIRExpression, trepr: ResolvedType): ExpressionTypeEnvironment {
       return new ExpressionTypeEnvironment(this.binds, this.capturedpcodes, this.capturedvars, this.argpcodes, this.args, this.locals, exp, trepr);
    }

    pushBinderFrame(binder: string, btype: ResolvedType): ExpressionTypeEnvironment {
        const nframe = new Map<string, VarInfo>([[binder, new VarInfo(btype, true, true)]]);
        return new ExpressionTypeEnvironment(this.binds, this.capturedpcodes, this.capturedvars, this.argpcodes, this.args, [...this.locals, nframe], new TIRInvalidExpression(SourceInfo.implicitSourceInfo(), "None"), ResolvedType.createInvalid());
    }

    popBinderFrame() {
        return new ExpressionTypeEnvironment(this.binds, this.capturedpcodes, this.capturedvars, this.argpcodes, this.args, this.locals.slice(0, this.locals.length - 1), this.expressionResult, this.trepr);
    }
}

class StatementTypeEnvironment {
    readonly binds: TemplateBindScope;
    readonly capturedpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>;
    readonly capturedvars: Map<string, VarInfo>;

    readonly argpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>;
    readonly args: Map<string, VarInfo>;
    readonly locals: Map<string, VarInfo>[];
    
    readonly isDeadFlow: boolean;

    private constructor(binds: TemplateBindScope, capturedpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>, capturedvars: Map<string, VarInfo>, argpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>, args: Map<string, VarInfo>, locals: Map<string, VarInfo>[], isDeadFlow: boolean) {
        this.binds = binds;
        this.capturedpcodes = capturedpcodes;
        this.capturedvars = capturedvars;

        this.argpcodes = argpcodes;;
        this.args = args;
        this.locals = locals;

        this.isDeadFlow = isDeadFlow;
    }

    addVar(name: string, isConst: boolean, dtype: ResolvedType, isDefined: boolean): StatementTypeEnvironment {
        let localcopy = (this.locals as Map<string, VarInfo>[]).map((frame) => new Map<string, VarInfo>(frame));
        localcopy[localcopy.length - 1].set(name, new VarInfo(dtype, isConst, isDefined));

        return new StatementTypeEnvironment(this.binds, this.capturedpcodes, this.capturedvars, this.argpcodes, this.args, localcopy, false);
    }

    setVar(name: string): StatementTypeEnvironment {
        if (this.getLocalVarInfo(name) !== undefined) {
            const oldv = this.lookupLocalVar(name) as VarInfo;
            const nv = new VarInfo(oldv.declaredType, oldv.isConst, true);

            let localcopy = (this.locals as Map<string, VarInfo>[]).map((frame) => frame.has(name) ? new Map<string, VarInfo>(frame).set(name, nv) : new Map<string, VarInfo>(frame));
            return new StatementTypeEnvironment(this.binds, this.capturedpcodes, this.capturedvars, this.argpcodes, this.args, localcopy, false);
        }
        else {
            const oldv = this.args.get(name) as VarInfo;
            const nv = new VarInfo(oldv.declaredType, oldv.isConst, true);

            const argscopy = new Map<string, VarInfo>(this.args as Map<string, VarInfo>).set(name, nv);
            return new StatementTypeEnvironment(this.binds, this.capturedpcodes, this.capturedvars, this.argpcodes, argscopy, this.locals, false);
        }
    }

    setVarFlowType(name: string, newtype: ResolvedType): StatementTypeEnvironment {
        const oldv = this.lookupLocalVar(name) as VarInfo;

        let argscopy = new Map<string, VarInfo>(this.args);
        if(argscopy.has(name)) {
            argscopy.set(name, new VarInfo(newtype, oldv.isConst, true));
        }

        let localcopy = (this.locals as Map<string, VarInfo>[]).map((frame) => {
            let nf = new Map<string, VarInfo>(frame);
            if(nf.has(name)) {
                nf.set(name, new VarInfo(newtype, oldv.isConst, true));
            }

            return nf;
        });
           
        return new StatementTypeEnvironment(this.binds, this.capturedpcodes, this.capturedvars, this.argpcodes, argscopy, localcopy, false);
    }

    endOfExecution(): StatementTypeEnvironment {
        return new StatementTypeEnvironment(this.binds, this.capturedpcodes, this.capturedvars, this.argpcodes, this.args, this.locals, true);
    }

    private getLocalVarInfo(name: string): VarInfo | undefined {
        const locals = this.locals as Map<string, VarInfo>[];
        for (let i = locals.length - 1; i >= 0; --i) {
            if (locals[i].has(name)) {
                return (locals[i].get(name) as VarInfo);
            }
        }

        return undefined;
    }

    lookupLocalVar(name: string): VarInfo | null {
        return this.getLocalVarInfo(name) || (this.args.get(name) || null);
    }

    lookupCapturedVar(name: string): VarInfo | null {
        return this.capturedvars.get(name) || null;
    }

    lookupArgPCode(name: string): {pcode: TIRCodePack, ftype: ResolvedFunctionType} | null {
        return this.argpcodes.get(name) || null;
    }

    lookupCapturedPCode(name: string): {pcode: TIRCodePack, ftype: ResolvedFunctionType} | null {
        return this.capturedpcodes.get(name) || null;
    }

    hasNormalFlow(): boolean {
        return !this.isDeadFlow;
    }

    static createInitialEnvForStatementEval(binds: TemplateBindScope, capturedpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>, capturedvars: Map<string, VarInfo>, argpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>, args: Map<string, VarInfo>, locals: Map<string, VarInfo>[]): StatementTypeEnvironment {
        return new StatementTypeEnvironment(binds, capturedpcodes, capturedvars, argpcodes, args, locals, false);
    }

    static createInitialEnvForStdBodyEval(binds: TemplateBindScope, argpcodes: Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>, args: Map<string, VarInfo>): StatementTypeEnvironment {
        return new StatementTypeEnvironment(binds, new Map<string, {pcode: TIRCodePack, ftype: ResolvedFunctionType}>(), new Map<string, VarInfo>(), argpcodes, args, [], false);
    }

    createInitialEnvForExpressionEval(): ExpressionTypeEnvironment {
        return ExpressionTypeEnvironment.createInitialEnvForExpressionEval(this.binds, this.capturedpcodes, this.capturedvars, this.argpcodes, this.args, this.locals);
    }

    pushLocalScope(): StatementTypeEnvironment {
        const localscopy = [...(this.locals as Map<string, VarInfo>[]), new Map<string, VarInfo>()];
        return new StatementTypeEnvironment(this.binds, this.capturedpcodes, this.capturedvars, this.argpcodes, this.args, localscopy, this.isDeadFlow);
    }

    popLocalScope(): StatementTypeEnvironment {
        const localscopy = (this.locals as Map<string, VarInfo>[]).slice(0, -1);
        return new StatementTypeEnvironment(this.binds, this.capturedpcodes, this.capturedvars, this.argpcodes, this.args, localscopy, this.isDeadFlow);
    }

    updateFlowAtJoin(remap: Map<string, ResolvedType>, rflows: StatementTypeEnvironment[]): StatementTypeEnvironment {
        let rargs = new Map<string, VarInfo>();
        this.args.forEach((ai, an) => {
            rargs.set(an, ai.updateTypeAndDef(remap.get(an) as ResolvedType, true));
        });

        const rlocals = this.locals.map((lf) => {
            let nlf = new Map<string, VarInfo>();
            lf.forEach((vi, vn) => {
                const mustdef = vi.mustDefined || rflows.every((ff) => (ff.lookupLocalVar(vn) as VarInfo).mustDefined);
                nlf.set(vn, vi.updateTypeAndDef(remap.get(vn) as ResolvedType, mustdef));
            });
            return nlf;
        });

        return new StatementTypeEnvironment(this.binds, this.capturedpcodes, this.capturedvars, this.argpcodes, rargs, rlocals, false);
    }
}

export {
    VarInfo, TemplateBindingScope
};
