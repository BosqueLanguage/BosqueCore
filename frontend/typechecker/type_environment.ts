
import { ResolvedFunctionType, ResolvedType, TemplateBindScope } from "./resolved_type";
import { TIRCodePack, TIRExpression, TIRInvalidExpression } from "../tree_ir/tir_body";
import { SourceInfo } from "../build_decls";

enum FlowTypeTruthValue {
    True = "True",
    False = "False",
    Unknown = "Unknown"
}

class FlowTypeTruthOps {
    static join(...values: FlowTypeTruthValue[]): FlowTypeTruthValue {
        if (values.length === 0) {
            return FlowTypeTruthValue.Unknown;
        }

        const hasunknown = values.indexOf(FlowTypeTruthValue.Unknown) !== -1;
        const hastrue = values.indexOf(FlowTypeTruthValue.True) !== -1;
        const hasfalse = values.indexOf(FlowTypeTruthValue.False) !== -1;

        if (hasunknown || (hastrue && hasfalse)) {
            return FlowTypeTruthValue.Unknown;
        }
        else {
            return hastrue ? FlowTypeTruthValue.True : FlowTypeTruthValue.False;
        }
    }

    static maybeTrueValue(e: FlowTypeTruthValue): boolean {
        return (e === FlowTypeTruthValue.True || e === FlowTypeTruthValue.Unknown);
    }

    static maybeFalseValue(e: FlowTypeTruthValue): boolean {
        return (e === FlowTypeTruthValue.False || e === FlowTypeTruthValue.Unknown);
    }

    static logicalNot(e: FlowTypeTruthValue): FlowTypeTruthValue {
        if(e === FlowTypeTruthValue.True) {
            return FlowTypeTruthValue.False;
        }
        else if(e === FlowTypeTruthValue.False) {
            return FlowTypeTruthValue.True;
        }
        else {
            return FlowTypeTruthValue.Unknown;
        }
    }
}

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

class FlowTypeInfoOption {
    readonly tinfer: ResolvedType; //The inferred (refined) type that the value holds -- e.g. repr might be "Int | None" but infer is "Int" 
    readonly etruth: FlowTypeTruthValue;

    readonly expInferInfo: Map<string, {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue}>;

    constructor(tinfer: ResolvedType, etruth: FlowTypeTruthValue, expInferInfo: Map<string, {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue}>) {
        this.tinfer = tinfer;
        this.etruth = etruth;

        this.expInferInfo = expInferInfo;
    }

    static createInitial(): FlowTypeInfoOption[] {
        return [new FlowTypeInfoOption(ResolvedType.createInvalid(), FlowTypeTruthValue.Unknown, new Map<string, {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue}>())]; 
    }

    static createFrom(fti: FlowTypeInfoOption[]): FlowTypeInfoOption[] {
        return fti.map((fi) => new FlowTypeInfoOption(ResolvedType.createInvalid(), FlowTypeTruthValue.Unknown, fi.expInferInfo));
    }

    static equivInferMaps(mi1: Map<string, {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue}>, mi2: Map<string, {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue}>): boolean {
        if(mi1.size !== mi2.size) {
            return false;
        }

        let allok = true;
        mi1.forEach((v, k) => {
            if(!mi2.has(k)) {
                allok = false;
            }
            else {
                const v2 = mi2.get(k) as {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue};
                allok = allok && v.infertruth === v2.infertruth && v.infertype.isSameType(v2.infertype);
            }
        });

        return allok;
    }

    inferFlowInfo(expr: TIRExpression, tinfer: ResolvedType, etruth: FlowTypeTruthValue): FlowTypeInfoOption {
        const iinfo = new Map<string, {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue}>(this.expInferInfo).set(expr.expstr, { depvars: new Set<string>(expr.getUsedVars()), infertype: tinfer, infertruth: etruth});
        return new FlowTypeInfoOption(tinfer, this.etruth, iinfo);
    }

    clearVars(vars: string[]): FlowTypeInfoOption {
        let nei = new Map<string, {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue}>();
        this.expInferInfo.forEach((v, k) => {
            if(!vars.some((vv) => v.depvars.has(vv))) {
                nei.set(k, v);
            }
        });

        return new FlowTypeInfoOption(this.tinfer, this.etruth, nei);
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
    
    readonly flowinfo: FlowTypeInfoOption[];

    private constructor(binds: TemplateBindScope, pcodes: Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>, frozenVars: Set<string>, args: Map<string, VarInfo>, locals: Map<string, VarInfo>[], expressionResult: TIRExpression, trepr: ResolvedType, flowinfo: FlowTypeInfoOption[]) {
        this.binds = binds;
        this.pcodes = pcodes;

        this.frozenVars = frozenVars;
        this.args = args;
        this.locals = locals;

        this.expressionResult = expressionResult;
        this.trepr = trepr;
        this.flowinfo = flowinfo;
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

    static createInitialEnvForExpressionEval(binds: TemplateBindScope, pcodes: Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>, frozenVars: Set<string>, args: Map<string, VarInfo>, locals: Map<string, VarInfo>[], flows: FlowTypeInfoOption[]): ExpressionTypeEnvironment {
        return new ExpressionTypeEnvironment(binds, pcodes, frozenVars, args, locals, new TIRInvalidExpression(SourceInfo.implicitSourceInfo(), "None"), ResolvedType.createInvalid(), flows);
    }

    static createInitialEnvForEvalStandalone(binds: TemplateBindScope): ExpressionTypeEnvironment {
        return new ExpressionTypeEnvironment(binds, new Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>(), new Set<string>(), new Map<string, VarInfo>(), [], new TIRInvalidExpression(SourceInfo.implicitSourceInfo(), "None"), ResolvedType.createInvalid(), FlowTypeInfoOption.createInitial());
    }

    static createInitialEnvForEvalWArgs(binds: TemplateBindScope, args: Map<string, VarInfo>): ExpressionTypeEnvironment {
        return new ExpressionTypeEnvironment(binds, new Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>(), new Set<string>(), args, [], new TIRInvalidExpression(SourceInfo.implicitSourceInfo(), "None"), ResolvedType.createInvalid(), FlowTypeInfoOption.createInitial());
    }

    static createInitialEnvForEvalWArgsPCodes(binds: TemplateBindScope, pcodes: Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>, args: Map<string, VarInfo>): ExpressionTypeEnvironment {
        return new ExpressionTypeEnvironment(binds, pcodes, new Set<string>(), args, [], new TIRInvalidExpression(SourceInfo.implicitSourceInfo(), "None"), ResolvedType.createInvalid(), FlowTypeInfoOption.createInitial());
    }

    static createInitialEnvForLiteralEval(binds: TemplateBindScope): ExpressionTypeEnvironment {
        return new ExpressionTypeEnvironment(binds, new Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>(), new Set<string>(), new Map<string, VarInfo>(), [], new TIRInvalidExpression(SourceInfo.implicitSourceInfo(), "None"), ResolvedType.createInvalid(), FlowTypeInfoOption.createInitial());
    }

    createFreshEnvExpressionFrom(): ExpressionTypeEnvironment {
        return new ExpressionTypeEnvironment(this.binds, this.pcodes, this.frozenVars, this.args, this.locals, new TIRInvalidExpression(SourceInfo.implicitSourceInfo(), "None"), ResolvedType.createInvalid(), FlowTypeInfoOption.createFrom(this.flowinfo));
    }

    createFreshFlowEnvExpressionFrom(flows: FlowTypeInfoOption[]): ExpressionTypeEnvironment {
        return new ExpressionTypeEnvironment(this.binds, this.pcodes, this.frozenVars, this.args, this.locals, new TIRInvalidExpression(SourceInfo.implicitSourceInfo(), "None"), ResolvedType.createInvalid(), FlowTypeInfoOption.createFrom(flows));
    }

    setResultExpressionInfo(exp: TIRExpression, trepr: ResolvedType, finfo: FlowTypeInfoOption[]): ExpressionTypeEnvironment {
       return new ExpressionTypeEnvironment(this.binds, this.pcodes, this.frozenVars, this.args, this.locals, exp, trepr, finfo);
    }

    updateFromClearVars(ninfo: FlowTypeInfoOption[]): ExpressionTypeEnvironment {
        return new ExpressionTypeEnvironment(this.binds, this.pcodes, this.frozenVars, this.args, this.locals, this.expressionResult, this.trepr, ninfo);
    }
}

class StatementTypeEnvironment {
    readonly binds: TemplateBindScope;
    readonly pcodes: Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>;

    readonly frozenVars: Set<string>;
    readonly args: Map<string, VarInfo>;
    readonly locals: Map<string, VarInfo>[];
    
    readonly isDeadFlow: boolean;
    readonly flowinfo: Map<string, {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue}>;

    private constructor(binds: TemplateBindScope, pcodes: Map<string, {iscapture: boolean, pcode: TIRCodePack, ftype: ResolvedFunctionType}>, frozenVars: Set<string>, args: Map<string, VarInfo>, locals: Map<string, VarInfo>[], isDeadFlow: boolean, flowinfo: Map<string, {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue}>) {
        this.binds = binds;
        this.pcodes = pcodes;

        this.frozenVars = frozenVars;
        this.args = args;
        this.locals = locals;

        this.isDeadFlow = isDeadFlow;
        this.flowinfo = flowinfo;
    }

    getDefVarInfo(): string[] {
        const args = [...this.args].sort((a, b) => a[0].localeCompare(b[0])).map((vv) => vv[0]);
        const locals = this.locals.map((ll) => [...ll].sort((a, b) => a[0].localeCompare(b[0])).map((vv) => vv[0]));

        return args.concat(...locals);
    }

    addVar(name: string, isConst: boolean, dtype: ResolvedType, isDefined: boolean, cinfo: FlowTypeInfoOption | undefined): StatementTypeEnvironment {
        let localcopy = (this.locals as Map<string, VarInfo>[]).map((frame) => new Map<string, VarInfo>(frame));
        localcopy[localcopy.length - 1].set(name, new VarInfo(dtype, isConst, false, isDefined));

        const iinfo = cinfo !== undefined ? new Map<string, {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue}>(cinfo.expInferInfo).set(name, { depvars: new Set<string>(name), infertype: cinfo.tinfer, infertruth: FlowTypeTruthValue.Unknown}) : this.flowinfo;
     
        return new StatementTypeEnvironment(this.binds, this.pcodes, this.frozenVars, this.args, localcopy, false, iinfo);
    }

    setVar(name: string, cinfo: FlowTypeInfoOption): StatementTypeEnvironment {
        const oldv = this.lookupVar(name) as VarInfo;

        let localcopy = (this.locals as Map<string, VarInfo>[]).map((frame) => new Map<string, VarInfo>(frame));
        localcopy[localcopy.length - 1].set(name, new VarInfo(oldv.declaredType, false, false, true));
           
        const iinfo = new Map<string, {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue}>(cinfo.expInferInfo).set(name, { depvars: new Set<string>(name), infertype: cinfo.tinfer, infertruth: FlowTypeTruthValue.Unknown});
     
        return new StatementTypeEnvironment(this.binds, this.pcodes, this.frozenVars, this.args, localcopy, false, iinfo);
    }

    endOfExecution(): StatementTypeEnvironment {
        return new StatementTypeEnvironment(this.binds, this.pcodes, this.frozenVars, this.args, this.locals, true, this.flowinfo);
    }

    setFlowInfo(finfo: Map<string, {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue}>): StatementTypeEnvironment {
        const iinfo = new Map<string, {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue}>(finfo);
        return new StatementTypeEnvironment(this.binds, this.pcodes, this.frozenVars, this.args, this.locals, false, iinfo);
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
        return new StatementTypeEnvironment(binds, pcodes, frozenVars, args, locals, false, new Map<string, {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue}>());
    }

    createInitialEnvForExpressionEval(): ExpressionTypeEnvironment {
        const flows = [new FlowTypeInfoOption(ResolvedType.createInvalid(), FlowTypeTruthValue.Unknown, this.flowinfo)];
        return ExpressionTypeEnvironment.createInitialEnvForExpressionEval(this.binds, this.pcodes, this.frozenVars, this.args, this.locals, flows);
    }

    pushLocalScope(): StatementTypeEnvironment {
        const localscopy = [...(this.locals as Map<string, VarInfo>[]), new Map<string, VarInfo>()];
        return new StatementTypeEnvironment(this.binds, this.pcodes, this.frozenVars, this.args, localscopy, this.isDeadFlow, this.flowinfo);
    }

    popLocalScope(): StatementTypeEnvironment {
        const localscopy = (this.locals as Map<string, VarInfo>[]).slice(0, -1);
        let iinfo = new Map<string, {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue}>();
        [...this.flowinfo].forEach((fi) => {
            if([...fi[1].depvars].every((vv) => !this.locals[this.locals.length - 1].has(vv))) {
                iinfo.set(fi[0], fi[1]);
            }
        });

        return new StatementTypeEnvironment(this.binds, this.pcodes, this.frozenVars, this.args, localscopy, this.isDeadFlow, iinfo);
    }
}

export {
    FlowTypeTruthValue, FlowTypeTruthOps,
    VarInfo,
    FlowTypeInfoOption, ExpressionTypeEnvironment, StatementTypeEnvironment
};
