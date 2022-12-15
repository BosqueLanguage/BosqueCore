import * as assert from "assert";

import { ResolvedType, TemplateBindScope } from "./resolved_type";
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
    readonly bodyid: string;
    readonly binds: TemplateBindScope;
    readonly pcodes: Map<string, TIRCodePack>;

    readonly frozenVars: Set<string>;
    readonly args: Map<string, VarInfo>;
    readonly locals: Map<string, VarInfo>[];

    readonly expressionResult: TIRExpression;
    readonly trepr: ResolvedType; //The type of the expression (value representation)
    
    readonly flowinfo: FlowTypeInfoOption[];

    private constructor(bodyid: string, binds: TemplateBindScope, pcodes: Map<string, TIRCodePack>, frozenVars: Set<string>, args: Map<string, VarInfo>, locals: Map<string, VarInfo>[], expressionResult: TIRExpression, trepr: ResolvedType, flowinfo: FlowTypeInfoOption[]) {
        this.bodyid = bodyid;
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

    static createInitialEnvForExpressionEval(bodyid: string, binds: TemplateBindScope, pcodes: Map<string, TIRCodePack>, frozenVars: Set<string>, args: Map<string, VarInfo>, locals: Map<string, VarInfo>[], flows: FlowTypeInfoOption[]): ExpressionTypeEnvironment {
        return new ExpressionTypeEnvironment(bodyid, binds, pcodes, frozenVars, args, locals, new TIRInvalidExpression(SourceInfo.implicitSourceInfo(), "None"), ResolvedType.createInvalid(), flows);
    }

    static createInitialEnvForConstEval(bodyid: string, binds: TemplateBindScope, pcodes: Map<string, TIRCodePack>, args: Map<string, VarInfo>): ExpressionTypeEnvironment {
        return new ExpressionTypeEnvironment(bodyid, binds, pcodes, new Set<string>(), args, [], new TIRInvalidExpression(SourceInfo.implicitSourceInfo(), "None"), ResolvedType.createInvalid(), FlowTypeInfoOption.createInitial());
    }

    static createInitialEnvForLiteralEval(bodyid: string, binds: TemplateBindScope): ExpressionTypeEnvironment {
        return new ExpressionTypeEnvironment(bodyid, binds, new Map<string, TIRCodePack>(), new Set<string>(), new Map<string, VarInfo>(), [], new TIRInvalidExpression(SourceInfo.implicitSourceInfo(), "None"), ResolvedType.createInvalid(), FlowTypeInfoOption.createInitial());
    }

    createFreshEnvExpressionFrom(): ExpressionTypeEnvironment {
        return new ExpressionTypeEnvironment(this.bodyid, this.binds, this.pcodes, this.frozenVars, this.args, this.locals, new TIRInvalidExpression(SourceInfo.implicitSourceInfo(), "None"), ResolvedType.createInvalid(), FlowTypeInfoOption.createFrom(this.flowinfo));
    }

    createFreshFlowEnvExpressionFrom(flows: FlowTypeInfoOption[]): ExpressionTypeEnvironment {
        return new ExpressionTypeEnvironment(this.bodyid, this.binds, this.pcodes, this.frozenVars, this.args, this.locals, new TIRInvalidExpression(SourceInfo.implicitSourceInfo(), "None"), ResolvedType.createInvalid(), FlowTypeInfoOption.createFrom(flows));
    }

    setResultExpressionInfo(exp: TIRExpression, trepr: ResolvedType, finfo: FlowTypeInfoOption[]): ExpressionTypeEnvironment {
       return new ExpressionTypeEnvironment(this.bodyid, this.binds, this.pcodes, this.frozenVars, this.args, this.locals, exp, trepr, finfo);
    }

    updateFromClearVars(ninfo: FlowTypeInfoOption[]): ExpressionTypeEnvironment {
        return new ExpressionTypeEnvironment(this.bodyid, this.binds, this.pcodes, this.frozenVars, this.args, this.locals, this.expressionResult, this.trepr, ninfo);
    }
}

class StatementTypeEnvironment {
    readonly bodyid: string;
    readonly binds: TemplateBindScope;
    readonly pcodes: Map<string, TIRCodePack>;

    readonly frozenVars: Set<string>;
    readonly args: Map<string, VarInfo>;
    readonly locals: Map<string, VarInfo>[];
    
    readonly flowinfo: Map<string, {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue}>[];

    private constructor(bodyid: string, binds: TemplateBindScope, pcodes: Map<string, TIRCodePack>, frozenVars: Set<string>, args: Map<string, VarInfo>, locals: Map<string, VarInfo>[], flowinfo: Map<string, {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue}>[]) {
        this.bodyid = bodyid;
        this.binds = binds;
        this.pcodes = pcodes;

        this.frozenVars = frozenVars;
        this.args = args;
        this.locals = locals;

        this.flowinfo = flowinfo;
    }

    addVar(name: string, isConst: boolean, dtype: ResolvedType, isDefined: boolean, rhs: ExpressionTypeEnvironment | undefined): StatementTypeEnvironment {
        assert(this.flowinfo.length !== 0);

        let localcopy = (this.locals as Map<string, VarInfo>[]).map((frame) => new Map<string, VarInfo>(frame));
        localcopy[localcopy.length - 1].set(name, new VarInfo(dtype, isConst, false, isDefined));

        const iinfo = rhs !== undefined ? rhs.flowinfo.map((fi) => new Map<string, {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue}>(fi.expInferInfo).set(name, { depvars: new Set<string>(name), infertype: fi.tinfer, infertruth: fi.etruth})) : this.flowinfo;
     
        return new StatementTypeEnvironment(this.bodyid, this.binds, this.pcodes, this.frozenVars, this.args, localcopy, iinfo);
    }

    setVar(name: string, rhs: ExpressionTypeEnvironment): StatementTypeEnvironment {
        assert(this.flowinfo.length !== 0);

        const oldv = this.lookupVar(name) as VarInfo;

        let localcopy = (this.locals as Map<string, VarInfo>[]).map((frame) => new Map<string, VarInfo>(frame));
        localcopy[localcopy.length - 1].set(name, new VarInfo(oldv.declaredType, false, false, true));
           
        const iinfo = rhs.flowinfo.map((fi) => new Map<string, {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue}>(fi.expInferInfo).set(name, { depvars: new Set<string>(name), infertype: fi.tinfer, infertruth: fi.etruth}));
     
        return new StatementTypeEnvironment(this.bodyid, this.binds, this.pcodes, this.frozenVars, this.args, localcopy, iinfo);
    }

    endOfExecution(): StatementTypeEnvironment {
        return new StatementTypeEnvironment(this.bodyid, this.binds, this.pcodes, this.frozenVars, this.args, this.locals, []);
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

    static createInitialEnvForStatementEval(bodyid: string, binds: TemplateBindScope, pcodes: Map<string, TIRCodePack>, frozenVars: Set<string>, args: Map<string, VarInfo>, locals: Map<string, VarInfo>[]): StatementTypeEnvironment {
        return new StatementTypeEnvironment(bodyid, binds, pcodes, frozenVars, args, locals, [new Map<string, {depvars: Set<string>, infertype: ResolvedType, infertruth: FlowTypeTruthValue}>()]);
    }

    createInitialEnvForExpressionEval(): ExpressionTypeEnvironment {
        const flows = this.flowinfo.map((ff) => new FlowTypeInfoOption(ResolvedType.createInvalid(), FlowTypeTruthValue.Unknown, ff));
        return ExpressionTypeEnvironment.createInitialEnvForExpressionEval(this.bodyid, this.binds, this.pcodes, this.frozenVars, this.args, this.locals, flows);
    }
/*
    

    setAbort(): TypeEnvironment {
        assert(this.hasNormalFlow());
        return new TypeEnvironment(this.ikey, this.bodyid, this.terms, this.pcodes, this.args, undefined, this.inferResult, this.inferYield, this.expressionResult, this.returnResult, this.yieldResult, this.frozenVars);
    }

    setReturn(assembly: Assembly, rtype: ResolvedType): TypeEnvironment {
        assert(this.hasNormalFlow());
        const rrtype = this.returnResult !== undefined ? assembly.typeUpperBound([this.returnResult, rtype]) : rtype;
        return new TypeEnvironment(this.ikey, this.bodyid, this.terms, this.pcodes, this.args, undefined, this.inferResult, this.inferYield, this.expressionResult, rrtype, this.yieldResult, this.frozenVars);
    }

    setYield(assembly: Assembly, ytype: ResolvedType): TypeEnvironment {
        assert(this.hasNormalFlow());
        const rytype = this.yieldResult !== undefined ? assembly.typeUpperBound([this.yieldResult, ytype]) : ytype;
        return new TypeEnvironment(this.ikey, this.bodyid, this.terms, this.pcodes, this.args, undefined, this.inferResult, this.inferYield, this.expressionResult, this.returnResult, rytype, this.frozenVars);
    }

    pushLocalScope(): TypeEnvironment {
        assert(this.hasNormalFlow());
        let localscopy = [...(this.locals as Map<string, VarInfo>[]), new Map<string, VarInfo>()];
        return new TypeEnvironment(this.ikey, this.bodyid, this.terms, this.pcodes, this.args, localscopy, this.inferResult, this.inferYield, this.expressionResult, this.returnResult, this.yieldResult, this.frozenVars);
    }

    popLocalScope(): TypeEnvironment {
        let localscopy = this.locals !== undefined ? (this.locals as Map<string, VarInfo>[]).slice(0, -1) : undefined;
        return new TypeEnvironment(this.ikey, this.bodyid, this.terms, this.pcodes, this.args, localscopy, this.inferResult, this.inferYield, this.expressionResult, this.returnResult, this.yieldResult, this.frozenVars);
    }

    lookupPCode(pc: string): PCode | undefined {
        return this.pcodes.get(pc);
    }

    addVar(name: string, isConst: boolean, dtype: ResolvedType, isDefined: boolean, infertype: ResolvedType): TypeEnvironment {
        assert(this.hasNormalFlow());

        let localcopy = (this.locals as Map<string, VarInfo>[]).map((frame) => new Map<string, VarInfo>(frame));
        localcopy[localcopy.length - 1].set(name, new VarInfo(dtype, isConst, false, isDefined, infertype));

        return new TypeEnvironment(this.ikey, this.bodyid, this.terms, this.pcodes, this.args, localcopy, this.inferResult, this.inferYield, this.expressionResult, this.returnResult, this.yieldResult, this.frozenVars);
    }

    setVar(name: string, flowtype: ResolvedType): TypeEnvironment {
        assert(this.hasNormalFlow());

        const oldv = this.lookupVar(name) as VarInfo;
        const nv = oldv.assign(flowtype);

        let localcopy = (this.locals as Map<string, VarInfo>[]).map((frame) => frame.has(name) ? new Map<string, VarInfo>(frame).set(name, nv) : new Map<string, VarInfo>(frame));
        return new TypeEnvironment(this.ikey, this.bodyid, this.terms, this.pcodes, this.args, localcopy, this.inferResult, this.inferYield, this.expressionResult, this.returnResult, this.yieldResult, this.frozenVars);
    }

    setRefVar(name: string): TypeEnvironment {
        assert(this.hasNormalFlow());

        const oldv = this.lookupVar(name) as VarInfo;
        const nv = oldv.assign(oldv.declaredType);

        let localcopy = (this.locals as Map<string, VarInfo>[]).map((frame) => frame.has(name) ? new Map<string, VarInfo>(frame).set(name, nv) : new Map<string, VarInfo>(frame));
        return new TypeEnvironment(this.ikey, this.bodyid, this.terms, this.pcodes, this.args, localcopy, this.inferResult, this.inferYield, this.expressionResult, this.returnResult, this.yieldResult, this.frozenVars);
    }

    multiVarUpdate(allDeclared: [boolean, string, ResolvedType, ResolvedType][], allAssigned: [string, ResolvedType][]): TypeEnvironment {
        assert(this.hasNormalFlow());

        let nenv: TypeEnvironment = this;

        for (let i = 0; i < allDeclared.length; ++i) {
            const declv = allDeclared[i];
            nenv = nenv.addVar(declv[1], declv[0], declv[2], true, declv[3]);
        }

        for (let i = 0; i < allAssigned.length; ++i) {
            const assignv = allAssigned[i];
            nenv = nenv.setVar(assignv[0], assignv[1]);
        }

        return nenv;
    }

    getCurrentFrameNames(): string[] {
        let res: string[] = [];
        (this.locals as Map<string, VarInfo>[])[(this.locals as Map<string, VarInfo>[]).length - 1].forEach((v, k) => {
            res.push(k);
        });
        return res;
    }

    getAllLocalNames(): Set<string> {
        let names = new Set<string>();
        (this.locals as Map<string, VarInfo>[]).forEach((frame) => {
            frame.forEach((v, k) => {
                names.add(k);
            });
        });
        return names;
    }

    freezeVars(inferyield: ResolvedType | undefined): TypeEnvironment {
        assert(this.hasNormalFlow());

        let svars = new Set<string>();
        for (let i = 0; i < (this.locals as Map<string, VarInfo>[]).length; ++i) {
            (this.locals as Map<string, VarInfo>[])[i].forEach((v, k) => svars.add(k));
        }

        const iyeild = [...this.inferYield, inferyield];

        return new TypeEnvironment(this.ikey, this.bodyid, this.terms, this.pcodes, this.args, this.locals, this.inferResult, iyeild, this.expressionResult, this.returnResult, this.yieldResult, svars);
    }

    static join(assembly: Assembly, ...opts: TypeEnvironment[]): TypeEnvironment {
        assert(opts.length !== 0);

        if (opts.length === 1) {
            return opts[0];
        }
        else {
            const fopts = opts.filter((opt) => opt.locals !== undefined);

            let argnames: string[] = [];
            fopts.forEach((opt) => {
                (opt.args as Map<string, VarInfo>).forEach((v, k) => argnames.push(k));
            });

            let args = fopts.length !== 0 ? new Map<string, VarInfo>() : undefined;
            if (args !== undefined) {
                argnames.forEach((aname) => {
                    const vinfo = VarInfo.join(assembly, ...fopts.map((opt) => (opt.args as Map<string, VarInfo>).get(aname) as VarInfo));
                    (args as Map<string, VarInfo>).set(aname, vinfo);
                });
            }

            let locals = fopts.length !== 0 ? ([] as Map<string, VarInfo>[]) : undefined;
            if (locals !== undefined) {
                for (let i = 0; i < (fopts[0].locals as Map<string, VarInfo>[]).length; ++i) {
                    let localsi = new Map<string, VarInfo>();
                    (fopts[0].locals as Map<string, VarInfo>[])[i].forEach((v, k) => {
                        localsi.set(k, VarInfo.join(assembly, ...fopts.map((opt) => opt.lookupVar(k) as VarInfo)));
                    });

                    locals.push(localsi);
                }
            }

            const expresall = fopts.filter((opt) => opt.expressionResult !== undefined).map((opt) => opt.getExpressionResult());
            let expres: ExpressionReturnResult | undefined = undefined;
            if (expresall.length !== 0) {
                const retype = ValueType.join(assembly, ...expresall.map((opt) => opt.valtype));
                const rflow = FlowTypeTruthOps.join(...expresall.map((opt) => opt.truthval));
                const evar = expresall.every((ee) => ee.expvar === expresall[0].expvar) ? expresall[0].expvar : undefined;
                expres = new ExpressionReturnResult(retype, rflow, evar);
            }

            const rflow = opts.filter((opt) => opt.returnResult !== undefined).map((opt) => opt.returnResult as ResolvedType);
            const yflow = opts.filter((opt) => opt.yieldResult !== undefined).map((opt) => opt.yieldResult as ResolvedType);

            return new TypeEnvironment(opts[0].ikey, opts[0].bodyid, opts[0].terms, opts[0].pcodes, args, locals, opts[0].inferResult, opts[0].inferYield, expres, rflow.length !== 0 ? assembly.typeUpperBound(rflow) : undefined, yflow.length !== 0 ? assembly.typeUpperBound(yflow) : undefined, opts[0].frozenVars);
        }
    }

    */
}

export {
    FlowTypeTruthValue, FlowTypeTruthOps,
    VarInfo,
    FlowTypeInfoOption, ExpressionTypeEnvironment, StatementTypeEnvironment
};
