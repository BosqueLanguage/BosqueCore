import assert from "node:assert";

import { TypeSignature } from "./type.js";

class VarInfo {
    readonly srcname: string;
    readonly decltype: TypeSignature;

    readonly vkind: "ref" | "out" | "out?" | "inout" | "let" | "var";
    readonly mustDefined: boolean;

    constructor(srcname: string, decltype: TypeSignature, vkind: "ref" | "out" | "out?" | "inout" | "let" | "var", mustDefined: boolean) {
        this.srcname = srcname;
        this.decltype = decltype;
        this.vkind = vkind;
        this.mustDefined = mustDefined;
    }

    clone(): VarInfo {
        return new VarInfo(this.srcname, this.decltype, this.vkind, this.mustDefined);
    }

    updateDefine(): VarInfo {
        return new VarInfo(this.srcname, this.decltype, this.vkind, true);
    }
}

abstract class TypeInferContext {
    static asSimpleType(ctx: TypeInferContext | undefined): TypeSignature | undefined {
        if(ctx === undefined) {
            return undefined
        }
        else {
            return ctx instanceof SimpleTypeInferContext ? ctx.ttype : undefined;
        }
    }

    static asEListOptions(ctx: TypeInferContext | undefined): (TypeSignature | undefined)[] | undefined {
        if(ctx === undefined) {
            return undefined
        }
        else {
            return ctx instanceof EListStyleTypeInferContext ? ctx.elist : undefined;
        }
    }
}

class SimpleTypeInferContext extends TypeInferContext {
    readonly ttype: TypeSignature;

    constructor(ttype: TypeSignature) {
        super();
        this.ttype = ttype;
    }
}

class EListStyleTypeInferContext extends TypeInferContext {
    readonly elist: (TypeSignature | undefined)[];

    constructor(elist: (TypeSignature | undefined)[]) {
        super();
        this.elist = elist;
    }
}

class LocalScope {
    readonly locals: VarInfo[];
    
    readonly binderscope: boolean;
    readonly accessed: Set<string>; //only for binder scopes

    constructor(binderscope: boolean, locals: VarInfo[], accessed: Set<string>) {
        this.binderscope = binderscope;
        this.locals = locals;
        this.accessed = accessed;
    }

    clone(): LocalScope {
        return new LocalScope(this.binderscope, [...this.locals.map((v) => v.clone())], new Set<string>(this.accessed));
    }

    resolveLocalVarInfoFromSrcName(vname: string): VarInfo | undefined {
        const vinfo = this.locals.find((v) => v.srcname === vname);
        if(vinfo !== undefined && this.binderscope) {
            this.accessed.add(vname);
        }

        return vinfo
    }

    assignLocalVariable(vname: string): [LocalScope, boolean] {
        const vidx = this.locals.findIndex((v) => v.srcname === vname);
        if(vidx === -1) {
            return [this, false];
        }
        else {
            let newlocals = [...this.locals];
            newlocals[vidx] = newlocals[vidx].updateDefine();
            return [new LocalScope(this.binderscope, newlocals, this.accessed), true];
        }
    }

    static mergeLocalScopes(...envs: LocalScope[]): LocalScope {
        let locals: VarInfo[] = [];
        for(let i = 0; i < envs[0].locals.length; i++) {
            const mdef = envs.every((e) => e.locals[i].mustDefined);
            locals.push(new VarInfo(envs[0].locals[i].srcname, envs[0].locals[i].decltype, envs[0].locals[i].vkind, mdef));
        }
        
        let baccess = new Set<string>();
        for(let i = 0; i < envs.length; i++) {
            baccess = new Set<string>([...baccess, ...envs[i].accessed]);
        }

        return new LocalScope(envs[0].binderscope, locals, baccess);
    }
}


class TypeTestBindInfo {
    readonly guardidx: number;
    readonly bname: string;

    readonly ttrue: TypeSignature | undefined;
    readonly tfalse: TypeSignature | undefined;

    constructor(guardidx: number, bname: string, ttrue: TypeSignature | undefined, tfalse: TypeSignature | undefined) {
        this.guardidx = guardidx;
        this.bname = bname;
        this.ttrue = ttrue;
        this.tfalse = tfalse;
    }

    notop(): TypeTestBindInfo {
        return new TypeTestBindInfo(this.guardidx, this.bname, this.tfalse, this.ttrue);
    }
}

class TypeResultWRefVarInfoResult {
    readonly tsig: TypeSignature;
    readonly setcondout: {ttrue: string[], tfalse: string[]};
    readonly modified: string[];
    readonly bbinds: TypeTestBindInfo[] = [];

    constructor(tsig: TypeSignature, setcondout: {ttrue: string[], tfalse: string[]}, modified: string[], bbinds: TypeTestBindInfo[]) {
        this.tsig = tsig;
        this.setcondout = setcondout;
        this.modified = modified;
        this.bbinds = bbinds;
    }

    static makeNoRefResult(tsig: TypeSignature): TypeResultWRefVarInfoResult {
        return new TypeResultWRefVarInfoResult(tsig, {ttrue: [], tfalse: []}, [], []);
    }

    static merge(results: TypeResultWRefVarInfoResult[]): TypeResultWRefVarInfoResult {
        assert(results.length > 0);

        const ttrue = new Set<string>();
        const tfalse = new Set<string>();
        const modified = new Set<string>();
        const bbinds: TypeTestBindInfo[] = [];

        for(let i = 0; i < results.length; i++) {
            results[i].setcondout.ttrue.forEach((v) => ttrue.add(v));
            results[i].setcondout.tfalse.forEach((v) => tfalse.add(v));
            results[i].modified.forEach((v) => modified.add(v));
            bbinds.push(...results[i].bbinds);
        }

        return new TypeResultWRefVarInfoResult(
            results[0].tsig,
            {ttrue: [...ttrue], tfalse: [...tfalse]},
            [...modified],
            bbinds
        );
    }
}

class TypeEnvironment {
    readonly declReturnType: TypeSignature;
    readonly inferReturn: TypeInferContext;

    readonly isnormalflow: boolean;

    readonly parent: TypeEnvironment | undefined; //undefined for normal scopes and set for lambda scopes
    readonly lcaptures: {vname: string, vtype: TypeSignature, scopeidx: number}[]; //only set for lambda scopes

    readonly args: VarInfo[];
    readonly locals: LocalScope[];

    constructor(declReturnType: TypeSignature, inferReturn: TypeInferContext, isnormalflow: boolean, parent: TypeEnvironment | undefined, lcaptures: {vname: string, vtype: TypeSignature, scopeidx: number}[], args: VarInfo[], locals: LocalScope[]) {
        this.declReturnType = declReturnType;
        this.inferReturn = inferReturn;

        this.isnormalflow = isnormalflow;

        this.parent = parent;
        this.lcaptures = lcaptures;
        
        this.args = args;
        this.locals = locals;
    }

    static createInitialStdEnv(declReturnType: TypeSignature, inferReturn: TypeInferContext,args: VarInfo[]): TypeEnvironment {
        return new TypeEnvironment(declReturnType, inferReturn, true, undefined, [], args, [new LocalScope(false, [], new Set<string>())]);
    }

    static createInitialLambdaEnv(declReturnType: TypeSignature, inferReturn: TypeInferContext, args: VarInfo[], enclosing: TypeEnvironment): TypeEnvironment {
        return new TypeEnvironment(declReturnType, inferReturn, true, enclosing, [], args, [new LocalScope(false, [], new Set<string>())]);
    }

    cloneEnvironment(): TypeEnvironment {
        return new TypeEnvironment(this.declReturnType, this.inferReturn, this.isnormalflow, this.parent, [...this.lcaptures], [...this.args], [...this.locals].map((l) => l.clone()));
    }

    resolveLambdaCaptureVarInfoFromSrcName(vname: string): [VarInfo, number] | undefined {
        const localdef = this.resolveLocalVarInfoFromSrcName(vname);
        if(localdef !== undefined) {
            return [localdef, 0];
        }

        if(this.parent === undefined) {
            return undefined;
        }

        const pcapture = this.parent.resolveLambdaCaptureVarInfoFromSrcName(vname);
        if(pcapture === undefined) {
            return undefined;
        }

        const [cinfo, cidx] = pcapture;
        this.lcaptures.push({vname: cinfo.srcname, vtype: cinfo.decltype, scopeidx: cidx + 1});
        return [cinfo, cidx + 1];
    }

    resolveLocalVarInfoFromSrcName(vname: string): VarInfo | undefined {
        for(let i = this.locals.length - 1; i >= 0; i--) {
            const vinfo = this.locals[i].resolveLocalVarInfoFromSrcName(vname);
            if(vinfo !== undefined) {
                return vinfo;
            }
        }

        return this.args.find((v) => v.srcname === vname);
    }

    isLocalVariableAParameter(vname: string): boolean {
        return this.args.some((v) => v.srcname === vname);
    }

    addLocalVar(vname: string, vtype: TypeSignature, vkind: "let" | "ref" | "var", mustDefined: boolean): TypeEnvironment {
        let newlocals = [...this.locals.slice(0, this.locals.length - 1), this.locals[this.locals.length - 1].clone()];
        newlocals[newlocals.length - 1].locals.push(new VarInfo(vname, vtype, vkind, mustDefined));

        return new TypeEnvironment(this.declReturnType, this.inferReturn, this.isnormalflow, this.parent, this.lcaptures, this.args, newlocals);
    }

    addLocalVarSet(vars: {name: string, vtype: TypeSignature}[], vkind: "let" | "ref" | "var"): TypeEnvironment {
        let newlocals = [...this.locals.slice(0, this.locals.length - 1), this.locals[this.locals.length - 1].clone()];
        const newvars = vars.map((v) => new VarInfo(v.name, v.vtype, vkind, true));
        newlocals[newlocals.length - 1].locals.push(...newvars);

        return new TypeEnvironment(this.declReturnType, this.inferReturn, this.isnormalflow, this.parent, this.lcaptures, this.args, newlocals);
    }

    assignLocalVariable(vname: string): TypeEnvironment {
        let locals: LocalScope[] = [];
        let assigned = false;
        for(let i = this.locals.length - 1; i >= 0; i--) {
            if(assigned) {
                locals.push(this.locals[i]);
            }
            else {
                const [newframe, wasassigned] = this.locals[i].assignLocalVariable(vname);
                locals.push(newframe);
                assigned = wasassigned;
            };
        }

        return new TypeEnvironment(this.declReturnType, this.inferReturn, this.isnormalflow, this.parent, this.lcaptures, this.args, locals);
    }

    setDeadFlow(): TypeEnvironment {
        return new TypeEnvironment(this.declReturnType, this.inferReturn, false, this.parent, this.lcaptures, this.args, this.locals);
    }

    setReturnFlow(): TypeEnvironment {
        return new TypeEnvironment(this.declReturnType, this.inferReturn, false, this.parent, this.lcaptures, this.args, this.locals);
    }

    setYieldFlow(): TypeEnvironment {
        return new TypeEnvironment(this.declReturnType, this.inferReturn, false, this.parent, this.lcaptures, this.args, this.locals);
    }

    pushNewLocalScope(): TypeEnvironment {
        return new TypeEnvironment(this.declReturnType, this.inferReturn, this.isnormalflow, this.parent, this.lcaptures, this.args, [...this.locals, new LocalScope(false, [], new Set<string>())]);
    }

    pushNewLocalBinderScope(vname: string, vtype: TypeSignature): TypeEnvironment {
        return new TypeEnvironment(this.declReturnType, this.inferReturn, this.isnormalflow, this, this.lcaptures, this.args, [...this.locals, new LocalScope(false, [new VarInfo(vname, vtype, "let", true)], new Set<string>())]);
    }

    popLocalScope(): [TypeEnvironment, LocalScope] {
        assert(this.locals.length > 0);
        return [new TypeEnvironment(this.declReturnType, this.inferReturn, this.isnormalflow, this.parent, this.lcaptures, [...this.args], [...this.locals].slice(0, this.locals.length - 1)), this.locals[this.locals.length - 1]];
    }

    static mergeEnvironmentsSimple(origenv: TypeEnvironment, ...envs: TypeEnvironment[]): TypeEnvironment {
        let locals: LocalScope[] = [];
        const normalenvs = envs.filter((e) => e.isnormalflow);
        for(let i = 0; i < origenv.locals.length; i++) {
            locals.push(LocalScope.mergeLocalScopes(...normalenvs.map((e) => e.locals[i])));
        }

        let lcaptures: {vname: string, vtype: TypeSignature, scopeidx: number}[] = [...origenv.lcaptures];
        for(let i = 0; i < envs.length; i++) {
            for(let j = 0; j < envs[i].lcaptures.length; j++) {
                const cinfo = envs[i].lcaptures[j];
                if(!lcaptures.some((c) => c.vname === cinfo.vname && c.scopeidx === cinfo.scopeidx)) {
                    lcaptures.push(cinfo);
                }
            }
        }

        const normalflow = envs.some((e) => e.isnormalflow);
        return new TypeEnvironment(origenv.declReturnType, origenv.inferReturn, normalflow, origenv.parent, lcaptures, [...origenv.args], locals);
    }

    generateBranchFlows(ttre: TypeResultWRefVarInfoResult): [TypeEnvironment, TypeEnvironment] {
        let tenv = this.cloneEnvironment();
        let fenv = this.cloneEnvironment();
            
        for(let i = 0; i < ttre.bbinds.length; i++) {
            const bind = ttre.bbinds[i];
            if(bind.ttrue !== undefined) {
                tenv = tenv.addLocalVar(bind.bname, bind.ttrue, "let", true);
            }

            if(bind.tfalse !== undefined) {
                fenv = fenv.addLocalVar(bind.bname, bind.tfalse, "let", true);
            }
        }

        for(let i = 0; i < ttre.setcondout.ttrue.length; i++) {
            tenv = tenv.assignLocalVariable(ttre.setcondout.ttrue[i]);
        }
        for(let i = 0; i < ttre.setcondout.tfalse.length; i++) {
            fenv = fenv.assignLocalVariable(ttre.setcondout.tfalse[i]);
        }

        return [tenv, fenv];
    }
}

export {
    VarInfo,
    TypeInferContext, SimpleTypeInferContext, EListStyleTypeInferContext,
    TypeTestBindInfo, TypeResultWRefVarInfoResult,
    TypeEnvironment
};
