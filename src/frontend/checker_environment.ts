import assert from "node:assert";

import { TypeSignature } from "./type.js";
import { BinderInfo } from "./body.js";

class VarInfo {
    readonly srcname: string;
    readonly scopename: string;
    readonly decltype: TypeSignature;
    readonly itype: TypeSignature;

    readonly isConst: boolean;
    readonly mustDefined: boolean;
    readonly isRef: boolean;

    constructor(srcname: string, scopename: string, decltype: TypeSignature, itype: TypeSignature, isConst: boolean, mustDefined: boolean, isRef: boolean) {
        this.srcname = srcname;
        this.scopename = scopename;
        this.decltype = decltype;
        this.itype = itype;

        this.isConst = isConst;
        this.mustDefined = mustDefined;
        this.isRef = isRef;
    }

    updateType(ttype: TypeSignature): VarInfo {
        return new VarInfo(this.srcname, this.scopename, this.decltype, ttype, this.isConst, this.mustDefined, this.isRef);
    }

    updateDefine(): VarInfo {
        return new VarInfo(this.srcname, this.scopename, this.decltype, this.itype, this.isConst, true, this.isRef);
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

class TypeEnvironment {
    readonly normalflow: boolean;
    readonly returnflow: boolean;
    readonly parent: TypeEnvironment | undefined;

    readonly args: VarInfo[];
    readonly declReturnType: TypeSignature;
    readonly inferReturn: TypeInferContext;

    readonly locals: VarInfo[][];

    constructor(normalflow: boolean, returnflow: boolean, parent: TypeEnvironment | undefined, args: VarInfo[], returnType: TypeSignature, inferctx: TypeInferContext, locals: VarInfo[][]) {
        this.normalflow = normalflow;
        this.returnflow = returnflow;
        this.parent = parent;

        this.args = args;
        this.declReturnType = returnType;
        this.inferReturn = inferctx;

        this.locals = locals;
    }

    private static cloneLocals(locals: VarInfo[][]): VarInfo[][] {
        return locals.map((l) => [...l]);
    }

    static createInitialStdEnv(args: VarInfo[], declReturnType: TypeSignature, inferReturn: TypeInferContext): TypeEnvironment {
        return new TypeEnvironment(true, false, undefined, args, declReturnType, inferReturn, [[]]);
    }

    static createInitialLambdaEnv(args: VarInfo[], declReturnType: TypeSignature, inferReturn: TypeInferContext, enclosing: TypeEnvironment): TypeEnvironment {
        return new TypeEnvironment(true, false, enclosing, args, declReturnType, inferReturn, [[]]);
    }

    private getBindScopeDepth(vname: string): number {
        let depth = 0;

        for(let i = this.locals.length - 1; i >= 0; i--) {
            for(let j = 0; j < this.locals[i].length; j++) {
                if(this.locals[i][j].srcname === vname) {
                    depth++;
                }
            }
        }

        let pp = this.parent;
        while(pp !== undefined) {
            depth += pp.getBindScopeDepth(vname);
            pp = pp.parent;
        }

        return depth;
    }

    getBindScopeName(vname: string): string {
        const depth = this.getBindScopeDepth(vname);
        return vname + (depth > 0 ? ("$" + depth) : "");
    }

    resolveLambdaCaptureVarInfoFromSrcName(vname: string): VarInfo | undefined {
        const localdef = this.resolveLocalVarInfoFromSrcName(vname);
        if(localdef !== undefined) {
            return localdef;
        }

        return this.parent !== undefined ? this.parent.resolveLambdaCaptureVarInfoFromSrcName(vname) : undefined;
    }

    resolveLocalVarInfoFromSrcName(vname: string): VarInfo | undefined {
        for(let i = this.locals.length - 1; i >= 0; i--) {
            for(let j = 0; j < this.locals[i].length; j++) {
                if(this.locals[i][j].srcname === vname) {
                    return this.locals[i][j];
                }
            }
        }

        return this.args.find((v) => v.srcname === vname);
    }

    resolveLocalVarInfoFromScopeName(vname: string): VarInfo | undefined {
        for(let i = this.locals.length - 1; i >= 0; i--) {
            for(let j = 0; j < this.locals[i].length; j++) {
                if(this.locals[i][j].scopename === vname) {
                    return this.locals[i][j];
                }
            }
        }

        return this.args.find((v) => v.srcname === vname);
    }

    addLocalVar(vname: string, vtype: TypeSignature, isConst: boolean, mustDefined: boolean): TypeEnvironment {
        let newlocals = TypeEnvironment.cloneLocals(this.locals);
        newlocals[newlocals.length - 1].push(new VarInfo(vname, vname, vtype, vtype, isConst, mustDefined, false));

        return new TypeEnvironment(this.normalflow, this.returnflow, this.parent, [...this.args], this.declReturnType, this.inferReturn, newlocals);
    }

    addLocalVarSet(vars: {name: string, vtype: TypeSignature}[], isConst: boolean): TypeEnvironment {
        let newlocals = TypeEnvironment.cloneLocals(this.locals);
        const newvars = vars.map((v) => new VarInfo(v.name, v.name, v.vtype, v.vtype, isConst, true, false));
        newlocals[newlocals.length - 1].push(...newvars);

        return new TypeEnvironment(this.normalflow, this.returnflow, this.parent, [...this.args], this.declReturnType, this.inferReturn, newlocals);
    }

    assignLocalVariable(vname: string): TypeEnvironment {
        let locals: VarInfo[][] = [];
        for(let i = this.locals.length - 1; i >= 0; i--) {
            let frame: VarInfo[] = [];
            for(let j = 0; j < this.locals[i].length; j++) {
                if(this.locals[i][j].srcname !== vname) {
                    frame.push(this.locals[i][j]);
                }
                else {
                    frame.push(this.locals[i][j].updateDefine());
                }
            }

            locals = [frame, ...locals];
        }

        return new TypeEnvironment(this.normalflow, this.returnflow, this.parent, [...this.args], this.declReturnType, this.inferReturn, locals);
    }

    retypeLocalVariable(vname: string, ttype: TypeSignature): TypeEnvironment {
        let locals: VarInfo[][] = [];
        for(let i = this.locals.length - 1; i >= 0; i--) {
            let frame: VarInfo[] = [];
            for(let j = 0; j < this.locals[i].length; j++) {
                if(this.locals[i][j].srcname !== vname) {
                    frame.push(this.locals[i][j]);
                }
                else {
                    frame.push(this.locals[i][j].updateType(ttype));
                }
            }

            locals = [frame, ...locals];
        }

        let reflowargs: VarInfo[] = [];
        for(let i = 0; i < this.args.length; i++) {
            if(this.args[i].srcname !== vname) {
                reflowargs.push(this.args[i]);
            }
            else {
                reflowargs.push(this.args[i].updateType(ttype));
            }
        }

        return new TypeEnvironment(this.normalflow, this.returnflow, this.parent, reflowargs, this.declReturnType, this.inferReturn, locals);
    }

    setDeadFlow(): TypeEnvironment {
        return new TypeEnvironment(false, false, this.parent, [...this.args], this.declReturnType, this.inferReturn, TypeEnvironment.cloneLocals(this.locals));
    }

    setReturnFlow(): TypeEnvironment {
        return new TypeEnvironment(false, true, this.parent, [...this.args], this.declReturnType, this.inferReturn, TypeEnvironment.cloneLocals(this.locals));
    }

    pushNewLocalScope(): TypeEnvironment {
        return new TypeEnvironment(this.normalflow, this.returnflow, this, [...this.args], this.declReturnType, this.inferReturn, [...TypeEnvironment.cloneLocals(this.locals), []]);
    }

    pushNewLocalBinderScope(vname: string, scopename: string, vtype: TypeSignature): TypeEnvironment {
        return new TypeEnvironment(this.normalflow, this.returnflow, this, [...this.args], this.declReturnType, this.inferReturn, [...TypeEnvironment.cloneLocals(this.locals), [new VarInfo(vname, scopename, vtype, vtype, true, true, false)]]);
    }

    popLocalScope(): TypeEnvironment {
        assert(this.locals.length > 0);
        return new TypeEnvironment(this.normalflow, this.returnflow, this.parent, [...this.args], this.declReturnType, this.inferReturn, TypeEnvironment.cloneLocals(this.locals).slice(0, this.locals.length - 1));
    }

    static mergeEnvironmentsSimple(origenv: TypeEnvironment, ...envs: TypeEnvironment[]): TypeEnvironment {
        let locals: VarInfo[][] = [];
        const normalenvs = envs.filter((e) => e.normalflow);
        for(let i = 0; i < origenv.locals.length; i++) {
            let frame: VarInfo[] = [];

            for(let j = 0; j < origenv.locals[i].length; j++) {
                const mdef = normalenvs.every((e) => (e.resolveLocalVarInfoFromScopeName(origenv.locals[i][j].scopename) as VarInfo).mustDefined);
                frame.push(new VarInfo(origenv.locals[i][j].srcname, origenv.locals[i][j].scopename, origenv.locals[i][j].decltype, origenv.locals[i][j].itype, origenv.locals[i][j].isConst, mdef, origenv.locals[i][j].isRef));
            }

            locals.push(frame);
        }

        const normalflow = envs.some((e) => e.normalflow);
        const returnflow = envs.every((e) => e.returnflow);
        return new TypeEnvironment(normalflow, returnflow, origenv.parent, [...origenv.args], origenv.declReturnType, origenv.inferReturn, locals);
    }

    static mergeEnvironmentsOptBinderFlow(origenv: TypeEnvironment, binfo: BinderInfo, refinetype: TypeSignature | undefined, ...envs: TypeEnvironment[]): TypeEnvironment {
        const menv = TypeEnvironment.mergeEnvironmentsSimple(origenv, ...envs);

        if(!binfo.refineonfollow || refinetype === undefined) {
            return menv;
        }
        else {
            const refinevar = binfo.scopename;
            return menv.retypeLocalVariable(refinevar.slice(1), refinetype)
        }
    }
}

export {
    VarInfo,
    TypeInferContext, SimpleTypeInferContext, EListStyleTypeInferContext,
    TypeEnvironment
};
