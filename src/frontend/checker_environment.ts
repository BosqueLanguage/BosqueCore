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

class TypeEnvironment {
    readonly normalflow: boolean;
    readonly returnflow: boolean;
    readonly parent: TypeEnvironment | undefined;

    readonly args: VarInfo[];

    readonly locals: VarInfo[][];

    constructor(normalflow: boolean, returnflow: boolean, parent: TypeEnvironment | undefined, args: VarInfo[], locals: VarInfo[][]) {
        this.normalflow = normalflow;
        this.returnflow = returnflow;
        this.parent = parent;

        this.args = args;

        this.locals = locals;
    }

    private static cloneLocals(locals: VarInfo[][]): VarInfo[][] {
        return locals.map((l) => [...l]);
    }

    static createInitialStdEnv(args: VarInfo[]): TypeEnvironment {
        return new TypeEnvironment(true, false, undefined, args, [[]]);
    }

    static createInitialLambdaEnv(args: VarInfo[], enclosing: TypeEnvironment): TypeEnvironment {
        return new TypeEnvironment(true, false, enclosing, args, [[]]);
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

    resolveLocalVarInfoFromSrcNameWithIsParam(vname: string): [VarInfo | undefined, boolean] {
        for(let i = this.locals.length - 1; i >= 0; i--) {
            for(let j = 0; j < this.locals[i].length; j++) {
                if(this.locals[i][j].srcname === vname) {
                    return [this.locals[i][j], false];
                }
            }
        }

        return [this.args.find((v) => v.srcname === vname), true];
    }

    addLocalVar(vname: string, vtype: TypeSignature, vkind: "let" | "ref" | "var", mustDefined: boolean): TypeEnvironment {
        let newlocals = TypeEnvironment.cloneLocals(this.locals);
        newlocals[newlocals.length - 1].push(new VarInfo(vname, vtype, vkind, mustDefined));

        return new TypeEnvironment(this.normalflow, this.returnflow, this.parent, [...this.args], newlocals);
    }

    addLocalVarSet(vars: {name: string, vtype: TypeSignature}[], vkind: "let" | "ref" | "var"): TypeEnvironment {
        let newlocals = TypeEnvironment.cloneLocals(this.locals);
        const newvars = vars.map((v) => new VarInfo(v.name, v.vtype, vkind, true));
        newlocals[newlocals.length - 1].push(...newvars);

        return new TypeEnvironment(this.normalflow, this.returnflow, this.parent, [...this.args], newlocals);
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

        return new TypeEnvironment(this.normalflow, this.returnflow, this.parent, [...this.args], locals);
    }

    setDeadFlow(): TypeEnvironment {
        return new TypeEnvironment(false, false, this.parent, [...this.args], TypeEnvironment.cloneLocals(this.locals));
    }

    setReturnFlow(): TypeEnvironment {
        return new TypeEnvironment(false, true, this.parent, [...this.args], TypeEnvironment.cloneLocals(this.locals));
    }

    pushNewLocalScope(): TypeEnvironment {
        return new TypeEnvironment(this.normalflow, this.returnflow, this, [...this.args], [...TypeEnvironment.cloneLocals(this.locals), []]);
    }

    pushNewLocalBinderScope(vname: string, vtype: TypeSignature): TypeEnvironment {
        return new TypeEnvironment(this.normalflow, this.returnflow, this, [...this.args], [...TypeEnvironment.cloneLocals(this.locals), [new VarInfo(vname, vtype, "let", true)]]);
    }

    popLocalScope(): TypeEnvironment {
        assert(this.locals.length > 0);
        return new TypeEnvironment(this.normalflow, this.returnflow, this.parent, [...this.args], TypeEnvironment.cloneLocals(this.locals).slice(0, this.locals.length - 1));
    }

    static mergeEnvironmentsSimple(origenv: TypeEnvironment, ...envs: TypeEnvironment[]): TypeEnvironment {
        let locals: VarInfo[][] = [];
        const normalenvs = envs.filter((e) => e.normalflow);
        for(let i = 0; i < origenv.locals.length; i++) {
            let frame: VarInfo[] = [];

            for(let j = 0; j < origenv.locals[i].length; j++) {
                const mdef = normalenvs.every((e) => (e.locals[i].find((vv) => vv.srcname === origenv.locals[i][j].srcname) as VarInfo).mustDefined);
                frame.push(new VarInfo(origenv.locals[i][j].srcname, origenv.locals[i][j].decltype, origenv.locals[i][j].vkind, mdef));
            }

            locals.push(frame);
        }

        const normalflow = envs.some((e) => e.normalflow);
        const returnflow = envs.every((e) => e.returnflow);
        return new TypeEnvironment(normalflow, returnflow, origenv.parent, [...origenv.args], locals);
    }
}

export {
    VarInfo,
    TypeInferContext, SimpleTypeInferContext, EListStyleTypeInferContext,
    TypeEnvironment
};
