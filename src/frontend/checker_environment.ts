import {strict as assert} from "assert";

import { TypeSignature } from "./type";
import { BinderInfo } from "./body";

class VarInfo {
    readonly srcname: string;
    readonly layoutType: TypeSignature;
    readonly flowType: TypeSignature;

    readonly isConst: boolean;
    readonly mustDefined: boolean;

    constructor(srcname: string, ltype: TypeSignature, ftype: TypeSignature, isConst: boolean, mustDefined: boolean) {
        this.srcname = srcname;
        this.layoutType = ltype;
        this.flowType = ftype;

        this.isConst = isConst;
        this.mustDefined = mustDefined;
    }

    updateFlowTypeAndDefine(ttype: TypeSignature): VarInfo {
        return new VarInfo(this.srcname, this.layoutType, ttype, this.isConst, true);
    }
}

class TypeEnvironment {
    readonly normalflow: boolean;
    readonly returnflow: boolean;
    readonly parent: TypeEnvironment | undefined;

    readonly args: VarInfo[];
    readonly returnType: TypeSignature;

    readonly locals: VarInfo[][];

    constructor(normalflow: boolean, returnflow: boolean, parent: TypeEnvironment | undefined, args: VarInfo[], returnType: TypeSignature, locals: VarInfo[][]) {
        this.normalflow = normalflow;
        this.returnflow = returnflow;
        this.parent = parent;

        this.args = args;
        this.returnType = returnType;

        this.locals = locals;
    }

    private static cloneLocals(locals: VarInfo[][]): VarInfo[][] {
        return locals.map((l) => [...l]);
    }

    static createInitialStdEnv(args: VarInfo[], returnType: TypeSignature): TypeEnvironment {
        return new TypeEnvironment(true, false, undefined, args, returnType, []);
    }

    static createInitialLambdaEnv(args: VarInfo[], returnType: TypeSignature, enclosing: TypeEnvironment): TypeEnvironment {
        return new TypeEnvironment(true, false, enclosing, args, returnType, []);
    }

    resolveLambdaCaptureVarType(vname: string): TypeSignature | undefined {
        let parent = this.parent;
        while(parent !== undefined) {
            const vv = parent.resolveLocalVarInfo(vname);
            if(vv !== undefined) {
                return vv.flowType;
            }
        }

        return undefined;
    }

    resolveLocalVarInfo(vname: string): VarInfo | undefined {
        for(let i = this.locals.length - 1; i >= 0; i--) {
            for(let j = 0; j < this.locals[i].length; j++) {
                if(this.locals[i][j].srcname === vname) {
                    return this.locals[i][j];
                }
            }
        }

        return this.args.find((v) => v.srcname === vname);
    }

    addLocalVariable(vname: string, vtype: TypeSignature, isConst: boolean, mustDefined: boolean): TypeEnvironment {
        return new TypeEnvironment(this.normalflow, this.returnflow, this.parent, [...this.args], this.returnType, [...TypeEnvironment.cloneLocals(this.locals), [new VarInfo(vname, vtype, vtype, isConst, mustDefined)]]);
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
                    frame.push(this.locals[i][j].updateFlowTypeAndDefine(this.locals[i][j].layoutType));
                }
            }

            locals = [frame, ...locals];
        }

        return new TypeEnvironment(this.normalflow, this.returnflow, this.parent, [...this.args], this.returnType, locals);
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
                    frame.push(this.locals[i][j].updateFlowTypeAndDefine(ttype));
                }
            }

            locals = [frame, ...locals];
        }

        return new TypeEnvironment(this.normalflow, this.returnflow, this.parent, [...this.args], this.returnType, locals);
    }

    setDeadFlow(): TypeEnvironment {
        return new TypeEnvironment(false, false, this.parent, [...this.args], this.returnType, TypeEnvironment.cloneLocals(this.locals));
    }

    setReturnFlow(): TypeEnvironment {
        return new TypeEnvironment(false, true, this.parent, [...this.args], this.returnType, TypeEnvironment.cloneLocals(this.locals));
    }

    pushNewLocalScope(): TypeEnvironment {
        return new TypeEnvironment(this.normalflow, this.returnflow, this, [...this.args], this.returnType, [...TypeEnvironment.cloneLocals(this.locals), []]);
    }

    pushNewLocalBinderScope(vname: string, vtype: TypeSignature): TypeEnvironment {
        return new TypeEnvironment(this.normalflow, this.returnflow, this, [...this.args], this.returnType, [...TypeEnvironment.cloneLocals(this.locals), [new VarInfo(vname, vtype, vtype, true, true)]]);
    }

    popLocalScope(): TypeEnvironment {
        assert(this.locals.length > 0);
        return new TypeEnvironment(this.normalflow, this.returnflow, this.parent, [...this.args], this.returnType, TypeEnvironment.cloneLocals(this.locals).slice(0, this.locals.length - 1));
    }

    static mergeEnvironmentsSimple(origenv: TypeEnvironment, ...envs: TypeEnvironment[]): TypeEnvironment {
        let locals: VarInfo[][] = [];
        for(let i = 0; i < origenv.locals.length; i++) {
            let frame: VarInfo[] = [];

            for(let j = 0; j < origenv.locals[i].length; j++) {
                const mdef = envs.every((e) => (e.resolveLocalVarInfo(origenv.locals[i][j].srcname) as VarInfo).mustDefined);
                frame.push(new VarInfo(origenv.locals[i][j].srcname, origenv.locals[i][j].layoutType, origenv.locals[i][j].flowType, origenv.locals[i][j].isConst, mdef));
            }

            locals.push(frame);
        }

        return new TypeEnvironment(origenv.normalflow, origenv.returnflow, origenv.parent, [...origenv.args], origenv.returnType, locals);
    }

    static gatherEnvironmentsOptBinderFlowType(binfo: BinderInfo | undefined, ...envs: TypeEnvironment[]): TypeSignature[] | undefined {
        if(binfo === undefined) {
            return undefined;
        }
        else {
            const topts = envs.filter((e) => e.normalflow).map((e) => e.resolveLocalVarInfo(binfo.scopename) as VarInfo);
            return topts.length !== 0 ? topts.map((v) => v.flowType) : undefined;
        }
    }

    static mergeEnvironmentsOptBinderFlow(origenv: TypeEnvironment, binfo: BinderInfo | undefined, refinetype: TypeSignature | undefined, ...envs: TypeEnvironment[]): TypeEnvironment {
        const menv = TypeEnvironment.mergeEnvironmentsSimple(origenv, ...envs);

        if(binfo === undefined || refinetype === undefined) {
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
    TypeEnvironment
};
