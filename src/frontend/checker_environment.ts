import {strict as assert} from "assert";

import { TypeSignature } from "./type";

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

    updateFlowType(ttype: TypeSignature): VarInfo {
        return new VarInfo(this.srcname, this.layoutType, ttype, this.isConst, this.mustDefined);
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

    static createInitialStdEnv(args: VarInfo[], returnType: TypeSignature): TypeEnvironment {
        return new TypeEnvironment(false, undefined, args, returnType, []);
    }

    static createInitialLambdaEnv(args: VarInfo[], returnType: TypeSignature, enclosing: TypeEnvironment): TypeEnvironment {
        return new TypeEnvironment(false, enclosing, args, returnType, []);
    }

    resolveLambdaCaptureVarType(scopename: string): TypeSignature | undefined {
        xxxx;
    }

    resolveLocalVarInfo(scopename: string): VarInfo | undefined {
        xxxx;
    }

    addLocalVariable(scopename: string, oftype: TypeSignature, isConst: boolean, mustDefined: boolean): TypeEnvironment {
        xxxx;
    }

    assignLocalVariable(scopename: string): TypeEnvironment {
        xxxx;
    }

    retypeLocalVariable(scopename: string, ttype: TypeSignature): TypeEnvironment {
        xxxx;
    }

    setDeadFlow(): TypeEnvironment {
        xxxx;
    }

    setReturnFlow(): TypeEnvironment {
        xxxx;
    }

    pushNewLocalScope(): TypeEnvironment {
        xxxx;
    }

    pushNewLocalBinderScope(vname: string, vtype: TypeSignature): TypeEnvironment {
        xxxx;
    }

    popLocalScope(): TypeEnvironment {
        xxxx;
    }

    static mergeEnvironments(...envs: TypeEnvironment[]): TypeEnvironment {
        xxxx;
    }
}

export {
    VarInfo,
    TypeEnvironment
};
