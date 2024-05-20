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

class TypeEnvironment {
    readonly binds: Map<string, VarInfo>;

    constructor(binds: Map<string, VarInfo>) {
        this.binds = new Map<string, VarInfo>(binds);
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
}

export {
    VarInfo,
    TypeEnvironment
};
