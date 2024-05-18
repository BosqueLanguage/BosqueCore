import {strict as assert} from "assert";

import { TemplateBindingScope, TypeSignature } from "./type";

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
    resolveLambdaCaptureVarType(scopename: string): TypeSignature {
        xxxx;
    }

    resolveLocalVarInfo(scopename: string): VarInfo {
        xxxx;
    }
}

export {
    VarInfo,
    TypeEnvironment
};
