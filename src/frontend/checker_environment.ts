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

class TypeEnvironment {

}

export {
    VarInfo, TemplateBindingScope,
    TypeEnvironment
};
