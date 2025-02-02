import { EListTypeSignature, FullyQualifiedNamespace, TemplateNameMapper, TypeSignature } from "./type.js";


class FunctionInstantiationInfo {
    readonly binds: TemplateNameMapper[] | undefined;

    constructor(binds: TemplateNameMapper[] | undefined) {
        this.binds = binds;
    }

    static createNoTemplateInfo(): FunctionInstantiationInfo {
        return new FunctionInstantiationInfo(undefined);
    }
}

class MethodInstantiationInfo {
    readonly binds: TemplateNameMapper[] | undefined;

    constructor(binds: TemplateNameMapper[] | undefined) {
        this.binds = binds;
    }

    static createNoTemplateInfo(): MethodInstantiationInfo {
        return new MethodInstantiationInfo(undefined);
    }
}

class TypeInstantiationInfo {
    readonly tkey: string;
    readonly tsig: TypeSignature;

    readonly binds: TemplateNameMapper | undefined;
    readonly functionbinds: Map<string, FunctionInstantiationInfo>;
    readonly methodbinds: Map<string, MethodInstantiationInfo>;

    constructor(tkey: string, tsig: TypeSignature, binds: TemplateNameMapper | undefined, functionbinds: Map<string, FunctionInstantiationInfo>, methodbinds: Map<string, MethodInstantiationInfo>) {
        this.tkey = tkey;
        this.tsig = tsig;
        this.binds = binds;

        this.functionbinds = functionbinds;
        this.methodbinds = methodbinds;
    }

    static createNoTemplateInfo(tkey: string, tsig: TypeSignature, functionbinds: Map<string, FunctionInstantiationInfo>, methodbinds: Map<string, MethodInstantiationInfo>): TypeInstantiationInfo {
        return new TypeInstantiationInfo(tkey, tsig, undefined, functionbinds, methodbinds);
    }
}

class NamespaceInstantiationInfo {
    readonly ns: FullyQualifiedNamespace;

    readonly functionbinds: Map<string, FunctionInstantiationInfo>;
    readonly typebinds: Map<string, TypeInstantiationInfo[]>;

    readonly elists: Map<string, EListTypeSignature>;

    constructor(ns: FullyQualifiedNamespace) {
        this.ns = ns;
        
        this.functionbinds = new Map<string, FunctionInstantiationInfo>();
        this.typebinds = new Map<string, TypeInstantiationInfo[]>();
        this.elists = new Map<string, EListTypeSignature>();
    }
}


export {
    FunctionInstantiationInfo,
    MethodInstantiationInfo,
    TypeInstantiationInfo,
    NamespaceInstantiationInfo
};
