import { EListTypeSignature, FullyQualifiedNamespace, TemplateNameMapper, TypeSignature } from "../../frontend/type.ts";
import { IRLambdaParameterPackTypeSignature } from "../irdefs/irtype.ts";

class InvokeInstantiationInfo {
    readonly newikey: string;

    readonly binds: TemplateNameMapper | undefined;
    readonly lambdas: { pname: string, psig: IRLambdaParameterPackTypeSignature, invtrgt: string }[];
    
    constructor(newikey: string, binds: TemplateNameMapper | undefined, lambdas: { pname: string, psig: IRLambdaParameterPackTypeSignature, invtrgt: string }[]) {
        this.newikey = newikey;
        this.binds = binds;
        this.lambdas = lambdas;
    }
}

class TypeInstantiationInfo {
    readonly tkey: string;
    readonly tsig: TypeSignature;

    readonly binds: TemplateNameMapper | undefined;
    readonly functionbinds: Map<string, InvokeInstantiationInfo[]>;
    readonly methodbinds: Map<string, InvokeInstantiationInfo[]>;

    constructor(tkey: string, tsig: TypeSignature, binds: TemplateNameMapper | undefined, functionbinds: Map<string, InvokeInstantiationInfo[]>, methodbinds: Map<string, InvokeInstantiationInfo[]>) {
        this.tkey = tkey;
        this.tsig = tsig;
        this.binds = binds;

        this.functionbinds = functionbinds;
        this.methodbinds = methodbinds;
    }

    static createNoTemplateInfo(tkey: string, tsig: TypeSignature, functionbinds: Map<string, InvokeInstantiationInfo[]>, methodbinds: Map<string, InvokeInstantiationInfo[]>): TypeInstantiationInfo {
        return new TypeInstantiationInfo(tkey, tsig, undefined, functionbinds, methodbinds);
    }
}

class NamespaceInstantiationInfo {
    readonly ns: FullyQualifiedNamespace;

    readonly functionbinds: Map<string, InvokeInstantiationInfo[]>;
    readonly typebinds: Map<string, TypeInstantiationInfo[]>;

    readonly elists: Map<string, EListTypeSignature>;

    constructor(ns: FullyQualifiedNamespace) {
        this.ns = ns;
        
        this.functionbinds = new Map<string, InvokeInstantiationInfo[]>();
        this.typebinds = new Map<string, TypeInstantiationInfo[]>();
        this.elists = new Map<string, EListTypeSignature>();
    }
}


export {
    InvokeInstantiationInfo,
    TypeInstantiationInfo,
    NamespaceInstantiationInfo
};
