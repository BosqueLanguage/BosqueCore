import { LambdaDecl, MethodDecl, NamespaceDeclaration, NamespaceFunctionDecl, TypeFunctionDecl } from "../../frontend/assembly.js";
import { EListTypeSignature, FullyQualifiedNamespace, LambdaTypeSignature, TemplateNameMapper, TypeSignature } from "../../frontend/type.js";

class LambdaInstantiationInfo {
    readonly newikey: string;

    readonly binds: TemplateNameMapper | undefined;
    readonly lambdacons: Map<number, string>;

    readonly capturedVars: [string, TypeSignature, "outer" | "local" | "param"][];
    readonly capturedLambdas: { pname: string, psigkey: string }[];
    readonly capturedTemplateNames: string[];

    readonly lsig: LambdaTypeSignature;
    readonly body: LambdaDecl;

    constructor(newikey: string, binds: TemplateNameMapper | undefined, lambdacons: Map<number, string>, capturedVars: [string, TypeSignature, "outer" | "local" | "param"][], capturedLambdas: { pname: string, psigkey: string }[], capturedTemplateNames: string[], lsig: LambdaTypeSignature, body: LambdaDecl) {
        this.newikey = newikey;
        this.binds = binds;
        this.lambdacons = lambdacons;
        this.capturedVars = capturedVars;
        this.capturedLambdas = capturedLambdas;
        this.capturedTemplateNames = capturedTemplateNames;
        this.lsig = lsig;
        this.body = body;
    }
}

class InvokeInstantiationInfo {
    readonly newikey: string;

    readonly binds: TemplateNameMapper | undefined;
    readonly lambdaargs: { pname: string, psigkey: string }[]; //string corresponds to a lambda instantation info
    readonly lambdacons: Map<number, string>; //string corresponds to a lambda instantation info

    readonly monoinvids: Map<number, string>;

    constructor(newikey: string, binds: TemplateNameMapper | undefined, lambdaargs: { pname: string, psigkey: string }[], lambdacons: Map<number, string>, monoinvids: Map<number, string>) {
        this.newikey = newikey;
        this.binds = binds;
        this.lambdaargs = lambdaargs;
        this.lambdacons = lambdacons;
        this.monoinvids = monoinvids;
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
    readonly lambdas: Map<string, LambdaInstantiationInfo>;

    constructor(ns: FullyQualifiedNamespace) {
        this.ns = ns;
        
        this.functionbinds = new Map<string, InvokeInstantiationInfo[]>();
        this.typebinds = new Map<string, TypeInstantiationInfo[]>();
        this.elists = new Map<string, EListTypeSignature>();
        this.lambdas = new Map<string, LambdaInstantiationInfo>();
    }
}

function computeTBindsKey(tbinds: TypeSignature[]): string {
    return (tbinds.length !== 0) ? `<${tbinds.map(t => t.tkeystr).join(", ")}>` : "";
}

function computeLambdaKey(packs: { pname: string, psigkey: string }[]): string {
    return (packs.length !== 0) ? `[${packs.map(lp => lp.psigkey).join(", ")}]` : "";
}

function computeResolveKeyForInvoke(ikey: string, termcount: number, hasref: boolean, lambdas: boolean): string {
    const tci = (termcount !== 0) ? `*tc_${termcount}_` : "";
    const rfi = (hasref ? "*_ref_" : "");
    const li = (lambdas ? "*_lambdas_" : "");

    return `${ikey}${tci}${rfi}${li}`;
}

function computeInvokeKeyForNamespaceFunction(ns: NamespaceDeclaration, fdecl: NamespaceFunctionDecl, terms: TypeSignature[], lambdas: { pname: string, psigkey: string }[]): string {
    const rti = fdecl.params.some((p) => p.pkind !== undefined) ? "#ref" : "";
    return `${ns.fullnamespace.emit()}::${fdecl.name}${rti}${computeTBindsKey(terms)}${computeLambdaKey(lambdas)}`;
}

function computeInvokeKeyForTypeFunction(rcvrtype: TypeSignature, fdecl: TypeFunctionDecl, terms: TypeSignature[], lambdas: { pname: string, psigkey: string }[]): string {
    const rti = fdecl.params.some((p) => p.pkind !== undefined) ? "#ref" : "";
    return `${rcvrtype.tkeystr}::${fdecl.name}${rti}${computeTBindsKey(terms)}${computeLambdaKey(lambdas)}`;
}

function computeInvokeKeyForTypeMethod(rcvrtype: TypeSignature, mdecl: MethodDecl, terms: TypeSignature[], lambdas: { pname: string, psigkey: string }[]): string {
    const rti = ((mdecl.isThisRef) || mdecl.params.some((p) => p.pkind !== undefined)) ? "#ref" : "";
    return `${rcvrtype.tkeystr}@${mdecl.name}${rti}${computeTBindsKey(terms)}${computeLambdaKey(lambdas)}`;
}

export {
    LambdaInstantiationInfo,
    InvokeInstantiationInfo,
    TypeInstantiationInfo,
    NamespaceInstantiationInfo,
    computeTBindsKey, computeLambdaKey, computeResolveKeyForInvoke, 
    computeInvokeKeyForNamespaceFunction, computeInvokeKeyForTypeFunction, computeInvokeKeyForTypeMethod
};
