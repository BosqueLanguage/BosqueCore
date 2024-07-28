
import { AbstractConceptTypeDecl, Assembly, NamespaceDeclaration } from "../frontend/assembly.js";
import { EListTypeSignature, FullyQualifiedNamespace, NominalTypeSignature, TypeSignature } from "../frontend/type.js";

class JSCodeFormatter {
    private level: number;

    constructor(iidnt: number) {
        this.level = iidnt;
    }

    indentPush() {
        this.level++;
    }
    
    indentPop() {
        this.level--;
    }
    
    indent(code: string): string {
        return "    ".repeat(this.level) + code;
    }   
}

class EmitNameManager {
    static isUniqueTypeForSubtypeChecking(ttype: TypeSignature): boolean {
        return (ttype instanceof NominalTypeSignature) && !(ttype.decl instanceof AbstractConceptTypeDecl);
    }

    static isNakedTypeRepr(ttype: TypeSignature): boolean {
        if(ttype instanceof EListTypeSignature) {
            return true;
        }
        else if(ttype instanceof NominalTypeSignature) {
            return !(ttype.decl instanceof AbstractConceptTypeDecl);
        }
        else {
            return false;
        }
    }

    static isBoxedTypeRepr(ttype: TypeSignature): boolean {
        return !this.isNakedTypeRepr(ttype);
    }

    static generateTypeKey(ttype: NominalTypeSignature): string {
        const nscope = ttype.decl.ns.ns.join(".");

        if(ttype.decl.terms.length === 0) {
            return nscope + "." + ttype.decl.name;
        }
        else {
            const termstr = `<${ttype.alltermargs.map((t) => t.tkeystr).join(", ")}>`;
            return `${nscope}.${ttype.decl.name}${termstr}`;
        }
    }

    static generateTypeKeySymbol(ttype: NominalTypeSignature): string {
        const tkey = this.generateTypeKey(ttype);
        return `Symbol.for("${tkey}")`;
    }

    static resolveNamespaceDecl(assembly: Assembly, ns: FullyQualifiedNamespace): NamespaceDeclaration {
        let curns = assembly.getToplevelNamespace(ns.ns[0]) as NamespaceDeclaration;

        for(let i = 1; i < ns.ns.length; ++i) {
            curns = curns.subns.find((nns) => nns.name === ns.ns[i]) as NamespaceDeclaration;
        }

        return curns as NamespaceDeclaration;
    }

    static emitNamespaceAccess(currentns: NamespaceDeclaration, tns: NamespaceDeclaration): string {
        const nscope = (tns.fullnamespace.ns[0] === "Core"  || currentns.fullnamespace.ns[0] === tns.fullnamespace.ns[0]) ? (tns.fullnamespace.ns.slice(1).join(".")) : ("$" + tns.fullnamespace.ns.join("."));
        const acroot = nscope !== "" ?  nscope + "." : "";

        return acroot;
    }

    static emitTypeAccess(currentns: NamespaceDeclaration, ttype: NominalTypeSignature): string {
        const nscope = (ttype.decl.ns.ns[0] === "Core" || currentns.fullnamespace.ns[0] === ttype.decl.ns.ns[0]) ? (ttype.decl.ns.ns.slice(1).join(".")) : ("$" + ttype.decl.ns.ns.join("."));
        const acroot = nscope !== "" ?  nscope + "." : "";

        if(ttype.decl.terms.length === 0) {
            return acroot + ttype.decl.name;
        }
        else {
            const termstr = `<${ttype.alltermargs.map((t) => t.tkeystr).join(", ")}>`;
            if(ttype.decl.isSpecialResultEntity()) {
                return `Result.${ttype.decl.name}["${termstr}"]`;
            }
            else if(ttype.decl.isSpecialAPIResultEntity()) {
                return `APIResult.${ttype.decl.name}["${termstr}"]`;
            }
            else {
                return `${acroot}${ttype.decl.name}["${termstr}"]`;
            }
        }
    }
}

export {
    JSCodeFormatter,
    EmitNameManager
};
