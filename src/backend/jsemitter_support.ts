
import { AbstractConceptTypeDecl, Assembly, ConstMemberDecl, NamespaceConstDecl, NamespaceDeclaration, NamespaceFunctionDecl, TypeFunctionDecl } from "../frontend/assembly.js";
import { SourceInfo } from "../frontend/build_decls.js";
import { EListTypeSignature, FullyQualifiedNamespace, NominalTypeSignature, TemplateNameMapper, TemplateTypeSignature, TypeSignature } from "../frontend/type.js";

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

    private static emitNamespaceAccess(currentns: NamespaceDeclaration, tns: NamespaceDeclaration): string {
        return (tns.fullnamespace.ns[0] === "Core"  || currentns.fullnamespace.ns[0] === tns.fullnamespace.ns[0]) ? (tns.fullnamespace.ns.slice(1).join(".")) : ("$" + tns.fullnamespace.ns.join("."));
    }

    private static emitTypeAccess(currentns: NamespaceDeclaration, ttype: NominalTypeSignature): string {
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

    static generateDeclarationNameForNamespaceConstant(currentns: NamespaceDeclaration, cv: NamespaceConstDecl): string {
        const nns = EmitNameManager.emitNamespaceAccess(currentns, currentns);
        if(nns === "") {
            return `const ${cv.name} = `;
        }
        else {
            return `${cv.name}: `;
        }
    }

    static generateDeclarationNameForNamespaceFunction(currentns: NamespaceDeclaration, fv: NamespaceFunctionDecl, mapper: TemplateNameMapper): string {
        const nns = EmitNameManager.emitNamespaceAccess(currentns, currentns);

        if(nns === "") {
            if(fv.terms.length === 0) {
                return `function ${fv.name}`;
            }
            else {
                const termstr = `<${fv.terms.map((t) => mapper.resolveTemplateMapping(new TemplateTypeSignature(SourceInfo.implicitSourceInfo(), t.name)).tkeystr).join(", ")}>`;
                return `"${fv.name}${termstr}": `;
            }
        }
        else {
            if(fv.terms.length === 0) {
                return `${fv.name}: `;
            }
            else {
                const termstr = `<${fv.terms.map((t) => mapper.resolveTemplateMapping(new TemplateTypeSignature(SourceInfo.implicitSourceInfo(), t.name)).tkeystr).join(", ")}>`;
                return `"${fv.name}${termstr}": `;
            }
        }
    }

    static generateDeclarationNameForTypeConstant(cv: ConstMemberDecl): string {
        return `${cv.name}: `;
    }

    static generateDeclarationNameForTypeFunction(fv: TypeFunctionDecl, mapper: TemplateNameMapper): string {
        if(fv.terms.length === 0) {
            return `${fv.name}: `;
        }
        else {
            const termstr = `<${fv.terms.map((t) => mapper.resolveTemplateMapping(new TemplateTypeSignature(SourceInfo.implicitSourceInfo(), t.name)).tkeystr).join(", ")}>`;
            return `"${fv.name}${termstr}": `;
        }
    }

    static generateAccssorNameForNamespaceConstant(currentns: NamespaceDeclaration, inns: NamespaceDeclaration, cv: NamespaceConstDecl): string {
        const nns = this.emitNamespaceAccess(currentns, inns);
        const ans = nns !== "" ? (nns + ".") : "";

        return `${ans}${cv}`;
    }

    static generateAccssorNameForNamespaceFunction(currentns: NamespaceDeclaration, inns: NamespaceDeclaration, fv: NamespaceFunctionDecl, mapper: TemplateNameMapper): string {
        const nns = this.emitNamespaceAccess(currentns, inns);
        const ans = nns !== "" ? (nns + ".") : "";

        if(fv.terms.length === 0) {
            return `${ans}${fv.name}`;
        }
        else {
            const termstr = `<${fv.terms.map((t) => mapper.resolveTemplateMapping(new TemplateTypeSignature(SourceInfo.implicitSourceInfo(), t.name)).tkeystr).join(", ")}>`;
            return `${ans}["${fv.name}${termstr}"]`;
        }
    }

    static generateAccssorNameForTypeConstant(ttype: NominalTypeSignature, cv: ConstMemberDecl): string {
        return `${this.generateTypeKey(ttype)}["${membername}"]`;
    }

    static generateAccssorNameForTypeFunction(ttype: NominalTypeSignature, fv: TypeFunctionDecl, mapper: TemplateNameMapper): string {
        return `${this.generateTypeKey(ttype)}["${membername}"]`;
    }
}

export {
    JSCodeFormatter,
    EmitNameManager
};
