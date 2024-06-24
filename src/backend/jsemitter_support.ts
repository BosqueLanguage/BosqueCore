import assert from "node:assert";

import { AutoTypeSignature, ErrorTypeSignature, NominalTypeSignature, TemplateTypeSignature, TypeSignature, VoidTypeSignature } from "../frontend/type.js";
import { ConstructableTypeDecl } from "../frontend/assembly.js";

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

class TypeNameResolver {
    emitDeclNameAccess(ttype: NominalTypeSignature): string {
        assert(ttype.resolvedDeclaration !== undefined);
        const rdecl = ttype.resolvedDeclaration;

        const nscope = "$" + rdecl.ns.ns.join(".");
        if((rdecl instanceof ConstructableTypeDecl) && (rdecl.name === "Ok" || rdecl.name === "Err")) {
            const termstr = `<${rdecl.terms.map((t) => { return t.emit(); }).join(", ")}>`;
            return `${nscope}.${rdecl.name}["${termstr}"]`;
        }
        else if((rdecl instanceof ConstructableTypeDecl) && (rdecl.name === "Rejected" || rdecl.name === "Failed" || rdecl.name === "Error" || rdecl.name === "Success")) {
            const termstr = `<${rdecl.terms.map((t) => { return t.emit(); }).join(", ")}>`;
            return `${nscope}.${rdecl.name}["${termstr}"]`;
        }
        else {
            if(rdecl.terms.length === 0) {
                return nscope + "." + rdecl.name;
            }
            else {
                const termstr = `<${ttype.tscope.map((t) => { return t.emit(); }).join(", ")}>`;
                return `${nscope}.${rdecl.name}["${termstr}"]`;
            }
        }
    }
}

export {
    JSCodeFormatter,
    TypeNameResolver
};
