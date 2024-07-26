
import { NominalTypeSignature } from "../frontend/type.js";

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
    generateTypeKey(ttype: NominalTypeSignature): string {
        const nscope = ttype.decl.ns.ns.join(".");

        if(ttype.decl.terms.length === 0) {
            return nscope + "." + ttype.decl.name;
        }
        else {
            const termstr = `<${ttype.alltermargs.map((t) => t.tkeystr).join(", ")}>`;
            return `${nscope}.${ttype.decl.name}${termstr}`;
        }
    }

    emitDeclNameAccess(ttype: NominalTypeSignature): string {
        const nscope = "$" + ttype.decl.ns.ns.join(".");

        if(ttype.decl.terms.length === 0) {
            return nscope + "." + ttype.decl.name;
        }
        else {
            const termstr = `<${ttype.alltermargs.map((t) => t.tkeystr).join(", ")}>`;
            return `${nscope}.${ttype.decl.name}["${termstr}"]`;
        }
    }
}

export {
    JSCodeFormatter,
    TypeNameResolver
};
