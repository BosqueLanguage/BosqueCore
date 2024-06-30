
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
    emitDeclNameAccess(ttype: NominalTypeSignature): string {
        const nscope = "$" + ttype.decl.ns.ns.join(".");
        const termstr = `<${ttype.alltermargs.map((t) => t.tkeystr).join(", ")}>`;

        if(ttype.decl.terms.length === 0) {
            return nscope + "." + ttype.decl.name;
        }
        else {
            return `${nscope}.${ttype.decl.name}["${termstr}"]`;
        }
    }
}

export {
    JSCodeFormatter,
    TypeNameResolver
};
