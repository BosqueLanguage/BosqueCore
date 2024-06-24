import assert from "node:assert";

import { AutoTypeSignature, ErrorTypeSignature, TypeSignature } from "../frontend/type.js";

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
    emitDeclName(ttype: TypeSignature): string {
        assert(!(ttype instanceof ErrorTypeSignature) && !(ttype instanceof AutoTypeSignature));
    }
}

export {
    JSCodeFormatter,
    TypeNameResolver
};
