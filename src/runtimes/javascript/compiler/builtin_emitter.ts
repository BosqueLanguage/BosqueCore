import * as assert from "assert";

import { TIRInvokePrimitive, TIRNamespaceFunctionDecl, TIROOType, TIRStaticFunctionDecl } from "../../../frontend/tree_ir/tir_assembly";
import { BodyEmitter } from "./body_emitter";

function emitBuiltinNamespaceFunction(func: TIRNamespaceFunctionDecl, bemitter: BodyEmitter): string | undefined {
    switch ((func.invoke as TIRInvokePrimitive).body) {
        case "special_extract":
        case "special_inject": {
            return undefined;
        }
        default: {
            assert(false, `Unknown primitive member function -- ${(func.invoke as TIRInvokePrimitive).body}`);
            return "[UNKNOWN PRIMITIVE FUNCTION]";
        }
    }
}

function emitBuiltinMemberFunction(ttype: TIROOType, func: TIRStaticFunctionDecl, bemitter: BodyEmitter): string | undefined {
    switch ((func.invoke as TIRInvokePrimitive).body) {
        case "special_extract":
        case "special_inject": {
            return undefined;
        }
        default: {
            assert(false, `Unknown primitive member function -- ${(func.invoke as TIRInvokePrimitive).body}`);
            return "[UNKNOWN PRIMITIVE FUNCTION]";
        }
    }
}

export {
    emitBuiltinNamespaceFunction, emitBuiltinMemberFunction
}