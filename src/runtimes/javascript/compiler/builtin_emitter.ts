import * as assert from "assert";
import { BSQRegex } from "../../../frontend/bsqregex";

import { TIRAssembly, TIRCodePack, TIRInvoke, TIRInvokePrimitive, TIRNamespaceFunctionDecl, TIROOType, TIRPCodeKey, TIRStaticFunctionDecl } from "../../../frontend/tree_ir/tir_assembly";
import { BodyEmitter } from "./body_emitter";

function resolveCodePack(asm: TIRAssembly, inv: TIRInvoke, pcname: string): TIRCodePack {
    return asm.pcodemap.get(inv.pcodes.get(pcname) as TIRPCodeKey) as TIRCodePack;
}

function generatePCodeInvokeName(pc: TIRCodePack): string {
    return `($Runtime.lambdas.get("${pc.invk}"))`;
}

function emitBuiltinNamespaceFunction(asm: TIRAssembly, func: TIRNamespaceFunctionDecl, bemitter: BodyEmitter): string | undefined {
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

function emitBuiltinMemberFunction(asm: TIRAssembly, ttype: TIROOType, func: TIRStaticFunctionDecl, bemitter: BodyEmitter): string | undefined {
    switch ((func.invoke as TIRInvokePrimitive).body) {
        case "special_extract":
        case "special_inject": {
            return undefined;
        }

        case "validator_accepts": {
            const vre = asm.validatorRegexs.get(ttype.tkey) as BSQRegex;
            const jsre = vre.re.compileToJS()
            return `{ return $Runtime.acceptsString(/${jsre}/); }`
        }

        case "s_string_append": {
            return `{ return ${func.invoke.params[0].name} + ${func.invoke.params[1].name}; }`;
        }

        case "s_list_empty": {
            return `{ return ${func.invoke.params[0].name}.size === 0; }`;
        }
        case "s_list_size": {
            return `{ return ${func.invoke.params[0].name}.size; }`;
        }
        case "s_list_get": {
            return `{ return ${func.invoke.params[0].name}.get(${func.invoke.params[1].name}); }`;
        }
        case "s_list_back": {
            return `{ return ${func.invoke.params[0].name}.last(); }`;
        }
        case "s_list_front": {
            return `{ return ${func.invoke.params[0].name}.first(); }`;
        }
        case "s_list_has_pred": {
            const pcode = resolveCodePack(asm, func.invoke, "p");
            const pcodeinvk = generatePCodeInvokeName(pcode);
            const pred = `($$vv) => $$pcf(${["p", "$$vv"].join(", ")})`
            return `{ const $$pcf = ${pcodeinvk}; return ${func.invoke.params[0].name}.some(${pred}); }`;
        }
        case "s_list_push_back": {
            return `{ return ${func.invoke.params[0].name}.push(${func.invoke.params[1].name}); }`;
        }
        case "s_list_push_front": {
            return `{ return ${func.invoke.params[0].name}.unshift(${func.invoke.params[1].name}); }`;
        }
        case "s_list_pop_back": {
            return `{ return ${func.invoke.params[0].name}.pop(); }`;
        }
        case "s_list_pop_front": {
            return `{ return ${func.invoke.params[0].name}.shift(); }`;
        }
        case "s_list_reduce": {
            const pcode = resolveCodePack(asm, func.invoke, "f");
            const pcodeinvk = generatePCodeInvokeName(pcode);
            const op = `($$uu, $$vv) => $$pcf(${["f", "$$uu", "$$vv"].join(", ")})`
            return `{ const $$pcf = ${pcodeinvk}; return ${func.invoke.params[0].name}.reduce(${op}, ${func.invoke.params[1].name}); }`;
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