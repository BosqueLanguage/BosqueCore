import * as assert from "assert";

import { TIRAssembly, TIRCodePack, TIRInvoke, TIRInvokePrimitive, TIRNamespaceFunctionDecl, TIROOType, TIRPCodeKey, TIRStaticFunctionDecl } from "../../../frontend/tree_ir/tir_assembly";
import { BodyEmitter } from "./body_emitter";

function resolveCodePack(asm: TIRAssembly, inv: TIRInvoke, pcname: string): TIRCodePack {
    return asm.pcodemap.get(inv.pcodes.get(pcname) as TIRPCodeKey) as TIRCodePack;
}

function resolveCapturedPackArgs(pcname: string, pcc: TIRCodePack): string[] {
    return [...pcc.capturedCodePacks.map((pcc) => pcc.cpname)];
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
        case "s_list_empty": {
            return `{ return  ${func.invoke.params[0].name}.size === 0; }`;
        }
        case "s_list_has_pred": {
            const pcode = resolveCodePack(asm, func.invoke, "p");
            const pcodeinvk = generatePCodeInvokeName(pcode);
            const pred = `($$vv) => ${pcodeinvk}(${[...resolveCapturedPackArgs("p", pcode), "$$vv"].join(", ")})`
            return `{ return ${func.invoke.params[0].name}.findIndex(${pred}) !== -1; }`;
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