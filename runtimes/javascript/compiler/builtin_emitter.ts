import * as assert from "assert";

import { TIRInvokePrimitive, TIRNamespaceFunctionDecl, TIROOType, TIRStaticFunctionDecl } from "../../../frontend/tree_ir/tir_assembly";
import { BodyEmitter } from "./body_emitter";

function emitBuiltinNamespaceFunction(func: TIRNamespaceFunctionDecl, bemitter: BodyEmitter): string {

}

function emitBuiltinMemberFunction(ttype: TIROOType, func: TIRStaticFunctionDecl, bemitter: BodyEmitter): string | undefined {
    switch ((func.invoke as TIRInvokePrimitive).body) {
        case "special_extract":
        case "special_inject": {
            return undefined;
        }
        case "validator_accepts": {
            const bsqre = this.assembly.validatorRegexs.get(idecl.enclosingDecl as MIRResolvedTypeKey) as BSQRegex;
            const lre = bsqre.compileToPatternToSMT(true);

            let accept = new SMTCallSimple("str.in.re", [new SMTVar(args[0].vname), new SMTConst(lre)]);
            return SMTFunction.create(ideclname, args, chkrestype, accept);
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