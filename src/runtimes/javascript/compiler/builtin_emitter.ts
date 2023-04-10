import { BSQRegex } from "../../../frontend/bsqregex";

import { TIRAssembly, TIRCodePack, TIRInvoke, TIRInvokePrimitive, TIRNamespaceFunctionDecl, TIROOType, TIRPCodeKey, TIRStaticFunctionDecl, TIRType, TIRTypeKey } from "../../../frontend/tree_ir/tir_assembly";
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
            const jsre = vre.re.compileToJS();
            return `{ return $Runtime.acceptsString(/${jsre}/, ${func.invoke.params[0].name}); }`
        }

        case "number_nattoint":
        case "number_nattobignat":
        case "number_nattobigint": {
            return `{ return ${func.invoke.params[0].name}; }`;
        }       
        case "number_inttonat":
        case "number_inttobignat":
        case "number_inttobigint": {
            return `{ return ${func.invoke.params[0].name}; }`;
        }

        case "float_power": {
            return `{ return Math.pow(${func.invoke.params[0].name}, ${func.invoke.params[1].name}); }`;
        }
        case "decimal_power": {
            return `{ return Decimal.pow(${func.invoke.params[0].name}, ${func.invoke.params[1].name}); }`;
        }
        case "float_sqrt": {
            return `{ return Math.sqrt(${func.invoke.params[0].name}); }`;
        }
        case "decimal_sqrt": {
            return `{ return Decimal.sqrt(${func.invoke.params[0].name}); }`;
        }

        case "s_string_empty": {
            return `{ return ${func.invoke.params[0].name}.length === 0; }`;
        }
        case "s_string_append": {
            return `{ return ${func.invoke.params[0].name} + ${func.invoke.params[1].name}; }`;
        }
        case "s_string_startswith": {
            return `{ return ${func.invoke.params[0].name}.startsWith(${func.invoke.params[1].name}); }`;
        }
        case "s_string_extractfront": {
            return `{ return ${func.invoke.params[0].name}.slice(0, ${func.invoke.params[1].name}.length()); }`;
        }
        case "s_string_removefront": {
            return `{ return ${func.invoke.params[0].name}.slice(${func.invoke.params[1].name}.length); }`;
        }
        case "s_string_endswith": {
            return `{ return ${func.invoke.params[0].name}.endsWith(${func.invoke.params[1].name}); }`;
        }
        case "s_string_extractend": {
            return `{ return ${func.invoke.params[0].name}.slice(${func.invoke.params[1].name}.length); }`;
        }
        case "s_string_removeend": {
            return `{ return ${func.invoke.params[0].name}.slice(0, ${func.invoke.params[1].name}.length); }`;
        }

        case "s_list_empty": {
            return `{ return ${func.invoke.params[0].name}.size === 0; }`;
        }
        case "s_list_size": {
            return `{ return BigInt(${func.invoke.params[0].name}.size); }`;
        }
        case "s_list_get": {
            return `{ return ${func.invoke.params[0].name}.get(Number(${func.invoke.params[1].name})); }`;
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
            const pred = `($$vv) => $$pcf(${["p", "$$vv"].join(", ")})`;
            return `{ const $$pcf = ${pcodeinvk}; return ${func.invoke.params[0].name}.some(${pred}); }`;
        }
        case "s_list_has_pred_idx": {
            const pcode = resolveCodePack(asm, func.invoke, "p");
            const pcodeinvk = generatePCodeInvokeName(pcode);
            const pred = `($$vv, $$ii) => $$pcf(${["p", "$$vv", "BigInt($$ii)"].join(", ")})`;
            return `{ const $$pcf = ${pcodeinvk}; return ${func.invoke.params[0].name}.some(${pred}); }`;
        }
        case "s_list_has": {
            const oftype = func.invoke.tbinds.get("T") as TIRTypeKey;
            const cmp = bemitter.typeEncodedAsUnion(oftype) ? `$CoreLibs.$KeyEqualGeneral` : `($CoreLibs.$KeyEqualOps.get("${oftype}"))`;
            return `{ return ${func.invoke.params[0].name}.some((e) => ${cmp}(e, ${func.invoke.params[1].name})); }`;
        }
        case "s_list_find_pred": {
            const pcode = resolveCodePack(asm, func.invoke, "p");
            const pcodeinvk = generatePCodeInvokeName(pcode);
            const pred = `($$vv) => $$pcf(${["p", "$$vv"].join(", ")})`;
            return `{ const $$pcf = ${pcodeinvk}; return BigInt(${func.invoke.params[0].name}.findKey(${pred}) || -1); }`;
        }
        case "s_list_find_pred_idx": {
            const pcode = resolveCodePack(asm, func.invoke, "p");
            const pcodeinvk = generatePCodeInvokeName(pcode);
            const pred = `($$vv, $$ii) => $$pcf(${["p", "$$vv", "BigInt($$ii)"].join(", ")})`;
            return `{ const $$pcf = ${pcodeinvk}; return BigInt(${func.invoke.params[0].name}.findKey(${pred}) || -1); }`;
        }
        case "s_list_filter_pred": {
            const pcode = resolveCodePack(asm, func.invoke, "p");
            const pcodeinvk = generatePCodeInvokeName(pcode);
            const pred = `($$vv) => $$pcf(${["p", "$$vv"].join(", ")})`;
            return `{ const $$pcf = ${pcodeinvk}; return ${func.invoke.params[0].name}.filter(${pred}); }`;
        }
        case "s_list_filter_pred_idx": {
            const pcode = resolveCodePack(asm, func.invoke, "p");
            const pcodeinvk = generatePCodeInvokeName(pcode);
            const pred = `($$vv, $$ii) => $$pcf(${["p", "$$vv", "BigInt($$ii)"].join(", ")})`;
            return `{ const $$pcf = ${pcodeinvk}; return ${func.invoke.params[0].name}.filter(${pred}); }`;
        }
        case "s_list_filter_map_fn": {
            const pcode = resolveCodePack(asm, func.invoke, "p");
            const pcodeinvk = generatePCodeInvokeName(pcode);
            const pred = `($$vv) => $$pcf(${["p", "$$vv"].join(", ")})`;

            const fcode = resolveCodePack(asm, func.invoke, "f");
            const fcodeinvk = generatePCodeInvokeName(fcode);
            const fn = `($$vv) => $$fcf(${["f", "$$vv"].join(", ")})`;

            return `{ const $$pcf = ${pcodeinvk}; const $$fcf = ${fcodeinvk}; return ${func.invoke.params[0].name}.filter(${pred}).map(${fn}); }`;
        }
        case "s_list_map": {
            const fcode = resolveCodePack(asm, func.invoke, "f");
            const fcodeinvk = generatePCodeInvokeName(fcode);
            const fn = `($$vv) => $$fcf(${["f", "$$vv"].join(", ")})`;

            return `{ const $$fcf = ${fcodeinvk}; return ${func.invoke.params[0].name}.map(${fn}); }`;
        }
        case "s_list_map_idx": {
            const fcode = resolveCodePack(asm, func.invoke, "f");
            const fcodeinvk = generatePCodeInvokeName(fcode);
            const fn = `($$vv, $$ii) => $$fcf(${["f", "$$vv", "BigInt($$ii)"].join(", ")})`;

            return `{ const $$fcf = ${fcodeinvk}; return ${func.invoke.params[0].name}.map(${fn}); }`;
        }
        case "s_list_map_sync": {
            const fcode = resolveCodePack(asm, func.invoke, "f");
            const fcodeinvk = generatePCodeInvokeName(fcode);
            const fn = `($$vv, $$uu) => $$fcf(${["f", "$$vv", "$$uu"].join(", ")})`;

            return `{ const $$fcf = ${fcodeinvk}; return ${func.invoke.params[0].name}.zipWith(${fn}, ${func.invoke.params[1].name}); }`;
        }
        case "s_list_append": {
            return `{ return ${func.invoke.params[0].name}.concat(${func.invoke.params[1].name}); }`;
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
        case "s_list_set": {
            return `{ return ${func.invoke.params[0].name}.set(Number(${func.invoke.params[1].name}), ${func.invoke.params[2].name}); }`;
        }
        case "s_list_insert": {
            return `{ return ${func.invoke.params[0].name}.insert(Number(${func.invoke.params[1].name}), ${func.invoke.params[2].name}); }`;
        }
        case "s_list_remove": {
            return `{ return ${func.invoke.params[0].name}.delete(Number(${func.invoke.params[1].name})); }`;
        }

        case "s_list_keysort": {
            const ttype = asm.typeMap.get(func.invoke.tbinds.get("T") as TIRTypeKey) as TIRType;
            let lt: string = "[UNDEF]";
            let gt: string = "[UNDEF]";

            if(ttype instanceof TIROOType) {
                lt = `($CoreLibs.$KeyLessOps.get("${ttype.tkey}"))(a, b)`;
                gt = `($CoreLibs.$KeyLessOps.get("${ttype.tkey}"))(b, a)`;
            }
            else {
                lt = `$CoreLibs.$KeyLessGeneral(a, b)`;
                gt = `$CoreLibs.$KeyLessGeneral(b, a)`;
            }

            return `{ return ${func.invoke.params[0].name}.sort((a, b) => { if(${lt}) return -1; else if(${gt}) return 1; else return 0; }); }`
        }

        case "s_list_reduce": {
            const pcode = resolveCodePack(asm, func.invoke, "f");
            const pcodeinvk = generatePCodeInvokeName(pcode);
            const op = `($$uu, $$vv) => $$pcf(${["f", "$$uu", "$$vv"].join(", ")})`;
            return `{ const $$pcf = ${pcodeinvk}; return ${func.invoke.params[0].name}.reduce(${op}, ${func.invoke.params[1].name}); }`;
        }
        case "s_list_reduce_idx": {
            const pcode = resolveCodePack(asm, func.invoke, "f");
            const pcodeinvk = generatePCodeInvokeName(pcode);
            const op = `($$uu, $$vv, $$ii) => $$pcf(${["f", "$$uu", "$$vv", "BigInt($$ii)"].join(", ")})`;
            return `{ const $$pcf = ${pcodeinvk}; return ${func.invoke.params[0].name}.reduce(${op}, ${func.invoke.params[1].name}); }`;
        }

        case "s_mapentry_key": {
            return `{ return ${func.invoke.params[0].name}[0]; }`;
        }
        case "s_mapentry_value": {
            return `{ return ${func.invoke.params[0].name}[1]; }`;
        }

        case "s_map_empty": {
            return `{ return ${func.invoke.params[0].name}.size === 0; }`;
        }
        case "s_map_count": {
            return `{ return BigInt(${func.invoke.params[0].name}.size); }`;
        }
        case "s_map_has": {
            return `{ return ${func.invoke.params[0].name}.has(${func.invoke.params[1].name}); }`;
        }
        case "s_map_get": {
            return `{ return ${func.invoke.params[0].name}.get(${func.invoke.params[1].name}); }`;
        }
        case "s_map_entries": {
            return `{ return ${func.invoke.params[0].name}.entrySeq().toList(); }`;
        }

        case "s_while": {
            const pcode = resolveCodePack(asm, func.invoke, "p");
            const pcodeinvk = generatePCodeInvokeName(pcode);

            const fcode = resolveCodePack(asm, func.invoke, "op");
            const fcodeinvk = generatePCodeInvokeName(fcode);

            return `{ var state = ${func.invoke.params[0].name}; const $$pcf = ${pcodeinvk}; const $$fcf = ${fcodeinvk}; while ($$pcf(p, state)) { state = $$fcf(op, state); } return state; }`;
        }

        default: {
            return "[UNKNOWN PRIMITIVE FUNCTION]";
        }
    }
}

export {
    emitBuiltinNamespaceFunction, emitBuiltinMemberFunction
}