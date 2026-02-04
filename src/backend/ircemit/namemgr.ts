
const s_coloncolon_repl = "ᕒ";
const s_hash_repl = "ᙾ";
const s_comma_repl = "ᐪ";
const s_BSQ_tag = "ᗑ";

const s_binderv_tag = "ᑯ";
const s_specialop_sep = "ᐤ";

const s_runtimename = "ᐸRuntimeᐳ";

class TransformCPPNameManager {
    static c_dangerous: Map<string, string> = new Map<string, string>([
        ["this", "ᐸthisᐳ"]
    ]);

    private static resymbol(cstr: string): string {
        const bb = cstr
            .replace(/::/g, s_coloncolon_repl)
            .replace(/#/g, s_hash_repl)
            .replace(/, */g, s_comma_repl)
            .replace(/</g, "ᐸ")
            .replace(/>/g, "ᐳ")
            .replace(/\[/g, "ᑅ")
            .replace(/\]/g, "ᑀ")
            .replace(/\(\|/g, "ᐸRuntimeᐳ::EList<")
            .replace(/\|\)/g, ">");

        if(bb.startsWith("lambda_")) {
            return "lambda_" + s_BSQ_tag + bb.slice(6);
        }
        else if(bb.startsWith("BSQ_")) {
            return "BSQ_" + s_BSQ_tag + bb.slice(3);
        }
        else if(bb.startsWith("MINT_")) {
            return "MINT_" + s_BSQ_tag + bb.slice(4);
        }
        else {
            return bb;
        }
    }

    private static safeifyName(name: string): string {
        const nn = TransformCPPNameManager.c_dangerous.get(name);
        if(nn !== undefined) {
            return nn;
        }
        else {
            return this.resymbol(name);
        }    
    }

    static convertIdentifier(vname: string): string {
        let nn = TransformCPPNameManager.safeifyName(vname);

        if(!nn.startsWith("$")) {
            return TransformCPPNameManager.safeifyName(vname);
        }
        else {
            return s_binderv_tag + TransformCPPNameManager.safeifyName(vname.slice(1));
        }
    }

    static convertNamespaceKey(nskey: string): string {
        return TransformCPPNameManager.safeifyName(nskey);
    }

    static convertTypeKey(tkey: string): string {
        return TransformCPPNameManager.safeifyName(tkey);
    }

    static convertInvokeKey(ikey: string): string {
        return TransformCPPNameManager.safeifyName(ikey);
    }

    static generateNameForUnionType(tkey: string): string {
        return `${TransformCPPNameManager.convertTypeKey(tkey)}${s_specialop_sep}Union`;
    }

    static generateNameForUnionMember(tkey: string): string {
        return `u_${TransformCPPNameManager.convertTypeKey(tkey)}`;
    }

    static generateTypeInfoNameForTypeKey(tkey: string): string {
        return `${s_runtimename}::g_typeinfo_${TransformCPPNameManager.convertTypeKey(tkey)}`;
    }

    static generateNameForConstantKey(constkey: string): string {
        return TransformCPPNameManager.safeifyName(constkey);
    }

    static generateNameForEnumKey(tkey: string, emember: string): string {
        return TransformCPPNameManager.convertTypeKey(tkey) + "::" + TransformCPPNameManager.safeifyName(emember);
    }

    static generateNameForConstructor(tkey: string): string {
        return TransformCPPNameManager.convertTypeKey(tkey);
    }

    static generateNameForInvariantFunction(tkey: string, invariantidx: number): string {
        return TransformCPPNameManager.convertTypeKey(tkey) + s_specialop_sep + "invariant_" + invariantidx;
    }

    static generateNameForValidateFunction(tkey: string, invariantidx: number): string {
        return TransformCPPNameManager.convertTypeKey(tkey) + s_specialop_sep + "validate_" + invariantidx;
    }

    static generateNameForBSQONParseFunction(tkey: string): string {
        return TransformCPPNameManager.convertTypeKey(tkey) + s_specialop_sep + "bsqparse";
    }

    static generateNameForBSQONEmitFunction(tkey: string): string {
        return TransformCPPNameManager.convertTypeKey(tkey) + s_specialop_sep + "bsqemit";
    }

    static generateNameForFieldDefaultFunction(tkey: string, fname: string): string {
        return TransformCPPNameManager.convertTypeKey(tkey) + s_specialop_sep + "default" + s_specialop_sep + TransformCPPNameManager.safeifyName(fname);
    }

    static generateNameForInvokePreconditionCheck(ikey: string, requiresidx: number): string {
        return TransformCPPNameManager.convertInvokeKey(ikey) + s_specialop_sep + "requires_" + requiresidx;
    }

    static generateNameForInvokePostconditionCheck(ikey: string, ensuresidx: number): string {
        return TransformCPPNameManager.convertInvokeKey(ikey) + s_specialop_sep + "ensures_" + ensuresidx;
    }
}

export {
    TransformCPPNameManager
};
