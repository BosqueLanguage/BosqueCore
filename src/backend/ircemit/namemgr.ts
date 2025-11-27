
const s_coloncolon_repl = "ᕒ";
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
        const bb = cstr.replace(/::/g, s_coloncolon_repl)
            .replace(/, */g, s_comma_repl)
            .replace(/\(|/g, "ᐸRuntimeᐳ::EList<")
            .replace(/|\)/g, ">");

        if(!bb.startsWith("BSQ_")) {
            return bb;
        }
        else {
            return "BSQ_" + s_BSQ_tag + bb.slice(3);
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

    private static convertIdentifier(vname: string): string {
        let nn = TransformCPPNameManager.safeifyName(vname);

        if(!nn.startsWith("$")) {
            return TransformCPPNameManager.safeifyName(vname);
        }
        else {
            return s_binderv_tag + TransformCPPNameManager.safeifyName(vname.slice(1));
        }
    }

    public static convertNamespaceKey(nskey: string): string {
        return TransformCPPNameManager.safeifyName(nskey);
    }

    public static convertTypeKey(tkey: string): string {
        return TransformCPPNameManager.safeifyName(tkey);
    }

    public static convertInvokeKey(ikey: string): string {
        return TransformCPPNameManager.safeifyName(ikey);
    }

    public static generateNameForUnionMember(tkey: string): string {
        return TransformCPPNameManager.convertTypeKey(tkey) + s_specialop_sep + "um";
    }

    public static generateTypeInfoNameForTypeKey(tkey: string): string {
        return `${s_runtimename}::g_typeinfo_${TransformCPPNameManager.convertTypeKey(tkey)}`;
    }

    public static generateNameForInvariantFunction(tkey: string): string {
        return TransformCPPNameManager.convertTypeKey(tkey) + s_specialop_sep + "invariant";
    }

    public static generateNameForFieldDefaultFunction(tkey: string, fname: string): string {
        return TransformCPPNameManager.convertTypeKey(tkey) + s_specialop_sep + "default" + s_specialop_sep + TransformCPPNameManager.safeifyName(fname);
    }
}

export {
    TransformCPPNameManager
};
