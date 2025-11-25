
const s_coloncolon_repl = xxxx;
const s_comma_repl = xxxx;
const s_BSQ_tag = xxxx;

const s_binderv_tag = xxxx;
const s_specialop_sep = xxxx;

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
            return nn;
        }
        else {
            return s_binderv_tag + nn.slice(1)
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

    public static generateNameForInvariantFunction(tkey: string): string {
        return TransformCPPNameManager.convertTypeKey(tkey) + s_specialop_sep + "invariant";
    }

    public static generateNameForFieldDefaultFunction(tkey: string, fname: string): string {
        return TransformCPPNameManager.convertTypeKey(tkey) + s_specialop_sep + "default" + TransformCPPNameManager.safeifyName(fname);
    }
}

export {
    TransformCPPNameManager
};
