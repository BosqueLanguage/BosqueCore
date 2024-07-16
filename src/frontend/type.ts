import { SourceInfo } from "./build_decls.js";
import { AbstractNominalTypeDecl, OptionTypeDecl, TemplateTermDecl } from "./assembly.js";

class FullyQualifiedNamespace {
    readonly ns: string[];

    constructor(ns: string[]) {
        this.ns = ns;
    }

    emit(): string {
        if(this.ns.length === 0) {
            return "";
        }
        else if(this.ns[0] === "Core") {
            return this.ns.slice(1).join("::");
        }
        else {
            return this.ns.join("::");
        }
    }
}

class TemplateConstraintScope {
    constraints: TemplateTermDecl[][] = [];

    constructor() {
    }

    pushConstraintScope(constraints: TemplateTermDecl[]) {
        this.constraints.push([...constraints]);
    }

    popConstraintScope() {
        this.constraints.pop();
    }

    resolveConstraint(name: string): TemplateTermDecl | undefined {
        for(let i = this.constraints.length - 1; i >= 0; ++i) {
            const res = this.constraints[i].find((cc) => cc.name === name);
            if(res !== undefined) {
                return res;
            }
        }
        
        return undefined;
    }
}

class TemplateNameMapper {
    readonly mapper: Map<string, TypeSignature>[];

    constructor(mapper: Map<string, TypeSignature>[]) {
        this.mapper = mapper;
    }

    static identicalMappings(m1: TemplateNameMapper, m2: TemplateNameMapper): boolean {
        if(m1.mapper.length !== m2.mapper.length) {
            return false;
        }

        for(let i = 0; i < m1.mapper.length; ++i) {
            if(m1.mapper[i].size !== m2.mapper[i].size) {
                return false;
            }

            const mm1 = [...m1.mapper[i]].sort((a, b) => a[0].localeCompare(b[0]));
            const mm2 = [...m2.mapper[i]].sort((a, b) => a[0].localeCompare(b[0]));

            for(let j = 0; j < mm1.length; ++j) {
                if(mm1[j][0] !== mm2[j][0] || mm1[j][1].tkeystr !== mm2[j][1].tkeystr) {
                    return false;
                }
            }
        }

        return true;
    }

    static createEmpty(): TemplateNameMapper {
        return new TemplateNameMapper([]);
    }

    static createInitialMapping(mapping: Map<string, TypeSignature>): TemplateNameMapper {
        return new TemplateNameMapper([mapping]);
    }

    static merge(m1: TemplateNameMapper, m2: TemplateNameMapper): TemplateNameMapper {
        return new TemplateNameMapper([...m1.mapper, ...m2.mapper]);
    }

    resolveTemplateMapping(ttype: TemplateTypeSignature): TypeSignature {
        for(let i = this.mapper.length - 1; i >= 0; --i) {
            const res = this.mapper[i].get(ttype.name);
            if(res !== undefined) {
                if(res instanceof TemplateTypeSignature) {
                    ttype = res;
                }
                else {
                    return res;
                }
            }
        }
        
        return ttype;
    }
}

abstract class TypeSignature {
    readonly sinfo: SourceInfo;
    readonly tkeystr: string;

    constructor(sinfo: SourceInfo, tkeystr: string) {
        this.sinfo = sinfo;
        this.tkeystr = tkeystr;
    }

    abstract remapTemplateBindings(mapper: TemplateNameMapper): TypeSignature;
}

class ErrorTypeSignature extends TypeSignature {
    readonly completionNamespace: FullyQualifiedNamespace | undefined;

    constructor(sinfo: SourceInfo, completionNamespace: FullyQualifiedNamespace | undefined) {
        super(sinfo, "^error^");

        this.completionNamespace = completionNamespace;
    }

    remapTemplateBindings(mapper: TemplateNameMapper): TypeSignature {
        return this;
    }
}

class VoidTypeSignature extends TypeSignature {
    constructor(sinfo: SourceInfo) {
        super(sinfo, "Void");
    }

    remapTemplateBindings(mapper: TemplateNameMapper): TypeSignature {
        return this;
    }
}

class AutoTypeSignature extends TypeSignature {
    constructor(sinfo: SourceInfo) {
        super(sinfo, "^auto^");
    }

    remapTemplateBindings(mapper: TemplateNameMapper): TypeSignature {
        return this;
    }
}

class TemplateTypeSignature extends TypeSignature {
    readonly name: string;

    constructor(sinfo: SourceInfo, name: string) {
        super(sinfo, name);
        this.name = name;
    }

    remapTemplateBindings(mapper: TemplateNameMapper): TypeSignature {
        return mapper.resolveTemplateMapping(this);
    }
}

class NominalTypeSignature extends TypeSignature {
    readonly decl: AbstractNominalTypeDecl;
    readonly alltermargs: TypeSignature[];

    private static computeTKeyStr(decl: AbstractNominalTypeDecl, alltermargs: TypeSignature[]): string {
        const tscope = alltermargs.length !== 0 ? ("<" + alltermargs.map((tt) => tt.tkeystr).join(", ") + ">") : "";
        if(decl instanceof OptionTypeDecl) {
            const oftype = alltermargs[0].tkeystr;
            if(!oftype.endsWith("?")) {
                return `${oftype}?`
            }
            else {
                return `Option<${oftype}>`;
            }
        }
        else if(decl.isSpecialResultEntity()) {
            return `Result${tscope}::${decl.name}`;
        }
        else if(decl.isSpecialAPIResultEntity()) {
            return `APIResult${tscope}::${decl.name}`;
        }
        else {
            let nscope: string;
            if(decl.ns.ns[0] === "Core") {
                nscope = decl.ns.ns.slice(1).join("::");
            }
            else {
                nscope = decl.ns.ns.join("::");
            }

            return nscope + (nscope !== "" ? "::" : "") + decl.name + tscope;
        }
    }

    constructor(sinfo: SourceInfo, decl: AbstractNominalTypeDecl, alltermargs: TypeSignature[]) {
        super(sinfo, NominalTypeSignature.computeTKeyStr(decl, alltermargs));
        this.decl = decl;
        this.alltermargs = alltermargs;
    }

    remapTemplateBindings(mapper: TemplateNameMapper): TypeSignature {
        const rtall = this.alltermargs.map((tt) => tt.remapTemplateBindings(mapper));

        return new NominalTypeSignature(this.sinfo, this.decl, rtall);
    }
}

class EListTypeSignature extends TypeSignature {
    readonly entries: TypeSignature[];

    constructor(sinfo: SourceInfo, entries: TypeSignature[]) {
        super(sinfo, "(" + entries.map((tt) => tt.tkeystr).join(", ") + ")");
        this.entries = entries;
    }

    remapTemplateBindings(mapper: TemplateNameMapper): TypeSignature {
        return new EListTypeSignature(this.sinfo, this.entries.map((tt) => tt.remapTemplateBindings(mapper)));
    }
}

class StringTemplateTypeSignature extends TypeSignature {
    readonly kind: "chars" | "utf8";
    readonly argtypes: TypeSignature[];

    constructor(sinfo: SourceInfo, kind: "chars" | "utf8", argtypes: TypeSignature[]) {
        super(sinfo, (kind === "chars" ? "CStringTemplate" : "StringTemplate") + "<" + argtypes.map((tt) => tt.tkeystr).join(", ") + ">");
        this.kind = kind;
        this.argtypes = argtypes;
    }

    remapTemplateBindings(mapper: TemplateNameMapper): TypeSignature {
        return new StringTemplateTypeSignature(this.sinfo, this.kind, this.argtypes.map((tt) => tt.remapTemplateBindings(mapper)));
    }
}

type RecursiveAnnotation = "yes" | "no" | "cond";

class LambdaParameterSignature {
    readonly type: TypeSignature;
    readonly isRefParam: boolean;
    readonly isRestParam: boolean;

    constructor(type: TypeSignature, isRefParam: boolean, isRestParam: boolean) {
        this.type = type;
        this.isRefParam = isRefParam;
        this.isRestParam = isRestParam;
    }

    emit(): string {
        return `${(this.isRefParam ? "ref " : "")}${this.isRestParam ? "..." : ""}${this.type.tkeystr}`;
    }
}

class LambdaTypeSignature extends TypeSignature {
    readonly recursive: RecursiveAnnotation;
    readonly name: "fn" | "pred";
    readonly params: LambdaParameterSignature[];
    readonly resultType: TypeSignature;

    constructor(sinfo: SourceInfo, recursive: RecursiveAnnotation, name: "fn" | "pred", params: LambdaParameterSignature[], resultType: TypeSignature) {
        super(sinfo, `${recursive === "yes" ? "rec " : ""}${name}(${params.map((pp) => pp.emit()).join(", ")}): ${resultType.tkeystr}`);
        this.recursive = recursive;
        this.name = name;
        this.params = params;
        this.resultType = resultType;
    }

    remapTemplateBindings(mapper: TemplateNameMapper): TypeSignature {
        const rbparams = this.params.map((pp) => new LambdaParameterSignature(pp.type.remapTemplateBindings(mapper), pp.isRefParam, pp.isRestParam));
        return new LambdaTypeSignature(this.sinfo, this.recursive, this.name, rbparams, this.resultType.remapTemplateBindings(mapper));
    }
}

export {
    FullyQualifiedNamespace, TemplateConstraintScope, TemplateNameMapper,
    TypeSignature, ErrorTypeSignature, VoidTypeSignature, AutoTypeSignature, 
    TemplateTypeSignature, NominalTypeSignature, 
    EListTypeSignature, StringTemplateTypeSignature,
    RecursiveAnnotation, LambdaParameterSignature, LambdaTypeSignature
};
