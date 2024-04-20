
import { FullyQualifiedNamespace, SourceInfo } from "../build_decls";

abstract class TypeSignature {
    readonly sinfo: SourceInfo;

    constructor(sinfo: SourceInfo) {
        this.sinfo = sinfo;
    }

    abstract emit(): string;
}

class ErrorTypeSignature extends TypeSignature {
    constructor(sinfo: SourceInfo) {
        super(sinfo);
    }

    emit(): string {
        return "[Parse Error]";
    }
}

class AutoTypeSignature extends TypeSignature {
    constructor(sinfo: SourceInfo) {
        super(sinfo);
    }

    emit(): string {
        return "[Auto Type]";
    }
}

class TemplateTypeSignature extends TypeSignature {
    readonly name: string;

    constructor(sinfo: SourceInfo, name: string) {
        super(sinfo);
        this.name = name;
    }

    emit(): string {
        return this.name;
    }
}

class NominalTypeSignature extends TypeSignature {
    readonly ns: FullyQualifiedNamespace;
    readonly tscope: {tname: string, terms: TypeSignature[]}[];

    constructor(sinfo: SourceInfo, ns: FullyQualifiedNamespace, tscope: {tname: string, terms: TypeSignature[]}[]) {
        super(sinfo);
        this.ns = ns;
        this.tscope = tscope;
    }

    emit(): string {
        const rrtscope = this.tscope.map((t) => t.tname + (t.terms.length !== 0 ? ("<" + t.terms.map((tt) => tt.emit()).join(", ") + ">") : ""));
        return (this.ns !== "Core" ? (this.ns + "::") : "") + rrtscope.join("::");
    }
}

class TupleTypeSignature extends TypeSignature {
    readonly entries: TypeSignature[];

    constructor(sinfo: SourceInfo, entries: TypeSignature[]) {
        super(sinfo);
        this.entries = entries;
    }

    emit(): string {
        return "[" + this.entries.map((tt) => tt.emit()).join(", ") + "]";
    }
}

class RecordTypeSignature extends TypeSignature {
    readonly entries: [string, TypeSignature][];

    constructor(sinfo: SourceInfo, entries: [string, TypeSignature][]) {
        super(sinfo);
        this.entries = entries;
    }

    emit(): string {
        return "{" + this.entries.map((tt) => (tt[0] + ": " + tt[1].emit())).join(", ") + "}";
    }
}

class EListTypeSignature extends TypeSignature {
    readonly entries: TypeSignature[];

    constructor(sinfo: SourceInfo, entries: TypeSignature[]) {
        super(sinfo);
        this.entries = entries;
    }

    emit(): string {
        return "[" + this.entries.map((tt) => tt.emit()).join(", ") + "]";
    }
}

class StringTemplateType extends TypeSignature {
    readonly kind: "ascii" | "utf8";
    readonly argtypes: TypeSignature[];

    constructor(sinfo: SourceInfo, kind: "ascii" | "utf8", argtypes: TypeSignature[]) {
        super(sinfo);
        this.kind = kind;
        this.argtypes = argtypes;
    }

    emit(): string {
        const sk = this.kind === "ascii" ? "ASCIIStringTemplate" : "StringTemplate";
        const uu = this.argtypes.map((tt) => tt.emit()).join(", ");

        return `${sk}<${uu}>`;
    }
}

type RecursiveAnnotation = "yes" | "no" | "cond";

class FunctionParameter {
    readonly name: string;
    readonly type: TypeSignature;
    readonly isRefParam: boolean;
    readonly isSpreadParam: boolean;

    constructor(name: string, type: TypeSignature, isRefParam: boolean, isSpreadParam: boolean) {
        this.name = name;
        this.type = type;
        this.isRefParam = isRefParam;
        this.isSpreadParam = isSpreadParam;
    }

    emit(): string {
        return `${(this.isRefParam ? "ref " : "")}${this.isSpreadParam ? "..." : ""}${this.name}: ${this.type.emit()}`;
    }
}

class LambdaTypeSignature extends TypeSignature {
    readonly recursive: RecursiveAnnotation;
    readonly name: "fn" | "pred";
    readonly params: FunctionParameter[];
    readonly resultType: TypeSignature | undefined;

    constructor(sinfo: SourceInfo, recursive: RecursiveAnnotation, name: "fn" | "pred", params: FunctionParameter[], resultType: TypeSignature | undefined) {
        super(sinfo);
        this.recursive = recursive;
        this.name = name;
        this.params = params;
        this.resultType = resultType;
    }

    emit(): string {
        return `${this.recursive === "yes" ? "rec " : ""}${this.name}(${this.params.map((pp) => pp.emit()).join(", ")}): ${this.resultType ? this.resultType.emit() : "void"}`;
    }
}

class ProjectTypeSignature extends TypeSignature {
    readonly fromtype: TypeSignature;
    readonly oftype: TypeSignature;

    constructor(sinfo: SourceInfo, fromtype: TypeSignature, oftype: TypeSignature) {
        super(sinfo);
        this.fromtype = fromtype;
        this.oftype = oftype;
    }

    emit(): string {
        return this.fromtype + "!" + this.oftype;
    }
}

class AndTypeSignature extends TypeSignature {
    readonly types: TypeSignature[];

    constructor(sinfo: SourceInfo, types: TypeSignature[]) {
        super(sinfo);
        this.types = types;
    }

    emit(): string {
        return this.types.map((tt) => tt.emit()).join("&");
    }
}

class UnionTypeSignature extends TypeSignature {
    readonly types: TypeSignature[];

    constructor(sinfo: SourceInfo, types: TypeSignature[]) {
        super(sinfo);
        this.types = types;
    }

    emit(): string {
        return this.types.map((tt) => tt.emit()).join(" | ");
    }
}

export { 
    TypeSignature, ErrorTypeSignature, AutoTypeSignature, 
    TemplateTypeSignature, NominalTypeSignature, 
    TupleTypeSignature, RecordTypeSignature, EListTypeSignature, StringTemplateType,
    RecursiveAnnotation, FunctionParameter, LambdaTypeSignature, ProjectTypeSignature, AndTypeSignature, UnionTypeSignature
};
