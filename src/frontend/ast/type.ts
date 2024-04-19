
import { SourceInfo } from "../build_decls";

class TypeSignature {
    readonly sinfo: SourceInfo;

    constructor(sinfo: SourceInfo) {
        this.sinfo = sinfo;
    }

    emit(): string {
        return "[Missing Implementation]";
    }
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

    getDiagnosticName(): string {
        return "[Auto Type]";
    }
}

class TemplateTypeSignature extends TypeSignature {
    readonly name: string;

    constructor(sinfo: SourceInfo, name: string) {
        super(sinfo);
        this.name = name;
    }

    getDiagnosticName(): string {
        return this.name;
    }
}

class NominalTypeSignature extends TypeSignature {
    readonly nameSpace: string;
    readonly tnames: string[];
    readonly terms: TypeSignature[];

    constructor(sinfo: SourceInfo, ns: string, tnames: string[], terms?: TypeSignature[]) {
        super(sinfo);
        this.nameSpace = ns;
        this.tnames = tnames;
        this.terms = terms || [];
    }

    computeResolvedName(): string {
        return this.tnames.join("::");
    }

    getDiagnosticName(): string {
        return (this.nameSpace !== "Core" ? (this.nameSpace + "::") : "") + this.tnames.join("::") + (this.terms.length !== 0 ? ("<" + this.terms.map((tt) => tt.getDiagnosticName()).join(", ") + ">") : "");
    }
}

class TupleTypeSignature extends TypeSignature {
    readonly entries: TypeSignature[];

    constructor(sinfo: SourceInfo, entries: TypeSignature[]) {
        super(sinfo);
        this.entries = entries;
    }

    getDiagnosticName(): string {
        return "[" + this.entries.map((tt) => tt.getDiagnosticName()).join(", ") + "]";
    }
}

class RecordTypeSignature extends TypeSignature {;
    readonly entries: [string, TypeSignature][];

    constructor(sinfo: SourceInfo, entries: [string, TypeSignature][]) {
        super(sinfo);
        this.entries = entries;
    }

    getDiagnosticName(): string {
        return "{" + this.entries.map((tt) => (tt[0] + ": " + tt[1].getDiagnosticName())).join(", ") + "}";
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
        return `${(this.isRefParam ? "ref " : "")}${this.isSpreadParam ? "..." : ""}${this.name}:${this.type.emit()}`;
    }
}

class LambdaTypeSignature extends TypeSignature {
    readonly recursive: RecursiveAnnotation;
    readonly params: FunctionParameter[];
    readonly resultType: TypeSignature;

    constructor(sinfo: SourceInfo, recursive: RecursiveAnnotation, params: FunctionParameter[], resultType: TypeSignature) {
        super(sinfo);
        this.recursive = recursive;
        this.params = params;
        this.resultType = resultType;
    }

    getDiagnosticName(): string {
        return (this.isPred ? "pred" : "fn") + (this.isThisRef ? "ref(" : " (") + this.params.map((param) => param.type.getDiagnosticName()).join(", ") + ") -> " + this.resultType.getDiagnosticName();
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

    getDiagnosticName(): string {
        return this.fromtype + "!" + this.oftype;
    }
}

class AndTypeSignature extends TypeSignature {
    readonly types: TypeSignature[];

    constructor(sinfo: SourceInfo, types: TypeSignature[]) {
        super(sinfo);
        this.types = types;
    }

    getDiagnosticName(): string {
        return this.types.map((tt) => tt.getDiagnosticName()).join("&");
    }
}

class UnionTypeSignature extends TypeSignature {
    readonly types: TypeSignature[];

    constructor(sinfo: SourceInfo, types: TypeSignature[]) {
        super(sinfo);
        this.types = types;
    }

    getDiagnosticName(): string {
        return this.types.map((tt) => tt.getDiagnosticName()).join(" | ");
    }
}

export { 
    TypeSignature, ParseErrorTypeSignature, AutoTypeSignature, 
    TemplateTypeSignature, NominalTypeSignature, 
    TupleTypeSignature, RecordTypeSignature,
    RecursiveAnnotation, FunctionParameter, FunctionTypeSignature, ProjectTypeSignature, AndTypeSignature, UnionTypeSignature
};
