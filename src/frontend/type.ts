
import { SourceInfo } from "./build_decls";
import { AbstractNominalTypeDecl } from "./assembly";

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

abstract class TypeSignature {
    readonly sinfo: SourceInfo;

    constructor(sinfo: SourceInfo) {
        this.sinfo = sinfo;
    }

    abstract emit(toplevel: boolean): string;
}

class ErrorTypeSignature extends TypeSignature {
    readonly completionNamespace: FullyQualifiedNamespace | undefined;

    constructor(sinfo: SourceInfo, completionNamespace: FullyQualifiedNamespace | undefined) {
        super(sinfo);

        this.completionNamespace = completionNamespace;
    }

    emit(toplevel: boolean): string {
        return `[Parse Error] @ ${this.completionNamespace ? this.completionNamespace.emit() + "::" : ""}?`;
    }
}

class VoidTypeSignature extends TypeSignature {
    constructor(sinfo: SourceInfo) {
        super(sinfo);
    }

    emit(toplevel: boolean): string {
        return "[Void Type]";
    }
}

class AutoTypeSignature extends TypeSignature {
    constructor(sinfo: SourceInfo) {
        super(sinfo);
    }

    emit(toplevel: boolean): string {
        return "[Auto Type]";
    }
}

class TemplateTypeSignature extends TypeSignature {
    readonly name: string;

    constructor(sinfo: SourceInfo, name: string) {
        super(sinfo);
        this.name = name;
    }

    emit(toplevel: boolean): string {
        return this.name;
    }
}

class NominalTypeSignature extends TypeSignature {
    readonly ns: string[];
    readonly tscope: {tname: string, terms: TypeSignature[]}[];

    readonly resolvedTerms: {name: string, type: TypeSignature}[];
    readonly resolvedTypeSignature: TypeSignature | undefined;
    readonly typeDeclaration: AbstractNominalTypeDecl | undefined;

    constructor(sinfo: SourceInfo, ns: string[], tscope: {tname: string, terms: TypeSignature[]}[], resolvedTerms: {name: string, type: TypeSignature}[], resolvedTypeSignature: TypeSignature | undefined, typeDeclaration: AbstractNominalTypeDecl | undefined) {
        super(sinfo);
        this.ns = ns;
        this.tscope = tscope;

        this.resolvedTerms = resolvedTerms;
        this.resolvedTypeSignature = resolvedTypeSignature;
        this.typeDeclaration = typeDeclaration;
    }

    emit(toplevel: boolean): string {
        let nscope: string;
        if(this.ns.length === 0) {
            nscope = "";
        }
        else if(this.ns.length !== 0 && this.ns[0] === "Core") {
            nscope = this.ns.slice(1).join("::") + "::";
        }
        else {
            nscope = this.ns.join("::") + "::";
        }

        const rrtscope = this.tscope.map((t) => t.tname + (t.terms.length !== 0 ? ("<" + t.terms.map((tt) => tt.emit(true)).join(", ") + ">") : ""));
        return nscope + rrtscope.join("::");
    }
}

class TupleTypeSignature extends TypeSignature {
    readonly entries: TypeSignature[];

    constructor(sinfo: SourceInfo, entries: TypeSignature[]) {
        super(sinfo);
        this.entries = entries;
    }

    emit(toplevel: boolean): string {
        return "[" + this.entries.map((tt) => tt.emit(true)).join(", ") + "]";
    }
}

class RecordTypeSignature extends TypeSignature {
    readonly entries: [string, TypeSignature][];

    constructor(sinfo: SourceInfo, entries: [string, TypeSignature][]) {
        super(sinfo);
        this.entries = entries;
    }

    emit(toplevel: boolean): string {
        return "{" + this.entries.map((tt) => (tt[0] + ": " + tt[1].emit(true))).join(", ") + "}";
    }
}

class EListTypeSignature extends TypeSignature {
    readonly entries: TypeSignature[];

    constructor(sinfo: SourceInfo, entries: TypeSignature[]) {
        super(sinfo);
        this.entries = entries;
    }

    emit(toplevel: boolean): string {
        return "(" + this.entries.map((tt) => tt.emit(true)).join(", ") + ")";
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

    emit(toplevel: boolean): string {
        const sk = this.kind === "ascii" ? "ASCIIStringTemplate" : "StringTemplate";
        const uu = this.argtypes.map((tt) => tt.emit(true)).join(", ");

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
        return `${(this.isRefParam ? "ref " : "")}${this.isSpreadParam ? "..." : ""}${this.name}: ${this.type.emit(true)}`;
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

    emit(toplevel: boolean): string {
        return `${this.recursive === "yes" ? "rec " : ""}${this.name}(${this.params.map((pp) => pp.emit()).join(", ")}): ${this.resultType ? this.resultType.emit(true) : "void"}`;
    }
}

class AndTypeSignature extends TypeSignature {
    readonly ltype: TypeSignature;
    readonly rtype: TypeSignature;

    constructor(sinfo: SourceInfo, ltype: TypeSignature, rtype: TypeSignature) {
        super(sinfo);
        this.ltype = ltype;
        this.rtype = rtype;
    }

    emit(toplevel: boolean): string {
        const bb = this.ltype.emit(false) + " & " + this.rtype.emit(false);
        return (toplevel) ? bb : "(" + bb + ")";
    }
}

class NoneableTypeSignature extends TypeSignature {
    readonly type: TypeSignature;

    constructor(sinfo: SourceInfo, type: TypeSignature) {
        super(sinfo);
        this.type = type;
    }

    emit(toplevel: boolean): string {
        return this.type.emit(false) + "?";
    }
}

class UnionTypeSignature extends TypeSignature {
    readonly ltype: TypeSignature;
    readonly rtype: TypeSignature;

    constructor(sinfo: SourceInfo, ltype: TypeSignature, rtype: TypeSignature) {
        super(sinfo);
        this.ltype = ltype;
        this.rtype = rtype;
    }

    emit(toplevel: boolean): string {
        const bb = this.ltype.emit(false) + " | " + this.rtype.emit(false);
        return (toplevel) ? bb : "(" + bb + ")";
    }
}

export {
    FullyQualifiedNamespace,
    TypeSignature, ErrorTypeSignature, VoidTypeSignature, AutoTypeSignature, 
    TemplateTypeSignature, NominalTypeSignature, 
    TupleTypeSignature, RecordTypeSignature, EListTypeSignature, StringTemplateType,
    RecursiveAnnotation, FunctionParameter, LambdaTypeSignature, AndTypeSignature, NoneableTypeSignature, UnionTypeSignature
};
