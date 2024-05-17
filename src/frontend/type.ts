import {strict as assert} from "assert";

import { SourceInfo } from "./build_decls";
import { AbstractNominalTypeDecl, NamespaceTypedef } from "./assembly";

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

class TemplateBindingScope {
    readonly typebinds: Map<string, TypeSignature>;
    readonly invokebinds: Map<string, TypeSignature>;

    readonly constraints: Map<string, TypeSignature>;

    constructor(typebinds: Map<string, TypeSignature>, invokebinds: Map<string, TypeSignature>, constraints: Map<string, TypeSignature>) {
        this.typebinds = typebinds;
        this.invokebinds = invokebinds;
        
        this.constraints = constraints;
    }

    static createEmptyScope(): TemplateBindingScope {
        return new TemplateBindingScope(new Map<string, TypeSignature>(), new Map<string, TypeSignature>(), new Map<string, TypeSignature>());
    }

    resolveTypeBinding(name: string): TypeSignature {
        assert(this.invokebinds.has(name) || this.typebinds.has(name), `Type binding ${name} not found in scope`);

        let rtype = this.invokebinds.has(name) ? this.invokebinds.get(name) as TypeSignature : new TemplateTypeSignature(SourceInfo.implicitSourceInfo(), name);

        if(rtype instanceof TemplateTypeSignature && this.typebinds.has(rtype.name)) {
            return this.typebinds.get(rtype.name) as TypeSignature;
        }
        else {
            return rtype;
        }
    }

    resolveConstraint(name: string): TypeSignature {
        assert(this.constraints.has(name), `Constraint ${name} not found in scope`);

        return this.constraints.get(name) as TypeSignature;
    }
}

abstract class TypeSignature {
    readonly sinfo: SourceInfo;

    constructor(sinfo: SourceInfo) {
        this.sinfo = sinfo;
    }

    abstract emit(toplevel: boolean): string;

    abstract remapTemplateBindings(bindings: TemplateBindingScope): TypeSignature;
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

    remapTemplateBindings(bindings: TemplateBindingScope): TypeSignature {
        return this;
    }
}

class VoidTypeSignature extends TypeSignature {
    constructor(sinfo: SourceInfo) {
        super(sinfo);
    }

    emit(toplevel: boolean): string {
        return "[Void Type]";
    }

    remapTemplateBindings(bindings: TemplateBindingScope): TypeSignature {
        return this;
    }
}

class AutoTypeSignature extends TypeSignature {
    constructor(sinfo: SourceInfo) {
        super(sinfo);
    }

    emit(toplevel: boolean): string {
        return "[Auto Type]";
    }

    remapTemplateBindings(bindings: TemplateBindingScope): TypeSignature {
        return this;
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

    remapTemplateBindings(bindings: TemplateBindingScope): TypeSignature {
        return bindings.resolveTypeBinding(this.name);
    }
}

class NominalTypeSignature extends TypeSignature {
    readonly ns: string[];
    readonly tscope: {tname: string, terms: TypeSignature[]}[];

    readonly resolvedTerms: {name: string, type: TypeSignature}[];
    readonly resolvedTypedef: NamespaceTypedef | undefined;
    readonly resolvedDeclaration: AbstractNominalTypeDecl | undefined;

    constructor(sinfo: SourceInfo, ns: string[], tscope: {tname: string, terms: TypeSignature[]}[], resolvedTerms: {name: string, type: TypeSignature}[], resolvedTypedef: NamespaceTypedef | undefined, resolvedDeclaration: AbstractNominalTypeDecl | undefined) {
        super(sinfo);
        this.ns = ns;
        this.tscope = tscope;

        this.resolvedTerms = resolvedTerms;
        this.resolvedTypedef = resolvedTypedef;
        this.resolvedDeclaration = resolvedDeclaration;
    }

    emit(toplevel: boolean): string {
        let nscope: string;
        if(this.ns.length === 0) {
            nscope = "";
        }
        else {
            nscope = this.ns.join("::") + "::";
        }

        const rrtscope = this.tscope.map((t) => t.tname + (t.terms.length !== 0 ? ("<" + t.terms.map((tt) => tt.emit(true)).join(", ") + ">") : ""));
        return nscope + rrtscope.join("::");
    }

    remapTemplateBindings(bindings: TemplateBindingScope): TypeSignature {
        const rtscope = this.tscope.map((t) => {
            return { tname: t.tname, terms: t.terms.map((tt) => tt.remapTemplateBindings(bindings)) };
        });

        const rresolvedTerms = this.resolvedTerms.map((tt) => {
            return { name: tt.name, type: tt.type.remapTemplateBindings(bindings) };
        });

        return new NominalTypeSignature(this.sinfo, this.ns, rtscope, rresolvedTerms, this.resolvedTypedef , this.resolvedDeclaration);
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

    remapTemplateBindings(bindings: TemplateBindingScope): TypeSignature {
        return new TupleTypeSignature(this.sinfo, this.entries.map((tt) => tt.remapTemplateBindings(bindings)));
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

    remapTemplateBindings(bindings: TemplateBindingScope): TypeSignature {
        return new RecordTypeSignature(this.sinfo, this.entries.map((tt) => [tt[0], tt[1].remapTemplateBindings(bindings)]));
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

    remapTemplateBindings(bindings: TemplateBindingScope): TypeSignature {
        return new EListTypeSignature(this.sinfo, this.entries.map((tt) => tt.remapTemplateBindings(bindings)));
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

    remapTemplateBindings(bindings: TemplateBindingScope): TypeSignature {
        return new StringTemplateType(this.sinfo, this.kind, this.argtypes.map((tt) => tt.remapTemplateBindings(bindings)));
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

    remapTemplateBindings(bindings: TemplateBindingScope): TypeSignature {
        const rbparams = this.params.map((pp) => new FunctionParameter(pp.name, pp.type.remapTemplateBindings(bindings), pp.isRefParam, pp.isSpreadParam));
        return new LambdaTypeSignature(this.sinfo, this.recursive, this.name, rbparams, this.resultType ? this.resultType.remapTemplateBindings(bindings) : undefined);
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

    remapTemplateBindings(bindings: TemplateBindingScope): TypeSignature {
        return new AndTypeSignature(this.sinfo, this.ltype.remapTemplateBindings(bindings), this.rtype.remapTemplateBindings(bindings));
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

    remapTemplateBindings(bindings: TemplateBindingScope): TypeSignature {
        return new NoneableTypeSignature(this.sinfo, this.type.remapTemplateBindings(bindings));
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

    remapTemplateBindings(bindings: TemplateBindingScope): TypeSignature {
        return new UnionTypeSignature(this.sinfo, this.ltype.remapTemplateBindings(bindings), this.rtype.remapTemplateBindings(bindings));
    }
}

export {
    FullyQualifiedNamespace, TemplateBindingScope,
    TypeSignature, ErrorTypeSignature, VoidTypeSignature, AutoTypeSignature, 
    TemplateTypeSignature, NominalTypeSignature, 
    TupleTypeSignature, RecordTypeSignature, EListTypeSignature, StringTemplateType,
    RecursiveAnnotation, FunctionParameter, LambdaTypeSignature, AndTypeSignature, NoneableTypeSignature, UnionTypeSignature
};
