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

class TemplateConstraintScope {
    constraints: Map<string, TypeSignature>[] = [];

    constructor() {
    }

    pushConstraintScope(constraints: [string, TypeSignature][]) {
        let nconstraints = new Map<string, TypeSignature>(constraints);
        this.constraints.push(nconstraints);
    }

    popConstraintScope() {
        this.constraints.pop();
    }

    resolveConstraint(name: string): TypeSignature {
        for(let i = this.constraints.length - 1; i >= 0; ++i) {
            const res = this.constraints[i].get(name);
            if(res !== undefined) {
                return res;
            }
        }
        assert(false, `Constraint ${name} not found in scope`);
    }
}

class TemplateNameMapper {
    readonly mapper: Map<string, TypeSignature>[];

    constructor(mapper: Map<string, TypeSignature>[]) {
        this.mapper = mapper;
    }

    static createEmpty(): TemplateNameMapper {
        return new TemplateNameMapper([]);
    }

    static merge(m1: TemplateNameMapper, m2: TemplateNameMapper): TemplateNameMapper {
        return new TemplateNameMapper([...m1.mapper, ...m2.mapper]);
    }

    resolveTemplateMapping(ttype: TemplateTypeSignature): TypeSignature {
        for(let i = this.mapper.length - 1; i >= 0; ++i) {
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

    constructor(sinfo: SourceInfo) {
        this.sinfo = sinfo;
    }

    abstract emit(toplevel: boolean): string;

    abstract remapTemplateBindings(mapper: TemplateNameMapper): TypeSignature;
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

    remapTemplateBindings(mapper: TemplateNameMapper): TypeSignature {
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

    remapTemplateBindings(mapper: TemplateNameMapper): TypeSignature {
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

    remapTemplateBindings(mapper: TemplateNameMapper): TypeSignature {
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

    remapTemplateBindings(mapper: TemplateNameMapper): TypeSignature {
        return mapper.resolveTemplateMapping(this);
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

    remapTemplateBindings(mapper: TemplateNameMapper): TypeSignature {
        const rtscope = this.tscope.map((t) => {
            return { tname: t.tname, terms: t.terms.map((tt) => tt.remapTemplateBindings(mapper)) };
        });

        const rresolvedTerms = this.resolvedTerms.map((tt) => {
            return { name: tt.name, type: tt.type.remapTemplateBindings(mapper) };
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

    remapTemplateBindings(mapper: TemplateNameMapper): TypeSignature {
        return new TupleTypeSignature(this.sinfo, this.entries.map((tt) => tt.remapTemplateBindings(mapper)));
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

    remapTemplateBindings(mapper: TemplateNameMapper): TypeSignature {
        return new RecordTypeSignature(this.sinfo, this.entries.map((tt) => [tt[0], tt[1].remapTemplateBindings(mapper)]));
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

    remapTemplateBindings(mapper: TemplateNameMapper): TypeSignature {
        return new EListTypeSignature(this.sinfo, this.entries.map((tt) => tt.remapTemplateBindings(mapper)));
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

    remapTemplateBindings(mapper: TemplateNameMapper): TypeSignature {
        return new StringTemplateType(this.sinfo, this.kind, this.argtypes.map((tt) => tt.remapTemplateBindings(mapper)));
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

    remapTemplateBindings(mapper: TemplateNameMapper): TypeSignature {
        const rbparams = this.params.map((pp) => new FunctionParameter(pp.name, pp.type.remapTemplateBindings(mapper), pp.isRefParam, pp.isSpreadParam));
        return new LambdaTypeSignature(this.sinfo, this.recursive, this.name, rbparams, this.resultType ? this.resultType.remapTemplateBindings(mapper) : undefined);
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

    remapTemplateBindings(mapper: TemplateNameMapper): TypeSignature {
        return new AndTypeSignature(this.sinfo, this.ltype.remapTemplateBindings(mapper), this.rtype.remapTemplateBindings(mapper));
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

    remapTemplateBindings(mapper: TemplateNameMapper): TypeSignature {
        return new NoneableTypeSignature(this.sinfo, this.type.remapTemplateBindings(mapper));
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

    remapTemplateBindings(mapper: TemplateNameMapper): TypeSignature {
        return new UnionTypeSignature(this.sinfo, this.ltype.remapTemplateBindings(mapper), this.rtype.remapTemplateBindings(mapper));
    }
}

export {
    FullyQualifiedNamespace, TemplateConstraintScope, TemplateNameMapper,
    TypeSignature, ErrorTypeSignature, VoidTypeSignature, AutoTypeSignature, 
    TemplateTypeSignature, NominalTypeSignature, 
    TupleTypeSignature, RecordTypeSignature, EListTypeSignature, StringTemplateType,
    RecursiveAnnotation, FunctionParameter, LambdaTypeSignature, AndTypeSignature, NoneableTypeSignature, UnionTypeSignature
};
