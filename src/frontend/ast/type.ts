//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { LiteralExpressionValue } from "./body";

import { SourceInfo } from "../build_decls";

class TypeSignature {
    readonly sinfo: SourceInfo;

    constructor(sinfo: SourceInfo) {
        this.sinfo = sinfo;
    }

    getDiagnosticName(): string {
        return "[Missing Implementation]";
    }
}

class ParseErrorTypeSignature extends TypeSignature {
    constructor(sinfo: SourceInfo) {
        super(sinfo);
    }

    getDiagnosticName(): string {
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
    readonly ddlit: LiteralExpressionValue | undefined;

    constructor(name: string, type: TypeSignature, ddlit: LiteralExpressionValue | undefined) {
        this.name = name;
        this.type = type;
        this.ddlit = ddlit;
    }
}

class FunctionTypeSignature extends TypeSignature {
    readonly recursive: RecursiveAnnotation;
    readonly isThisRef: boolean;
    readonly params: FunctionParameter[];
    readonly resultType: TypeSignature;
    readonly isPred: boolean;

    constructor(sinfo: SourceInfo, isThisRef: boolean, recursive: RecursiveAnnotation, params: FunctionParameter[], resultType: TypeSignature, isPred: boolean) {
        super(sinfo);
        this.recursive = recursive;
        this.isThisRef = isThisRef;
        this.params = params;
        this.resultType = resultType;
        this.isPred = isPred;
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
