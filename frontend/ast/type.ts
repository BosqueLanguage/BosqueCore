//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { LiteralExpressionValue } from "./body";

class TypeSignature {
    getDiagnosticName(): string {
        return "[Missing Implementation]";
    }
}

class ParseErrorTypeSignature extends TypeSignature {
    getDiagnosticName(): string {
        return "[Parse Error]";
    }
}

class AutoTypeSignature extends TypeSignature {
    getDiagnosticName(): string {
        return "[Auto Type]";
    }
}

class TemplateTypeSignature extends TypeSignature {
    readonly name: string;

    constructor(name: string) {
        super();
        this.name = name;
    }

    getDiagnosticName(): string {
        return this.name;
    }
}

class LiteralTypeSignature extends TypeSignature {
    readonly lvalue: LiteralExpressionValue;

    constructor(lvalue: LiteralExpressionValue) {
        super();
        this.lvalue = lvalue;
    }

    getDiagnosticName(): string {
        return "[Literal Type]";
    }
}

class NominalTypeSignature extends TypeSignature {
    readonly nameSpace: string;
    readonly tnames: string[];
    readonly terms: TypeSignature[];

    constructor(ns: string, tnames: string[], terms?: TypeSignature[]) {
        super();
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

    constructor(entries: TypeSignature[]) {
        super();
        this.entries = entries;
    }

    getDiagnosticName(): string {
        return "[" + this.entries.map((tt) => tt.getDiagnosticName()).join(", ") + "]";
    }
}

class RecordTypeSignature extends TypeSignature {;
    readonly entries: [string, TypeSignature][];

    constructor(entries: [string, TypeSignature][]) {
        super();
        this.entries = entries;
    }

    getDiagnosticName(): string {
        return "{" + this.entries.map((tt) => (tt[0] + ": " + tt[1].getDiagnosticName())).join(", ") + "}";
    }
}

class EphemeralListTypeSignature extends TypeSignature {
    readonly entries: TypeSignature[];

    constructor(entries: TypeSignature[]) {
        super();
        this.entries = entries;
    }

    getDiagnosticName(): string {
        return "(|" + this.entries.map((tt) => tt.getDiagnosticName()).join(", ") + "|)";
    }
}

class FunctionTypeSignature extends TypeSignature {
    readonly recursive: "yes" | "no" | "cond";
    readonly isThisRef: boolean;
    readonly params: TypeSignature[];
    readonly resultType: TypeSignature;
    readonly isPred: boolean;

    constructor(isThisRef: boolean, recursive: "yes" | "no" | "cond", params: TypeSignature[], resultType: TypeSignature, isPred: boolean) {
        super();
        this.recursive = recursive;
        this.isThisRef = isThisRef;
        this.params = params;
        this.resultType = resultType;
        this.isPred = isPred;
    }

    getDiagnosticName(): string {
        return (this.isPred ? "pred" : "fn") + (this.isThisRef ? "ref(" : " (") + this.params.map((ptype) => ptype.getDiagnosticName()).join(", ") + ") -> " + this.resultType.getDiagnosticName();
    }
}

class ProjectTypeSignature extends TypeSignature {
    readonly fromtype: TypeSignature;
    readonly oftype: TypeSignature;

    constructor(fromtype: TypeSignature, oftype: TypeSignature) {
        super();
        this.fromtype = fromtype;
        this.oftype = oftype;
    }

    getDiagnosticName(): string {
        return this.fromtype + "!" + this.oftype;
    }
}

class AndTypeSignature extends TypeSignature {
    readonly types: TypeSignature[];

    constructor(types: TypeSignature[]) {
        super();
        this.types = types;
    }

    getDiagnosticName(): string {
        return this.types.map((tt) => tt.getDiagnosticName()).join("&");
    }
}

class UnionTypeSignature extends TypeSignature {
    readonly types: TypeSignature[];

    constructor(types: TypeSignature[]) {
        super();
        this.types = types;
    }

    getDiagnosticName(): string {
        return this.types.map((tt) => tt.getDiagnosticName()).join("|");
    }
}

export { 
    TypeSignature, ParseErrorTypeSignature, AutoTypeSignature, 
    TemplateTypeSignature, LiteralTypeSignature, NominalTypeSignature, 
    TupleTypeSignature, RecordTypeSignature, EphemeralListTypeSignature,
    FunctionTypeSignature, ProjectTypeSignature, AndTypeSignature, UnionTypeSignature
};
