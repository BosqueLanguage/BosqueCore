//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";

import { ConceptTypeDecl, EntityTypeDecl, TaskTypeDecl } from "../ast/assembly";
import { LiteralTypeSignature } from "../ast/type";

abstract class ResolvedAtomType {
    readonly typeID: string;

    constructor(typeID: string) {
        this.typeID = typeID;
    }
}

class ResolvedLiteralAtomType extends ResolvedAtomType {
    readonly ltype: LiteralTypeSignature;
    readonly lexp: TIRLiteralValue;
    readonly ofype: ResolvedAtomType;

    constructor(lvalue: string, ltype: LiteralTypeSignature, lexp: TIRLiteralValue, ofype: ResolvedAtomType) {
        super(lvalue);
        this.ltype = ltype;
        this.lexp = lexp;
        this.ofype = ofype;
    }
}

class ResolvedEntityAtomType extends ResolvedAtomType {
    readonly object: EntityTypeDecl;
    readonly binds: Map<string, ResolvedType>;

    constructor(typeID: string, object: EntityTypeDecl, binds: Map<string, ResolvedType>) {
        super(typeID);
        this.object = object;
        this.binds = binds;
    }

    static create(object: EntityTypeDecl, binds: Map<string, ResolvedType>): ResolvedEntityAtomType {
        let name = (object.ns !== "Core" ? (object.ns + "::") : "") + object.name;
        if (object.terms.length !== 0) {
            name += "<" + object.terms.map((arg) => (binds.get(arg.name) as ResolvedType).typeID).join(", ") + ">";
        }

        return new ResolvedEntityAtomType(name, object, binds);
    }
}



xxxx;

class ResolvedTaskAtomType extends ResolvedAtomType {
    readonly task: TaskTypeDecl;
    readonly binds: Map<string, ResolvedType>;

    constructor(typeID: string, task: TaskTypeDecl, binds: Map<string, ResolvedType>) {
        super(typeID);
        this.task = task;
        this.binds = binds;
    }

    static create(object: EntityTypeDecl, binds: Map<string, ResolvedType>): ResolvedEntityAtomType {
        let name = (object.ns !== "Core" ? (object.ns + "::") : "") + object.name;
        if (object.terms.length !== 0) {
            name += "<" + object.terms.map((arg) => (binds.get(arg.name) as ResolvedType).typeID).join(", ") + ">";
        }

        return new ResolvedEntityAtomType(name, object, binds);
    }

    hasTemplateType(): boolean {
        return false;
    }
}

class ResolvedConceptAtomTypeEntry {
    readonly typeID: string;
    readonly concept: ConceptTypeDecl;
    readonly binds: Map<string, ResolvedType>;

    constructor(typeID: string, concept: ConceptTypeDecl, binds: Map<string, ResolvedType>) {
        this.typeID = typeID;
        this.concept = concept;
        this.binds = binds;
    }

    static create(concept: ConceptTypeDecl, binds: Map<string, ResolvedType>): ResolvedConceptAtomTypeEntry {
        let name = (concept.ns !== "Core" ? (concept.ns + "::") : "") + concept.name;
        if (concept.terms.length !== 0) {
            name += "<" + concept.terms.map((arg) => (binds.get(arg.name) as ResolvedType).typeID).join(", ") + ">";
        }

        return new ResolvedConceptAtomTypeEntry(name, concept, binds);
    }
}

class ResolvedConceptAtomType extends ResolvedAtomType {
    readonly conceptTypes: ResolvedConceptAtomTypeEntry[];

    constructor(typeID: string, concepts: ResolvedConceptAtomTypeEntry[]) {
        super(typeID);
        this.conceptTypes = concepts;
    }

    static create(concepts: ResolvedConceptAtomTypeEntry[]): ResolvedConceptAtomType {
        const sortedConcepts = concepts.sort((a, b) => a.typeID.localeCompare(b.typeID));
        const name = sortedConcepts.map((cpt) => cpt.typeID).join("&");

        return new ResolvedConceptAtomType(name, sortedConcepts);
    }

    hasTemplateType(): boolean {
        return false;
    }
}

class ResolvedTupleAtomType extends ResolvedAtomType {
    readonly types: ResolvedType[];

    constructor(typeID: string, types: ResolvedType[]) {
        super(typeID);
        this.types = types;
    }

    static create(types: ResolvedType[]): ResolvedTupleAtomType {
        const name = types.map((entry) => entry.typeID).join(", ");

        return new ResolvedTupleAtomType("[" + name + "]", types);
    }

    hasTemplateType(): boolean {
        return this.types.some((entry) => entry.hasTemplateType());
    }
}

class ResolvedRecordAtomType extends ResolvedAtomType {
    readonly entries: {pname: string, ptype: ResolvedType}[];

    constructor(typeID: string, entries: {pname: string, ptype: ResolvedType}[]) {
        super(typeID);
        this.entries = entries;
    }

    static create(entries: {pname: string, ptype: ResolvedType}[]): ResolvedRecordAtomType {
        let simplifiedEntries = [...entries].sort((a, b) => a.pname.localeCompare(b.pname));
        const name = simplifiedEntries.map((entry) => entry.pname + ": " + entry.ptype.typeID).join(", ");

        return new ResolvedRecordAtomType("{" + name + "}", simplifiedEntries);
    }

    hasTemplateType(): boolean {
        return this.entries.some((entry) => entry.ptype.hasTemplateType());
    }
}

class ResolvedEphemeralListType extends ResolvedAtomType {
    readonly types: ResolvedType[];

    constructor(typeID: string, types: ResolvedType[]) {
        super(typeID);
        this.types = types;
    }

    static create(entries: ResolvedType[]): ResolvedEphemeralListType {
        const name = entries.map((entry) => entry.typeID).join(", ");

        return new ResolvedEphemeralListType("(|" + name + "|)", entries);
    }

    hasTemplateType(): boolean {
        return this.types.some((type) => type.hasTemplateType());
    }
}

enum TypePropertyFlags {
    Grounded,
    Unique,
    Numeric
}

class ResolvedType {
    readonly typeID: string;
    readonly options: ResolvedAtomType[];
    readonly flags: TypePropertyFlags[];

    constructor(typeID: string, options: ResolvedAtomType[], flags: TypePropertyFlags[]) {
        this.typeID = typeID;
        this.options = options;
        this.flags = flags;
    }

    private static isGroundedType(options: ResolvedAtomType[]): boolean {
        return options.every((opt) => {
            if(opt instanceof ResolvedConceptAtomType) {
                return opt.conceptTypes.every((cpt) => !cpt.concept.attributes.includes("__universal"));
            }
            else if (opt instanceof ResolvedTupleAtomType) {
                return opt.types.every((tt) => ResolvedType.isGroundedType(tt.options));
            }
            else if (opt instanceof ResolvedRecordAtomType) {
                return opt.entries.every((entry) => ResolvedType.isGroundedType(entry.ptype.options));
            }
            else {
                return true;
            }
        });
    }

    private static isUniqueType(options: ResolvedAtomType[]): boolean {
        if(options.length !== 1) {
            return false;
        }

        return !(options[0] instanceof ResolvedConceptAtomType);
    }

    private static isNumericType(options: ResolvedAtomType[]): boolean {
        if(options.length !== 1 || !(options[0] instanceof ResolvedEntityAtomType)) {
            return false;
        }

        const atom = options[0] as ResolvedEntityAtomType;
        if(atom.object.attributes.includes)
    }

    static createSingle(type: ResolvedAtomType, flags: TypePropertyFlags[]): ResolvedType {
        if(!flags.includes(TypePropertyFlags.Unique, xxxx)) {
            flags = [...flags, TypePropertyFlags.Unique]
        }

        if(!flags.includes(TypePropertyFlags.Grounded) && ResolvedType.isGroundedType([type])) {
            flags = [...flags, TypePropertyFlags.Grounded];
        }

        return new ResolvedType(type.typeID, [type], flags);
    }

    static create(types: ResolvedAtomType[], flags: TypePropertyFlags[]): ResolvedType {
        assert(types.length !== 0, "Invalid Type??")
         
        if (types.length === 1) {
            return ResolvedType.createSingle(types[0], flags);
        }
        else {
            const atoms = types.sort((a, b) => a.typeID.localeCompare(b.typeID));
            const name = atoms.map((arg) => arg.typeID).join(" | ");

            if(!flags.includes(TypePropertyFlags.Grounded) && ResolvedType.isGroundedType(types)) {
                flags = [...flags, TypePropertyFlags.Grounded];
            }

            return new ResolvedType(name, atoms, flags);
        }
    }

    static tryGetUniqueOOTypeInfo(t: ResolvedType): ResolvedEntityAtomType | ResolvedConceptAtomType | undefined {
        if (t.options.length !== 1) {
            return undefined;
        }

        if (t.options[0] instanceof ResolvedEntityAtomType) {
            return (t.options[0] as ResolvedEntityAtomType);
        }
        else if (t.options[0] instanceof ResolvedConceptAtomType) {
            return t.options[0] as ResolvedConceptAtomType;
        }
        else {
            return undefined;
        }
    }

    static tryGetUniqueTaskTypeInfo(t: ResolvedType): ResolvedTaskAtomType | undefined {
        if (t.options.length !== 1) {
            return undefined;
        }

        if (t.options[0] instanceof ResolvedTaskAtomType) {
            return (t.options[0] as ResolvedTaskAtomType);
        }
        else {
            return undefined;
        }
    }

    getCollectionContentsType(): ResolvedType {
        const oodecl = this.getUniqueCallTargetType().object;
        const oobinds = this.getUniqueCallTargetType().binds;
        
        const etype = oodecl.attributes.includes("__map_type") 
                ? ResolvedType.createSingle(ResolvedTupleAtomType.create([oobinds.get("K") as ResolvedType, oobinds.get("V") as ResolvedType]))
                : oobinds.get("T") as ResolvedType;

        return etype;
    }

    isSameType(otype: ResolvedType): boolean {
        return this.typeID === otype.typeID;
    }

    isNoneType(): boolean {
        return this.typeID === "None";
    }

    isSomeType(): boolean {
        return this.typeID === "Some";
    }

    isAnyType(): boolean {
        return this.typeID === "Any";
    }

    isNothingType(): boolean {
        return this.typeID === "Nothing";
    }

    isSomethingType(): boolean {
        if(!this.isUniqueCallTargetType()) {
            return false;
        }

        const oodecl = this.getUniqueCallTargetType().object;
        return oodecl.attributes.includes("__something_type");
    }

    isOptionType(): boolean {
        if(this.options.length !== 1 || !(this.options[0] instanceof ResolvedConceptAtomType)) {
            return false;
        }

        const ccpt = this.options[0] as ResolvedConceptAtomType;
        return ccpt.conceptTypes.length === 1 && ccpt.conceptTypes[0].concept.attributes.includes("__option_type");
    }

    isOkType(): boolean {
        if(!this.isUniqueCallTargetType()) {
            return false;
        }

        const oodecl = this.getUniqueCallTargetType().object;
        return oodecl.attributes.includes("__ok_type");
    }

    isErrType(): boolean {
        if(!this.isUniqueCallTargetType()) {
            return false;
        }

        const oodecl = this.getUniqueCallTargetType().object;
        return oodecl.attributes.includes("__err_type");
    }

    isResultType(): boolean {
        if(this.options.length !== 1 || !(this.options[0] instanceof ResolvedConceptAtomType)) {
            return false;
        }

        const ccpt = this.options[0] as ResolvedConceptAtomType;
        return ccpt.conceptTypes.length === 1 && ccpt.conceptTypes[0].concept.attributes.includes("__option_type");
    }
}

class ResolvedFunctionTypeParam {
    readonly name: string;
    readonly type: ResolvedType | ResolvedFunctionType;
    readonly refKind: "ref" | "out" | "out?" | undefined;
    readonly isOptional: boolean;
    readonly litexp: string | undefined;

    constructor(name: string, type: ResolvedType | ResolvedFunctionType, isOpt: boolean, refKind: "ref" | "out" | "out?" | undefined, litexp: string | undefined) {
        this.name = name;
        this.type = type;
        this.isOptional = isOpt;
        this.refKind = refKind;
        this.litexp = litexp;
    }
}

class ResolvedFunctionType {
    readonly typeID: string;
    readonly recursive: "yes" | "no" | "cond";
    readonly params: ResolvedFunctionTypeParam[];
    readonly optRestParamName: string | undefined;
    readonly optRestParamType: ResolvedType | undefined;
    readonly resultType: ResolvedType;
    readonly isPred: boolean;

    readonly allParamNames: Set<string>;

    constructor(typeID: string, recursive: "yes" | "no" | "cond", params: ResolvedFunctionTypeParam[], optRestParamName: string | undefined, optRestParamType: ResolvedType | undefined, resultType: ResolvedType, isPred: boolean) {
        this.typeID = typeID;
        this.recursive = recursive;
        this.params = params;
        this.optRestParamName = optRestParamName;
        this.optRestParamType = optRestParamType;
        this.resultType = resultType;
        this.isPred = isPred;

        this.allParamNames = new Set<string>();
    }

    static create(recursive: "yes" | "no" | "cond", params: ResolvedFunctionTypeParam[], optRestParamName: string | undefined, optRestParamType: ResolvedType | undefined, resultType: ResolvedType, isPred: boolean): ResolvedFunctionType {
        const cvalues = params.map((param) => (param.refKind !== undefined ? param.refKind : "") + param.name + (param.isOptional ? "?: " : ": ") + param.type.typeID + (param.litexp !== undefined ? ("==" + param.litexp) : ""));
        let cvalue = cvalues.join(", ");

        if (optRestParamName !== undefined && optRestParamType !== undefined) {
            cvalue += ((cvalues.length !== 0 ? ", " : "") + ("..." + optRestParamName + ": " + optRestParamType.typeID));
        }

        const lstr = isPred ? "pred" : "fn";
        const name = lstr + "(" + cvalue + ") -> " + resultType.typeID;
        return new ResolvedFunctionType(name, recursive, params, optRestParamName, optRestParamType, resultType, isPred);
    }
}

class TemplateBindScope {
    readonly scopes: Map<string, ResolvedType | string>[] = [];

    constructor(scopes: Map<string, ResolvedType | string>[]) {
        this.scopes = scopes;
    }

    private tryTemplateResolveType_RecUp(tt: string, idx: number): ResolvedType | undefined {
        const midx = this.scopes.findIndex((sc) => sc.has(tt), idx);
        if(midx === -1) {
            return undefined;
        }

        const bb = this.scopes[midx].get(tt);
        if(bb === undefined) {
            return undefined;
        }

        if(typeof(bb) !== "string") {
            return bb;
        }
        else {
            return this.tryTemplateResolveType_RecUp(bb, midx + 1);
        }
    }

    tryTemplateResolveType(tt: string): ResolvedType | undefined {
        const midx = this.scopes.findIndex((sc) => sc.has(tt));
        if(midx === -1) {
            return undefined;
        }

        const bb = this.scopes[midx].get(tt);
        if(bb === undefined) {
            return undefined;
        }

        if(typeof(bb) !== "string") {
            return bb;
        }
        else {
            return this.tryTemplateResolveType_RecUp(bb, midx + 1);
        }
    }

    templateResolveType(tt: string): ResolvedType {
        const bb = this.tryTemplateResolveType(tt);
        assert(bb !== undefined, "Template name expected to have binding -- would \"tryTemplateResolveType\" be the right choice?");

        return bb as ResolvedType;
    }

    pushScope(nscope: Map<string, ResolvedType | string>): TemplateBindScope {
        return new TemplateBindScope([new Map<string, ResolvedType | string>(nscope), ...this.scopes]);
    }
}

export {
    ResolvedAtomType,
    ResolvedLiteralAtomType,
    ResolvedConceptAtomTypeEntry, ResolvedConceptAtomType, ResolvedEntityAtomType, ResolvedTaskAtomType,
    ResolvedTupleAtomType, ResolvedRecordAtomType, 
    ResolvedEphemeralListType,
    TypePropertyFlags, ResolvedType, 
    ResolvedFunctionTypeParam, ResolvedFunctionType,
    TemplateBindScope
};
