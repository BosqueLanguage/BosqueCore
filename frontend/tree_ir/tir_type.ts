//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as assert from "assert";

import { ConceptTypeDecl, EntityTypeDecl, TaskTypeDecl } from "../ast/assembly";
import { TIRLiteralValue } from "./tir_body";

abstract class ResolvedAtomType {
    readonly typeID: string;

    constructor(typeID: string) {
        this.typeID = typeID;
    }
}

class ResolvedLiteralAtomType extends ResolvedAtomType {
    readonly lexp: TIRLiteralValue;

    constructor(reprexp: string, lexp: TIRLiteralValue) {
        super(reprexp);
        this.lexp = lexp;
    }
}

abstract class ResolvedEntityAtomType extends ResolvedAtomType {
    readonly object: EntityTypeDecl;

    constructor(typeID: string, object: EntityTypeDecl) {
        super(typeID);
        this.object = object;
    }

    getBinds(): Map<string, ResolvedType> {
        return new Map<string, ResolvedType>();
    }
}

//Represents types declared as entities in the code
class ResolvedObjectEntityAtomType extends ResolvedEntityAtomType {
    readonly binds: Map<string, ResolvedType>;

    constructor(typeID: string, object: EntityTypeDecl, binds: Map<string, ResolvedType>) {
        super(typeID, object);
        this.binds = binds;
    }

    static create(object: EntityTypeDecl, binds: Map<string, ResolvedType>): ResolvedEntityAtomType {
        let name = (object.ns !== "Core" ? (object.ns + "::") : "") + object.name;
        if (object.terms.length !== 0) {
            name += "<" + object.terms.map((arg) => (binds.get(arg.name) as ResolvedType).typeID).join(", ") + ">";
        }

        return new ResolvedObjectEntityAtomType(name, object, binds);
    }

    getBinds(): Map<string, ResolvedType> {
        return this.binds;
    }
}

//Represents enum types declared as entities in the code
class ResolvedEnumEntityAtomType extends ResolvedEntityAtomType {
    constructor(typeID: string, object: EntityTypeDecl) {
        super(typeID, object);
    }

    static create(object: EntityTypeDecl): ResolvedEntityAtomType {
        let name = (object.ns !== "Core" ? (object.ns + "::") : "") + object.name;
        return new ResolvedEnumEntityAtomType(name, object);
    }
}

//Represents typedecl T = X ... types where the representation is a single primitve typed value
class ResolvedTypedeclEntityAtomType extends ResolvedEntityAtomType {
    readonly valuetype: ResolvedEntityAtomType; //result of .value()
    readonly representation: ResolvedPrimitiveInternalEntityAtomType; //result of getUnderlyingRepresentation opcode 

    constructor(typeID: string, object: EntityTypeDecl, valuetype: ResolvedEntityAtomType, representation: ResolvedPrimitiveInternalEntityAtomType) {
        super(typeID, object);
        this.valuetype = valuetype;
        this.representation = representation;
    }

    static create(object: EntityTypeDecl, valuetype: ResolvedEntityAtomType, representation: ResolvedPrimitiveInternalEntityAtomType): ResolvedEntityAtomType {
        let name = (object.ns !== "Core" ? (object.ns + "::") : "") + object.name;
        return new ResolvedTypedeclEntityAtomType(name, object, valuetype, representation);
    }
}

//base class for all the primitive types that are defined
abstract class ResolvedInternalEntityAtomType extends ResolvedEntityAtomType {
    constructor(typeID: string, object: EntityTypeDecl) {
        super(typeID, object);
    }
} 

//class representing all the primitive values (Int, Bool, String, ...). ALl of these are special implemented values
class ResolvedPrimitiveInternalEntityAtomType extends ResolvedInternalEntityAtomType {
    constructor(typeID: string, object: EntityTypeDecl) {
        super(typeID, object);
    }

    static create(object: EntityTypeDecl): ResolvedPrimitiveInternalEntityAtomType {
        let name = (object.ns !== "Core" ? (object.ns + "::") : "") + object.name;
        return new ResolvedPrimitiveInternalEntityAtomType(name, object);
    }
} 

//class representing Validator regex types
class ResolvedValidatorEntityAtomType extends ResolvedInternalEntityAtomType {
    constructor(typeID: string, object: EntityTypeDecl) {
        super(typeID, object);
    }

    static create(object: EntityTypeDecl): ResolvedValidatorEntityAtomType {
        let name = (object.ns !== "Core" ? (object.ns + "::") : "") + object.name;
        return new ResolvedValidatorEntityAtomType(name, object);
    }
}

//class representing StringOf<T> types
class ResolvedStringOfEntityAtomType extends ResolvedInternalEntityAtomType {
    readonly validatortype: ResolvedValidatorEntityAtomType;

    constructor(typeID: string, object: EntityTypeDecl, validatortype: ResolvedValidatorEntityAtomType) {
        super(typeID, object);
        this.validatortype = validatortype;
    }

    static create(object: EntityTypeDecl, validatortype: ResolvedValidatorEntityAtomType): ResolvedStringOfEntityAtomType {
        let name = (object.ns !== "Core" ? (object.ns + "::") : "") + object.name;
        return new ResolvedStringOfEntityAtomType(name, object, validatortype);
    }

    getBinds(): Map<string, ResolvedType> {
        return new Map<string, ResolvedType>().set("T", ResolvedType.createSingle(this.validatortype));
    }
}

//class representing ASCIIStringOf<T> types
class ResolvedASCIIStringOfEntityAtomType extends ResolvedInternalEntityAtomType {
    readonly validatortype: ResolvedValidatorEntityAtomType;

    constructor(typeID: string, object: EntityTypeDecl, validatortype: ResolvedValidatorEntityAtomType) {
        super(typeID, object);
        this.validatortype = validatortype;
    }

    static create(object: EntityTypeDecl, validatortype: ResolvedValidatorEntityAtomType): ResolvedASCIIStringOfEntityAtomType {
        let name = (object.ns !== "Core" ? (object.ns + "::") : "") + object.name;
        return new ResolvedASCIIStringOfEntityAtomType(name, object, validatortype);
    }

    getBinds(): Map<string, ResolvedType> {
        return new Map<string, ResolvedType>().set("T", ResolvedType.createSingle(this.validatortype));
    }
}

//class representing PathValidator types
class ResolvedPathValidatorEntityAtomType extends ResolvedInternalEntityAtomType {
    constructor(typeID: string, object: EntityTypeDecl) {
        super(typeID, object);
    }

    static create(object: EntityTypeDecl): ResolvedPathValidatorEntityAtomType {
        let name = (object.ns !== "Core" ? (object.ns + "::") : "") + object.name;
        return new ResolvedPathValidatorEntityAtomType(name, object);
    }
}

//class representing a Path<T> type
class ResolvedPathEntityAtomType extends ResolvedInternalEntityAtomType {
    readonly validatortype: ResolvedPathValidatorEntityAtomType;

    constructor(typeID: string, object: EntityTypeDecl, validatortype: ResolvedPathValidatorEntityAtomType) {
        super(typeID, object);
        this.validatortype = validatortype;
    }

    static create(object: EntityTypeDecl, validatortype: ResolvedPathValidatorEntityAtomType): ResolvedPathEntityAtomType {
        let name = (object.ns !== "Core" ? (object.ns + "::") : "") + object.name;
        return new ResolvedPathEntityAtomType(name, object, validatortype);
    }

    getBinds(): Map<string, ResolvedType> {
        return new Map<string, ResolvedType>().set("T", ResolvedType.createSingle(this.validatortype));
    }
}

//class representing a PathFragment<T> type
class ResolvedPathFragmentEntityAtomType extends ResolvedInternalEntityAtomType {
    readonly validatortype: ResolvedValidatorEntityAtomType;

    constructor(typeID: string, object: EntityTypeDecl, validatortype: ResolvedPathValidatorEntityAtomType) {
        super(typeID, object);
        this.validatortype = validatortype;
    }

    static create(object: EntityTypeDecl, validatortype: ResolvedPathValidatorEntityAtomType): ResolvedPathFragmentEntityAtomType {
        let name = (object.ns !== "Core" ? (object.ns + "::") : "") + object.name;
        return new ResolvedPathFragmentEntityAtomType(name, object, validatortype);
    }

    getBinds(): Map<string, ResolvedType> {
        return new Map<string, ResolvedType>().set("T", ResolvedType.createSingle(this.validatortype));
    }
}

class ResolvedPathGlobEntityAtomType extends ResolvedInternalEntityAtomType {
    readonly validatortype: ResolvedPathValidatorEntityAtomType;

    constructor(typeID: string, object: EntityTypeDecl, validatortype: ResolvedPathValidatorEntityAtomType) {
        super(typeID, object);
        this.validatortype = validatortype;
    }

    static create(object: EntityTypeDecl, validatortype: ResolvedValidatorEntityAtomType): ResolvedPathGlobEntityAtomType {
        let name = (object.ns !== "Core" ? (object.ns + "::") : "") + object.name;
        return new ResolvedPathGlobEntityAtomType(name, object, validatortype);
    }

    getBinds(): Map<string, ResolvedType> {
        return new Map<string, ResolvedType>().set("T", ResolvedType.createSingle(this.validatortype));
    }
}

//class representing Ok, Err, Something types
class ResolvedConstructableEntityAtomType extends ResolvedInternalEntityAtomType {
    readonly binds: Map<string, ResolvedType>;

    constructor(typeID: string, object: EntityTypeDecl, binds: Map<string, ResolvedType>) {
        super(typeID, object);
        this.binds = binds;
    }

    static create(object: EntityTypeDecl, binds: Map<string, ResolvedType>): ResolvedConstructableEntityAtomType {
        let name = (object.ns !== "Core" ? (object.ns + "::") : "") + object.name + "<" + object.terms.map((arg) => (binds.get(arg.name) as ResolvedType).typeID).join(", ") + ">";
        return new ResolvedConstructableEntityAtomType(name, object, binds);
    }

    getBinds(): Map<string, ResolvedType> {
        return this.binds
    }
}

//class representing special havoc type
class ResolvedHavocEntityAtomType extends ResolvedInternalEntityAtomType {
    constructor(typeID: string, object: EntityTypeDecl) {
        super(typeID, object);
    }

    static create(object: EntityTypeDecl): ResolvedHavocEntityAtomType {
        let name = (object.ns !== "Core" ? (object.ns + "::") : "") + object.name;
        return new ResolvedHavocEntityAtomType(name, object);
    }
}

//abstract class for all the builtin collection types
abstract class ResolvedPrimitiveCollectionEntityAtomType extends ResolvedInternalEntityAtomType {
    constructor(typeID: string, object: EntityTypeDecl) {
        super(typeID, object);
    }
}

//class representing List<T>
class ResolvedListEntityAtomType extends ResolvedPrimitiveCollectionEntityAtomType {
    readonly typeT: ResolvedType;

    constructor(typeID: string, object: EntityTypeDecl, typeT: ResolvedType) {
        super(typeID, object);
        this.typeT = typeT;
    }

    static create(object: EntityTypeDecl, typeT: ResolvedType): ResolvedListEntityAtomType {
        let name = "List<" + typeT.typeID + ">";
        return new ResolvedListEntityAtomType(name, object, typeT);
    }

    getBinds(): Map<string, ResolvedType> {
        return new Map<string, ResolvedType>().set("T", this.typeT);
    }
}

//class representing Stack<T>
class ResolvedStackEntityAtomType extends ResolvedPrimitiveCollectionEntityAtomType {
    readonly typeT: ResolvedType;

    constructor(typeID: string, object: EntityTypeDecl, typeT: ResolvedType) {
        super(typeID, object);
        this.typeT = typeT;
    }

    static create(object: EntityTypeDecl, typeT: ResolvedType): ResolvedStackEntityAtomType {
        let name = "Stack<" + typeT.typeID + ">";
        return new ResolvedStackEntityAtomType(name, object, typeT);
    }

    getBinds(): Map<string, ResolvedType> {
        return new Map<string, ResolvedType>().set("T", this.typeT);
    }
}

//class representing Queue<T>
class ResolvedQueueEntityAtomType extends ResolvedPrimitiveCollectionEntityAtomType {
    readonly typeT: ResolvedType;

    constructor(typeID: string, object: EntityTypeDecl, typeT: ResolvedType) {
        super(typeID, object);
        this.typeT = typeT;
    }

    static create(object: EntityTypeDecl, typeT: ResolvedType): ResolvedQueueEntityAtomType {
        let name = "Queue<" + typeT.typeID + ">";
        return new ResolvedQueueEntityAtomType(name, object, typeT);
    }

    getBinds(): Map<string, ResolvedType> {
        return new Map<string, ResolvedType>().set("T", this.typeT);
    }
}

//class representing Set<T>
class ResolvedSetEntityAtomType extends ResolvedPrimitiveCollectionEntityAtomType {
    readonly typeT: ResolvedType;

    constructor(typeID: string, object: EntityTypeDecl, typeT: ResolvedType) {
        super(typeID, object);
        this.typeT = typeT;
    }

    static create(object: EntityTypeDecl, typeT: ResolvedType): ResolvedSetEntityAtomType {
        let name = "Set<" + typeT.typeID + ">";
        return new ResolvedSetEntityAtomType(name, object, typeT);
    }

    getBinds(): Map<string, ResolvedType> {
        return new Map<string, ResolvedType>().set("T", this.typeT);
    }
}

//class representing Map<K, V>
class ResolvedMapEntityAtomType extends ResolvedPrimitiveCollectionEntityAtomType {
    readonly typeK: ResolvedType;
    readonly typeV: ResolvedType;

    constructor(typeID: string, object: EntityTypeDecl, typeK: ResolvedType, typeV: ResolvedType) {
        super(typeID, object);
        this.typeK = typeK;
        this.typeV = typeV;
    }

    static create(object: EntityTypeDecl, typeK: ResolvedType, typeV: ResolvedType): ResolvedMapEntityAtomType {
        let name = "Map<" + typeK.typeID + "," + typeV.typeID + ">";
        return new ResolvedMapEntityAtomType(name, object, typeK, typeV);
    }

    getBinds(): Map<string, ResolvedType> {
        return new Map<string, ResolvedType>().set("K", this.typeK).set("V", this.typeV);
    }
}

class ResolvedTaskAtomType extends ResolvedAtomType {
    readonly task: TaskTypeDecl;
    readonly binds: Map<string, ResolvedType>;

    constructor(typeID: string, task: TaskTypeDecl, binds: Map<string, ResolvedType>) {
        super(typeID);
        this.task = task;
        this.binds = binds;
    }

    static create(object: TaskTypeDecl, binds: Map<string, ResolvedType>): ResolvedTaskAtomType {
        let name = (object.ns !== "Core" ? (object.ns + "::") : "") + object.name;
        if (object.terms.length !== 0) {
            name += "<" + object.terms.map((arg) => (binds.get(arg.name) as ResolvedType).typeID).join(", ") + ">";
        }

        return new ResolvedTaskAtomType(name, object, binds);
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
}

class ResolvedType {
    readonly typeID: string;
    readonly options: ResolvedAtomType[];

    constructor(typeID: string, options: ResolvedAtomType[]) {
        this.typeID = typeID;
        this.options = options;
    }

    static isGroundedType(options: ResolvedAtomType[]): boolean {
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

    static isUniqueType(tt: ResolvedAtomType): boolean {
        return !(tt instanceof ResolvedConceptAtomType);
    }

    static isNumericType(options: ResolvedAtomType[]): boolean {
        if(options.length !== 1 || !(options[0] instanceof ResolvedEntityAtomType)) {
            return false;
        }
        const atom = options[0] as ResolvedEntityAtomType;

        if(atom instanceof ResolvedPrimitiveInternalEntityAtomType) {
            return atom.object.attributes.includes("__numeric");
        }
        
        if(atom instanceof ResolvedTypedeclEntityAtomType) {
            return atom.representation.object.attributes.includes("__numeric");
        }
        
        return false;
    }

    static createInvalid(): ResolvedType {
        return new ResolvedType("[INVALID]", []);
    }

    static createSingle(type: ResolvedAtomType): ResolvedType {
        return new ResolvedType(type.typeID, [type]);
    }

    static create(types: ResolvedAtomType[]): ResolvedType {
        assert(types.length !== 0, "Invalid Type??")
         
        if (types.length === 1) {
            return ResolvedType.createSingle(types[0]);
        }
        else {
            const atoms = types.sort((a, b) => a.typeID.localeCompare(b.typeID));
            const name = atoms.map((arg) => arg.typeID).join(" | ");

            return new ResolvedType(name, atoms);
        }
    }

    tryGetUniqueLiteralTypeInfo(): ResolvedLiteralAtomType | undefined {
        if (this.options.length !== 1) {
            return undefined;
        }

        if (this.options[0] instanceof ResolvedLiteralAtomType) {
            return (this.options[0] as ResolvedLiteralAtomType);
        }
        else {
            return undefined;
        }
    }

    tryGetUniqueOOTypeInfo(): ResolvedEntityAtomType | ResolvedConceptAtomType | undefined {
        if (this.options.length !== 1) {
            return undefined;
        }

        if (this.options[0] instanceof ResolvedEntityAtomType) {
            return (this.options[0] as ResolvedEntityAtomType);
        }
        else if (this.options[0] instanceof ResolvedConceptAtomType) {
            return this.options[0] as ResolvedConceptAtomType;
        }
        else {
            return undefined;
        }
    }

    tryGetUniqueEntityBindsInfo(): Map<string, ResolvedType> | undefined{
        if (this.options.length !== 1) {
            return undefined;
        }

        if (this.options[0] instanceof ResolvedEntityAtomType) {
            return this.options[0].getBinds();
        }
        else {
            return undefined;
        }
    }

    tryGetUniqueEntityTypeInfo(): ResolvedEntityAtomType | undefined {
        if (this.options.length !== 1) {
            return undefined;
        }

        if (this.options[0] instanceof ResolvedEntityAtomType) {
            return (this.options[0] as ResolvedEntityAtomType);
        }
        else {
            return undefined;
        }
    }

    tryGetUniqueTaskTypeInfo(t: ResolvedType): ResolvedTaskAtomType | undefined {
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
        if(this.options.length !== 1 || !(this.options[0] instanceof ResolvedConstructableEntityAtomType)) {
            return false;
        }

        const cct = this.options[0] as ResolvedConstructableEntityAtomType;
        return cct.object.attributes.includes("__something_type");
    }

    isOptionType(): boolean {
        if(this.options.length !== 1 || !(this.options[0] instanceof ResolvedConceptAtomType)) {
            return false;
        }

        const ccpt = this.options[0] as ResolvedConceptAtomType;
        return ccpt.conceptTypes.length === 1 && ccpt.conceptTypes[0].concept.attributes.includes("__option_type");
    }

    isOkType(): boolean {
        if(this.options.length !== 1 || !(this.options[0] instanceof ResolvedConstructableEntityAtomType)) {
            return false;
        }

        const cct = this.options[0] as ResolvedConstructableEntityAtomType;
        return cct.object.attributes.includes("__ok_type");
    }

    isErrType(): boolean {
        if(this.options.length !== 1 || !(this.options[0] instanceof ResolvedConstructableEntityAtomType)) {
            return false;
        }

        const cct = this.options[0] as ResolvedConstructableEntityAtomType;
        return cct.object.attributes.includes("__err_type");
    }

    isResultType(): boolean {
        if(this.options.length !== 1 || !(this.options[0] instanceof ResolvedConceptAtomType)) {
            return false;
        }

        const ccpt = this.options[0] as ResolvedConceptAtomType;
        return ccpt.conceptTypes.length === 1 && ccpt.conceptTypes[0].concept.attributes.includes("__option_type");
    }

    isInvalidType(): boolean {
        return this.options.length === 0;
    }
}

class ResolvedFunctionTypeParam {
    readonly name: string;
    readonly type: ResolvedType;
    readonly litexp: TIRLiteralValue | undefined;

    constructor(name: string, type: ResolvedType, litexp: TIRLiteralValue | undefined) {
        this.name = name;
        this.type = type;
        this.litexp = litexp;
    }
}

class ResolvedFunctionType {
    readonly typeID: string;
    readonly recursive: "yes" | "no" | "cond";
    readonly params: ResolvedFunctionTypeParam[];
    readonly resultType: ResolvedType;
    readonly isPred: boolean;

    constructor(typeID: string, recursive: "yes" | "no" | "cond", params: ResolvedFunctionTypeParam[], resultType: ResolvedType, isPred: boolean) {
        this.typeID = typeID;
        this.recursive = recursive;
        this.params = params;
        this.resultType = resultType;
        this.isPred = isPred;
    }

    static create(recursive: "yes" | "no" | "cond", params: ResolvedFunctionTypeParam[], resultType: ResolvedType, isPred: boolean): ResolvedFunctionType {
        const cvalues = params.map((param) => param.name + param.type.typeID + (param.litexp !== undefined ? ("==" + param.litexp.lidstr) : ""));
        let cvalue = cvalues.join(", ");

        const lstr = isPred ? "pred" : "fn";
        const name = lstr + "(" + cvalue + ") -> " + resultType.typeID;
        return new ResolvedFunctionType(name, recursive, params, resultType, isPred);
    }
}

class TemplateBindScope {
    readonly scopes: Map<string, ResolvedType>[] = [];

    constructor(scopes: Map<string, ResolvedType>[]) {
        this.scopes = scopes;
    }

    tryTemplateResolveType(tt: string): ResolvedType | undefined {
        const midx = this.scopes.findIndex((sc) => sc.has(tt));
        if(midx === -1) {
            return undefined;
        }

        return this.scopes[midx].get(tt);
    }

    templateResolveType(tt: string): ResolvedType {
        const bb = this.tryTemplateResolveType(tt);
        assert(bb !== undefined, "Template name expected to have binding -- would \"tryTemplateResolveType\" be the right choice?");

        return bb as ResolvedType;
    }

    pushScope(nscope: Map<string, ResolvedType>): TemplateBindScope {
        return new TemplateBindScope([new Map<string, ResolvedType>(nscope), ...this.scopes]);
    }

    static createEmptyBindScope(): TemplateBindScope {
        return new TemplateBindScope([]);
    }

    static createBaseBindScope(binds: Map<string, ResolvedType>): TemplateBindScope {
        return TemplateBindScope.createEmptyBindScope().pushScope(binds);
    }
}

export {
    ResolvedAtomType,
    ResolvedLiteralAtomType,
    ResolvedEntityAtomType, ResolvedObjectEntityAtomType, ResolvedEnumEntityAtomType, ResolvedTypedeclEntityAtomType, ResolvedInternalEntityAtomType, 
    ResolvedPrimitiveInternalEntityAtomType,
    ResolvedValidatorEntityAtomType, ResolvedStringOfEntityAtomType, ResolvedASCIIStringOfEntityAtomType,
    ResolvedPathValidatorEntityAtomType, ResolvedPathEntityAtomType, ResolvedPathFragmentEntityAtomType, ResolvedPathGlobEntityAtomType,
    ResolvedConstructableEntityAtomType, ResolvedHavocEntityAtomType,
    ResolvedPrimitiveCollectionEntityAtomType, ResolvedListEntityAtomType, ResolvedStackEntityAtomType, ResolvedQueueEntityAtomType, ResolvedSetEntityAtomType, ResolvedMapEntityAtomType,
    ResolvedConceptAtomTypeEntry, ResolvedConceptAtomType, ResolvedTaskAtomType,
    ResolvedTupleAtomType, ResolvedRecordAtomType, 
    ResolvedEphemeralListType,
    ResolvedType, 
    ResolvedFunctionTypeParam, ResolvedFunctionType,
    TemplateBindScope
};
