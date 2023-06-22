import { TIRASCIIStringOfEntityType, TIRAssembly, TIRConceptType, TIREnumEntityType, TIRListEntityType, TIRMapEntityType, TIRMapEntryEntityType, TIROOType, TIRObjectEntityType, TIRPathEntityType, TIRPathFragmentEntityType, TIRPathGlobEntityType, TIRPathValidatorEntityType, TIRPrimitiveInternalEntityType, TIRQueueEntityType, TIRSetEntityType, TIRStackEntityType, TIRStringOfEntityType, TIRTaskType, TIRType, TIRTypeKey, TIRTypedeclEntityType, TIRUnionType, TIRValidatorEntityType } from "../../../frontend/tree_ir/tir_assembly";

function assert(cond: boolean, msg?: string) {
    if(!cond) {
        throw new Error((msg || "error")  + " -- type_emitter.ts");
    }
} 

function typeEncodedAsUnion(asm: TIRAssembly, tt: TIRTypeKey): boolean {
    assert(asm.typeMap.has(tt), `missing type name entry ${tt}`);

    const ttype = asm.typeMap.get(tt) as TIRType;
    return (ttype instanceof TIRConceptType) || (ttype instanceof TIRUnionType);
}

function resolveTypeMemberAccess(asm: TIRAssembly, tt: TIRTypeKey): string {
    assert(asm.typeMap.has(tt), `missing type name entry ${tt}`);

    const ttype = asm.typeMap.get(tt) as TIROOType;
    const nsl = ttype.tname.ns === "Core" ? "$BSQ" : `$ASM.${ttype.tname.ns.replace(/::/g, "$")}`;

    if (ttype instanceof TIRObjectEntityType) {
        if (ttype.binds.size === 0) {
            return `${nsl}.${ttype.tname.name}`;
        }
        else {
            return `${nsl}["${ttype.tkey}"]`;
        }
    }
    else if((ttype instanceof TIREnumEntityType) || (ttype instanceof TIRTypedeclEntityType)) {
        return `${nsl}.${ttype.tname.name}`;
    }
    else if(ttype instanceof TIRPrimitiveInternalEntityType) {
        return `${nsl}.${ttype.tname.name}`;
    }
    else if ((ttype instanceof TIRValidatorEntityType) || (ttype instanceof TIRPathValidatorEntityType)) {
        return `${nsl}.${ttype.tname.name}`;
    }
    else if ((ttype instanceof TIRStringOfEntityType) || (ttype instanceof TIRASCIIStringOfEntityType)) {
        return `${nsl}["${ttype.tkey}"]`;
    }
    else if ((ttype instanceof TIRPathEntityType) || (ttype instanceof TIRPathFragmentEntityType) || (ttype instanceof TIRPathGlobEntityType)) {
        return `${nsl}["${ttype.tkey}"]`;
    }
    else if(ttype instanceof TIRMapEntryEntityType) {
        return `${nsl}["${ttype.tkey}"]`;
    }
    else if((ttype instanceof TIRListEntityType) || (ttype instanceof TIRStackEntityType) || (ttype instanceof TIRQueueEntityType) ||  (ttype instanceof TIRSetEntityType) || (ttype instanceof TIRMapEntityType)) {
        return `${nsl}["${ttype.tkey}"]`;
    }
    else if(ttype instanceof TIRTaskType) {
        return `${nsl}.${ttype.tname.name}`;
    }
    else if(ttype instanceof TIRConceptType) {
        if (ttype.binds.size === 0) {
            return `${nsl}.${ttype.tname.name}`;
        }
        else {
            return `${nsl}["${ttype.tkey}"]`;
        }
    }
    else {
        assert(false, "Unknown type in resolveTypeNameAccess");
        return "[UNKNOWN TYPE]";
    }
}

export {
    typeEncodedAsUnion,
    resolveTypeMemberAccess
}