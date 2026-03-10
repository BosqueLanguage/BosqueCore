
import { IRAbstractCollectionTypeDecl, IRAbstractEntityTypeDecl, IRAbstractNominalTypeDecl, IRAssembly, IRConceptTypeDecl, IRDatatypeTypeDecl, IREntityTypeDecl, IRListTypeDecl, IROptionTypeDecl, IRSomeTypeDecl } from "../irdefs/irassembly.js";
import { IRDashResultTypeSignature, IREListTypeSignature, IRFormatTypeSignature, IRLambdaParameterPackTypeSignature, IRNominalTypeSignature, IRTypeSignature, IRVoidTypeSignature } from "../irdefs/irtype.js";
import { TransformCPPNameManager } from "./namemgr.js";

import assert from "node:assert";

//Duplicated from C++ definitions
const MAX_LIST_INLINE_BYTES = 48; //Bytes -- so 64 total when we add 8 bytes for the size and 8 bytes for the tag

function LIST_T_CAPACITY(elem_size: number): number {
    return Math.max(Math.floor(MAX_LIST_INLINE_BYTES / elem_size), 1);
}

class FieldOffsetInfo {
    readonly fkey: string;

    readonly enclosingtype: IRTypeSignature;
    readonly fname: string;
    readonly ftype: IRTypeSignature;

    readonly offset: number;

    constructor(fkey: string, enclosingtype: IRTypeSignature, fname: string, ftype: IRTypeSignature, offset: number) {
        this.fkey = fkey;
        this.enclosingtype = enclosingtype;
        this.fname = fname;
        this.ftype = ftype;
        this.offset = offset;
    }
}

enum LayoutTag {
    Value  = "Value",
    Ref    = "Ref",
    Tagged = "Tagged"
}

class TypeInfo {
    readonly tkey: string;
    readonly tsig: IRTypeSignature;

    readonly bsqtypeid: number;
    readonly bytesize: number;
    readonly slotcount: number;
    readonly tag: LayoutTag;

    readonly ptrmask: string | undefined; // NULL is for leaf values or structs
    readonly vtable: FieldOffsetInfo[] | undefined;

    constructor(tkey: string, tsig: IRTypeSignature, bsqtypeid: number, bytesize: number, slotcount: number, tag: LayoutTag, ptrmask: string | undefined, vtable: FieldOffsetInfo[] | undefined) {
        this.tkey = tkey;
        this.tsig = tsig;

        this.bsqtypeid = bsqtypeid;
        this.bytesize = bytesize;
        this.slotcount = slotcount;
        this.tag = tag;
        
        this.ptrmask = ptrmask;
        this.vtable = vtable;
    }
}

class TypeInfoManager {
    private typeInfoMap: Map<string, TypeInfo>;

    static readonly c_ref_pass_size: number = 32; //Bytes used for ref passing (pointer + typeid + extra)

    constructor() {
        this.typeInfoMap = new Map<string, TypeInfo>();
    }

    hasTypeInfo(tkey: string): boolean {
        return this.typeInfoMap.has(tkey);
    }

    getTypeInfo(tkey: string): TypeInfo {
        assert(this.typeInfoMap.has(tkey), `TypeInfoManager::getTypeInfo - Missing type info for key ${tkey}`);
        
        return this.typeInfoMap.get(tkey) as TypeInfo;
    }

    addTypeInfo(tkey: string, typeInfo: TypeInfo): void {
        if(this.typeInfoMap.has(tkey))  {
            console.log(this.typeInfoMap.get(tkey));
        }

        assert(!this.typeInfoMap.has(tkey), `TypeInfoManager::addTypeInfo - Duplicate type info for key ${tkey}`);

        this.typeInfoMap.set(tkey, typeInfo);
    }

    generateAllocatorNameForTypeKeyGeneral(tkey: string): string | undefined {
        const tii = this.getTypeInfo(tkey);
        if(tii.tag !== LayoutTag.Ref) {
            return undefined;
        }

        return TransformCPPNameManager.convertTypeKey(tkey) + "_allocator";
    }

    generateAllocatorNameForTypeKeySpecial(tkey: string): string[] | undefined {
        const tii = this.getTypeInfo(tkey);

        if(tii.tkey === "CString") {
            return [
                `PosRBTreeLeaf_CString_allocator`,
                `PosRBTreeNode_CString_allocator`
            ];
        }
        else if (tii.tkey === "String") {
            return [
                `PosRBTreeLeaf_String_allocator`,
                `PosRBTreeNode_String_allocator`
            ];
        }
        else if (tii.tkey.startsWith("List")) {
            return [
                `PosRBTreeLeaf_${TransformCPPNameManager.convertTypeKey(tkey)}_allocator`,
                `PosRBTreeNode_${TransformCPPNameManager.convertTypeKey(tkey)}_allocator`
            ];
        }
        else {
            if(tii.tag !== LayoutTag.Ref) {
                return undefined;
            }

            assert(false, `TypeInfoManager::generateAllocatorNameForTypeKeySpecial - No special allocator for type key ${tkey}`);
        }
    }

    generateAllocatorNameForTypeKeyGeneralMapEntry(tkey: string): string | undefined {
        const tii = this.getTypeInfo(tkey);
        if(tii.tag !== LayoutTag.Ref) {
            return undefined;
        }

        return `{ ${tii.bsqtypeid}, &ᐸRuntimeᐳ::${TransformCPPNameManager.convertTypeKey(tkey) + "_allocator"} }`;
    }

    generateAllocatorNameForTypeKeySpecialMapEntry(tkey: string): string[] | undefined {
        const tii = this.getTypeInfo(tkey);

        if(tii.tkey === "CString") {
            return [
                `{ ᐸRuntimeᐳ::WELL_KNOWN_TYPE_ID_POSRB_TREE_LEAF_CSTRING, &ᐸRuntimeᐳ::PosRBTreeLeaf_CString_allocator }`,
                `{ ᐸRuntimeᐳ::WELL_KNOWN_TYPE_ID_POSRB_TREE_NODE_CSTRING, &ᐸRuntimeᐳ::PosRBTreeNode_CString_allocator }`
            ];
        }
        else if (tii.tkey === "String") {
            return [
                `{ ᐸRuntimeᐳ::WELL_KNOWN_TYPE_ID_POSRB_TREE_LEAF_STRING, &ᐸRuntimeᐳ::PosRBTreeLeaf_String_allocator }`,
                `{ ᐸRuntimeᐳ::WELL_KNOWN_TYPE_ID_POSRB_TREE_NODE_STRING, &ᐸRuntimeᐳ::PosRBTreeNode_String_allocator }`
            ];
        }
        else if (tii.tkey.startsWith("List")) {
            return [
                `{ ${tii.bsqtypeid}, &ᐸRuntimeᐳ::PosRBTreeLeaf_${TransformCPPNameManager.convertTypeKey(tkey)}_allocator }`,
                `{ ${tii.bsqtypeid}, &ᐸRuntimeᐳ::PosRBTreeNode_${TransformCPPNameManager.convertTypeKey(tkey)}_allocator }`
            ];
        }
        else {
            if(tii.tag !== LayoutTag.Ref) {
                return undefined;
            }

            assert(false, `TypeInfoManager::generateAllocatorNameForTypeKeySpecial - No special allocator for type key ${tkey}`);
        }
    }

    emitTypeInfoDecl(tkey: string): string {
        const typeinfo = this.getTypeInfo(tkey);
        const tk = TransformCPPNameManager.convertTypeKey(tkey);
        
        let layouttag = "";
        if(typeinfo.tag === LayoutTag.Value) {
            layouttag = "Value";
        }
        else if(typeinfo.tag === LayoutTag.Ref) {
            layouttag = "Ref";
        }
        else {
            layouttag = "Tagged";
        }

        assert(typeinfo.vtable?.length === 0, `TypeInfoManager::emitTypeInfoDecl - VTable emission not yet supported for type key ${tkey}`);

        return `constexpr TypeInfo g_typeinfo_${tk} = { ${typeinfo.bsqtypeid}, ${typeinfo.bytesize}, ${typeinfo.slotcount}, LayoutTag::${layouttag}, ${typeinfo.ptrmask ?? "BSQ_PTR_MASK_LEAF"}, "${tk}", nullptr };`;
    }

    emitTypeAsParameter(tkey: string, isreftagged: boolean): string {
        const typeinfo = this.getTypeInfo(tkey);

        const rtspec = (isreftagged ? "&" : "");
        if(typeinfo.tag === LayoutTag.Ref) {
            return TransformCPPNameManager.convertTypeKey(tkey) + "*" + rtspec;
        }
        else if(typeinfo.tsig instanceof IRLambdaParameterPackTypeSignature) {
            return "const " + TransformCPPNameManager.convertTypeKey(tkey) + "&";
        }
        else {
            if(typeinfo.bytesize <= TypeInfoManager.c_ref_pass_size) {
                return TransformCPPNameManager.convertTypeKey(tkey) + rtspec;
            }
            else {
                return TransformCPPNameManager.convertTypeKey(tkey) + "&";                
            }
        }
    }

    emitTypeAsReturn(tkey: string): string {
        if(tkey === "Void") {
            return "void"; //special case for void functions
        }
        else {
            const typeinfo = this.getTypeInfo(tkey);

            if(typeinfo.tag !== LayoutTag.Ref) {
                return TransformCPPNameManager.convertTypeKey(tkey);
            }
            else {
                return TransformCPPNameManager.convertTypeKey(tkey) + "*";            
            }
        }
    }

    emitTypeAsMemberField(tkey: string): string {
        const typeinfo = this.getTypeInfo(tkey);

        if(typeinfo.tag !== LayoutTag.Ref) {
            return TransformCPPNameManager.convertTypeKey(tkey);
        }
        else {
            return TransformCPPNameManager.convertTypeKey(tkey) + "*";            
        }
    }

    emitTypeAsStd(tkey: string): string {
        const typeinfo = this.getTypeInfo(tkey);

        if(typeinfo.tag !== LayoutTag.Ref) {
            return TransformCPPNameManager.convertTypeKey(tkey);
        }
        else {
            return TransformCPPNameManager.convertTypeKey(tkey) + "*";            
        }
    }

    private isRecursiveTypeKey(tkey: string, irasm: IRAssembly): boolean {
        return irasm.typedepcycles.some((cycle) => {
            return cycle.some((tt) => tt.tkeystr === tkey);
        });
    }

    private isNominalRecursiveType(ttype: IRTypeSignature, irasm: IRAssembly): boolean {
        if(!(ttype instanceof IRNominalTypeSignature)) {
            return false;
        }

        return this.isRecursiveTypeKey(ttype.tkeystr, irasm);
    }

    private isSizeOkForValueLayout(bytesize: number): boolean {
        return bytesize <= 64;
    }

    private static computeValueMaskOfK(k: number): string {
        return Array(k).fill("0").join("");
    }

    private static computeTaggedMaskOfK(k: number): string {
        return "2" + Array(k).fill("0").join("");
    }

    private processInfoGenerationForEntity(tdecl: IRAbstractEntityTypeDecl, irasm: IRAssembly): TypeInfo {
        if(tdecl instanceof IRSomeTypeDecl) {
            const oftinfo = this.processInfoGenerationForType(tdecl.ttype, irasm);

            const ttid = this.typeInfoMap.size;
            if(oftinfo.tag === LayoutTag.Ref) {
                this.addTypeInfo(tdecl.tkey, new TypeInfo(tdecl.tkey, new IRNominalTypeSignature(tdecl.tkey), ttid, 8, 1, LayoutTag.Value, "1", undefined));
            }
            else {
                this.addTypeInfo(tdecl.tkey, new TypeInfo(tdecl.tkey, new IRNominalTypeSignature(tdecl.tkey), ttid, oftinfo.bytesize, oftinfo.slotcount, oftinfo.tag, oftinfo.ptrmask, undefined));
            }
            
            return this.getTypeInfo(tdecl.tkey);
        }
        else if(tdecl instanceof IRAbstractCollectionTypeDecl) {
            if(tdecl instanceof IRListTypeDecl) {
                const oftinfo = this.processInfoGenerationForType(tdecl.oftype, irasm);

                const ttid = this.typeInfoMap.size + 5; //+5 for the leaf, node, tree, inline, and tree repr type infos we need to generate for all the parts in the list
                const ldatasize = Math.max(MAX_LIST_INLINE_BYTES, oftinfo.bytesize);
                const ltotalsize = 8 + ldatasize; //8 bytes for for the tag

                const mask = TypeInfoManager.computeTaggedMaskOfK(ltotalsize / 8);
                this.addTypeInfo(tdecl.tkey, new TypeInfo(tdecl.tkey, new IRNominalTypeSignature(tdecl.tkey), ttid, ltotalsize, ltotalsize / 8, LayoutTag.Tagged, mask, undefined));

                return this.getTypeInfo(tdecl.tkey);
            }
            else {
                assert(false, `TypeInfoManager::processInfoGenerationForEntity - Unsupported collection type declaration for key ${tdecl.tkey}`);
            }
        }
        else {
            assert(tdecl instanceof IREntityTypeDecl, `TypeInfoManager::processInfoGenerationForEntity - Unsupported entity type declaration for key ${tdecl.tkey}`);

            const etdecl = tdecl as IREntityTypeDecl;
            let totalbytesize = 0;
            let totalslotcount = 0;
            let eptrmask = "";
            const vtable: FieldOffsetInfo[] | undefined = undefined;

            const mustref = this.isRecursiveTypeKey(tdecl.tkey, irasm);
            for(const fdecl of etdecl.saturatedBFieldInfo) {
                if(this.isNominalRecursiveType(fdecl.ftype, irasm)) {
                    if((fdecl instanceof IRConceptTypeDecl) || (fdecl instanceof IRDatatypeTypeDecl)) {
                        totalbytesize += 16;
                        totalslotcount += 2;
                        eptrmask += "20";
                    }
                    else {
                        totalbytesize += 8;
                        totalslotcount += 1;
                        eptrmask += "1";
                    }
                }
                else {
                    const ftypeinfo = this.processInfoGenerationForType(fdecl.ftype, irasm);

                    if(ftypeinfo.tag === LayoutTag.Ref) {
                        totalbytesize += 8;
                        totalslotcount += 1;
                        eptrmask += "1";
                    }
                    else {
                        totalbytesize += ftypeinfo.bytesize;
                        totalslotcount += ftypeinfo.slotcount;
                        eptrmask += ftypeinfo.ptrmask || TypeInfoManager.computeValueMaskOfK(ftypeinfo.slotcount);
                    }
                }
            }

            let ptrmask: string | undefined = undefined; 
            if(eptrmask.includes("1") || eptrmask.includes("2")) {
                ptrmask = eptrmask;
            }

            const ttid = this.typeInfoMap.size;
            if(!mustref && this.isSizeOkForValueLayout(totalbytesize)) {
                this.addTypeInfo(tdecl.tkey, new TypeInfo(tdecl.tkey, new IRNominalTypeSignature(tdecl.tkey), ttid, totalbytesize, totalslotcount, LayoutTag.Value, ptrmask, vtable));
            }
            else {
                this.addTypeInfo(tdecl.tkey, new TypeInfo(tdecl.tkey, new IRNominalTypeSignature(tdecl.tkey), ttid, totalbytesize, totalslotcount, LayoutTag.Ref, ptrmask, vtable));
            }

            return this.getTypeInfo(tdecl.tkey);
        }
    }

    private processInfoGenerationForConcept(tdecl: IRAbstractEntityTypeDecl, irasm: IRAssembly): TypeInfo {
        if(tdecl instanceof IROptionTypeDecl) {
            const oftinfo = this.processInfoGenerationForType(tdecl.ttype, irasm);

            const ttid = this.typeInfoMap.size;
            if(oftinfo.tag === LayoutTag.Ref) {
                this.addTypeInfo(tdecl.tkey, new TypeInfo(tdecl.tkey, new IRNominalTypeSignature(tdecl.tkey), ttid, 16, 2, LayoutTag.Tagged, "20", undefined));
            }
            else {
                let spm = TypeInfoManager.computeTaggedMaskOfK(oftinfo.slotcount);
                this.addTypeInfo(tdecl.tkey, new TypeInfo(tdecl.tkey, new IRNominalTypeSignature(tdecl.tkey), ttid, oftinfo.bytesize + 8, oftinfo.slotcount + 1, LayoutTag.Tagged, spm, undefined));
            }
            
            return this.getTypeInfo(tdecl.tkey);
        }
        else {
            assert(tdecl instanceof IRConceptTypeDecl, `TypeInfoManager::processInfoGenerationForConcept - Unsupported concept type declaration for key ${tdecl.tkey}`);

            let totalbytesize = 0;
            let totalslotcount = 0;

            const subtypes = irasm.concretesubtypes.get(tdecl.tkey) as IRTypeSignature[];
            for(const subtt of subtypes) {
              if(this.isNominalRecursiveType(subtt, irasm)) {
                    totalbytesize = Math.max(totalbytesize, 8);
                    totalslotcount = Math.max(totalslotcount, 1);
                }
                else {
                    const ftypeinfo = this.processInfoGenerationForType(subtt, irasm);

                    if(ftypeinfo.tag === LayoutTag.Ref) {
                        totalbytesize = Math.max(totalbytesize, 8);
                        totalslotcount = Math.max(totalslotcount, 1);
                    }
                    else {
                        totalbytesize = Math.max(totalbytesize, ftypeinfo.bytesize);
                        totalslotcount = Math.max(totalslotcount, ftypeinfo.slotcount);
                    }
                }
            }

            const ttid = this.typeInfoMap.size;
            let eptrmask = TypeInfoManager.computeTaggedMaskOfK(totalslotcount);
            this.addTypeInfo(tdecl.tkey, new TypeInfo(tdecl.tkey, new IRNominalTypeSignature(tdecl.tkey), ttid, totalbytesize, totalslotcount, LayoutTag.Tagged, eptrmask, undefined));

            return this.getTypeInfo(tdecl.tkey);
        }
    }

    private processInfoGenerationForFormat(ttype: IRFormatTypeSignature, irasm: IRAssembly): TypeInfo {
        const ttid = this.typeInfoMap.size;
        this.addTypeInfo(ttype.tkeystr, new TypeInfo(ttype.tkeystr, ttype, ttid, 8, 1, LayoutTag.Value, undefined, undefined));

        return this.getTypeInfo(ttype.tkeystr);
    }

    private processInfoGenerationForType(ttype: IRTypeSignature, irasm: IRAssembly): TypeInfo {
        if(this.hasTypeInfo(ttype.tkeystr)) {
            return this.getTypeInfo(ttype.tkeystr);
        }

        if(ttype instanceof IRNominalTypeSignature) {
            const ddecl = irasm.alltypes.get(ttype.tkeystr) as IRAbstractNominalTypeDecl;
            if(ddecl instanceof IRAbstractEntityTypeDecl) {
                return this.processInfoGenerationForEntity(ddecl, irasm);
            }
            else {
                return this.processInfoGenerationForConcept(ddecl, irasm);
            }
        }
        else {
            assert(!(ttype instanceof IRVoidTypeSignature), "Don't think we should ever be doing this...");

            if(ttype instanceof IREListTypeSignature) {
                assert(false, `TypeInfoManager::processInfoGenerationForType - Unsupported elist type signature for key ${ttype.tkeystr}`);
            }
            else if(ttype instanceof IRDashResultTypeSignature) {
                assert(false, `TypeInfoManager::processInfoGenerationForType - Unsupported dash result type signature for key ${ttype.tkeystr}`);
            }
            else if(ttype instanceof IRFormatTypeSignature) {
                return this.processInfoGenerationForFormat(ttype, irasm);
            }
            else if(ttype instanceof IRLambdaParameterPackTypeSignature) {
                assert(false, `TypeInfoManager::processInfoGenerationForType - Unsupported lambda parameter pack type signature for key ${ttype.tkeystr}`);
            }
            else {
                assert(false, `TypeInfoManager::processInfoGenerationForType - Unsupported type signature for key ${ttype.tkeystr}`);
            }
        }
    }

    static generateTypeInfos(irasm: IRAssembly): TypeInfoManager {
        const timgr = new TypeInfoManager();

        //setup the well-known primitive types
        timgr.addTypeInfo("None", new TypeInfo("None", new IRNominalTypeSignature("None"), 0, 8, 1, LayoutTag.Value, undefined, undefined));
        timgr.addTypeInfo("Bool", new TypeInfo("Bool", new IRNominalTypeSignature("Bool"), 1, 8, 1, LayoutTag.Value, undefined, undefined));
        timgr.addTypeInfo("Int", new TypeInfo("Int", new IRNominalTypeSignature("Int"), 2, 8, 1, LayoutTag.Value, undefined, undefined));
        timgr.addTypeInfo("Nat", new TypeInfo("Nat", new IRNominalTypeSignature("Nat"), 3, 8, 1, LayoutTag.Value, undefined, undefined));
        timgr.addTypeInfo("ChkInt", new TypeInfo("ChkInt", new IRNominalTypeSignature("ChkInt"), 4, 16, 2, LayoutTag.Value, undefined, undefined));
        timgr.addTypeInfo("ChkNat", new TypeInfo("ChkNat", new IRNominalTypeSignature("ChkNat"), 5, 16, 2, LayoutTag.Value, undefined, undefined));

        timgr.addTypeInfo("Float", new TypeInfo("Float", new IRNominalTypeSignature("Float"), 6, 8, 1, LayoutTag.Value, undefined, undefined));
        
        timgr.addTypeInfo("PosRBTreeLeaf_CString", new TypeInfo("PosRBTreeLeaf_CString", new IRNominalTypeSignature("PosRBTreeLeaf_CString"), 7, 40, 5, LayoutTag.Ref, undefined, undefined));
        timgr.addTypeInfo("PosRBTreeNode_CString", new TypeInfo("PosRBTreeNode_CString", new IRNominalTypeSignature("PosRBTreeNode_CString"), 8, 48, 6, LayoutTag.Ref, "002020", undefined));
        timgr.addTypeInfo("PosRBTree_CString", new TypeInfo("PosRBTree_CString", new IRNominalTypeSignature("PosRBTree_CString"), 9, 16, 2, LayoutTag.Tagged, "20", undefined));
        timgr.addTypeInfo("CStringInline", new TypeInfo("CStringInline", new IRNominalTypeSignature("CStringInline"), 10, 16, 2, LayoutTag.Value, undefined, undefined));
        timgr.addTypeInfo("CStringTree", new TypeInfo("CStringTree", new IRNominalTypeSignature("CStringTree"), 11, 16, 2, LayoutTag.Tagged, "20", undefined));
        timgr.addTypeInfo("CString", new TypeInfo("CString", new IRNominalTypeSignature("CString"), 12, 24, 3, LayoutTag.Tagged, "200", undefined));

        timgr.addTypeInfo("PosRBTreeLeaf_String", new TypeInfo("PosRBTreeLeaf_String", new IRNominalTypeSignature("PosRBTreeLeaf_String"), 13, 40, 5, LayoutTag.Ref, undefined, undefined));
        timgr.addTypeInfo("PosRBTreeNode_String", new TypeInfo("PosRBTreeNode_String", new IRNominalTypeSignature("PosRBTreeNode_String"), 14, 48, 6, LayoutTag.Ref, "002020", undefined));
        timgr.addTypeInfo("PosRBTree_String", new TypeInfo("PosRBTree_String", new IRNominalTypeSignature("PosRBTree_String"), 15, 16, 2, LayoutTag.Tagged, "20", undefined));
        timgr.addTypeInfo("StringInline", new TypeInfo("StringInline", new IRNominalTypeSignature("StringInline"), 16, 32, 4, LayoutTag.Value, undefined, undefined));
        timgr.addTypeInfo("StringTree", new TypeInfo("StringTree", new IRNominalTypeSignature("StringTree"), 17, 16, 2, LayoutTag.Tagged, "20", undefined));
        timgr.addTypeInfo("String", new TypeInfo("String", new IRNominalTypeSignature("String"), 18, 40, 5, LayoutTag.Tagged, "20000", undefined));

        timgr.addTypeInfo("ByteBufferEntry", new TypeInfo("ByteBufferEntry", new IRNominalTypeSignature("ByteBufferEntry"), 19, 512, 64, LayoutTag.Ref, undefined, undefined));
        timgr.addTypeInfo("ByteBufferBlock", new TypeInfo("ByteBufferBlock", new IRNominalTypeSignature("ByteBufferBlock"), 20, 512, 64, LayoutTag.Ref, "1111111111111111111111111111111111111111111111111111111111111111", undefined));
        timgr.addTypeInfo("ByteBuffer", new TypeInfo("ByteBuffer", new IRNominalTypeSignature("ByteBuffer"), 21, 24, 3, LayoutTag.Value, "200", undefined));

        timgr.addTypeInfo("UUIDV4", new TypeInfo("UUIDV4", new IRNominalTypeSignature("UUIDV4"), 22, 16, 2, LayoutTag.Value, undefined, undefined));
        timgr.addTypeInfo("UUIDV7", new TypeInfo("UUIDV7", new IRNominalTypeSignature("UUIDV7"), 23, 16, 2, LayoutTag.Value, undefined, undefined));

        //TODO: more primitive types

        //TODO enums
        for(let i = 0; i < irasm.enums.length; ++i) {
            const etdecl = irasm.enums[i];
            const etkey = TransformCPPNameManager.convertTypeKey(etdecl.tkey);
            const etid = timgr.typeInfoMap.size;
            const enumtd = new TypeInfo(etkey, new IRNominalTypeSignature(etkey), etid, 8, 1, LayoutTag.Value, undefined, undefined);

            timgr.addTypeInfo(etdecl.tkey, enumtd);
        }

        for(let i = 0; i < irasm.typedecls.length; ++i) {
            const tdecl = irasm.typedecls[i];
            const ttkey = TransformCPPNameManager.convertTypeKey(tdecl.tkey);
            const ttid = timgr.typeInfoMap.size;

            const utypeinfo = timgr.getTypeInfo(TransformCPPNameManager.convertTypeKey(tdecl.valuetype.tkeystr));
            const typedtd = new TypeInfo(ttkey, new IRNominalTypeSignature(ttkey), ttid, utypeinfo.bytesize, utypeinfo.slotcount, utypeinfo.tag, utypeinfo.ptrmask, undefined);
            
            timgr.addTypeInfo(tdecl.tkey, typedtd);
        }

        const cstringtypeinfo = timgr.getTypeInfo("CString");
        for(let i = 0; i < irasm.cstringoftypedecls.length; ++i) {
            const tdecl = irasm.typedecls[i];
            const ttkey = TransformCPPNameManager.convertTypeKey(tdecl.tkey);
            const ttid = timgr.typeInfoMap.size;
            const typedtd = new TypeInfo(ttkey, new IRNominalTypeSignature(ttkey), ttid, cstringtypeinfo.bytesize, cstringtypeinfo.slotcount, cstringtypeinfo.tag, cstringtypeinfo.ptrmask, undefined);
            
            timgr.addTypeInfo(tdecl.tkey, typedtd);
        }

        const stringtypeinfo = timgr.getTypeInfo("CString");
        for(let i = 0; i < irasm.stringoftypedecls.length; ++i) {
            const tdecl = irasm.typedecls[i];
            const ttkey = TransformCPPNameManager.convertTypeKey(tdecl.tkey);
            const ttid = timgr.typeInfoMap.size;
            const typedtd = new TypeInfo(ttkey, new IRNominalTypeSignature(ttkey), ttid, stringtypeinfo.bytesize, stringtypeinfo.slotcount, stringtypeinfo.tag, stringtypeinfo.ptrmask, undefined);
            
            timgr.addTypeInfo(tdecl.tkey, typedtd);
        }

        //Now handle entities with a recursive walk
        irasm.constructables.forEach((tdecl) => { if(!timgr.hasTypeInfo(tdecl.tkey)) { timgr.processInfoGenerationForEntity(tdecl, irasm); } });
        irasm.collections.forEach((tdecl) => { if(!timgr.hasTypeInfo(tdecl.tkey)) { timgr.processInfoGenerationForEntity(tdecl, irasm); } });
        irasm.eventlists.forEach((tdecl) => { if(!timgr.hasTypeInfo(tdecl.tkey)) { timgr.processInfoGenerationForEntity(tdecl, irasm); } });
        irasm.entities.forEach((tdecl) => { if(!timgr.hasTypeInfo(tdecl.tkey)) { timgr.processInfoGenerationForEntity(tdecl, irasm); } });
        irasm.datamembers.forEach((tdecl) => { if(!timgr.hasTypeInfo(tdecl.tkey)) { timgr.processInfoGenerationForEntity(tdecl, irasm); } });

        irasm.pconcepts.forEach((cdecl) => { if(!timgr.hasTypeInfo(cdecl.tkey)) { timgr.processInfoGenerationForConcept(cdecl, irasm); } });
        irasm.concepts.forEach((cdecl) => { if(!timgr.hasTypeInfo(cdecl.tkey)) { timgr.processInfoGenerationForConcept(cdecl, irasm); } });
        irasm.datatypes.forEach((cdecl) => { if(!timgr.hasTypeInfo(cdecl.tkey)) { timgr.processInfoGenerationForConcept(cdecl, irasm); } });

        irasm.elists.forEach((ttype) => { if(!timgr.hasTypeInfo(ttype.tkeystr)) { timgr.processInfoGenerationForType(ttype, irasm); } });
        irasm.dashtypes.forEach((ttype) => { if(!timgr.hasTypeInfo(ttype.tkeystr)) { timgr.processInfoGenerationForType(ttype, irasm); } });
        irasm.formats.forEach((ttype) => { if(!timgr.hasTypeInfo(ttype.tkeystr)) { timgr.processInfoGenerationForType(ttype, irasm); } });
        irasm.lpacksigs.forEach((ttype) => { if(!timgr.hasTypeInfo(ttype.tkeystr)) { timgr.processInfoGenerationForType(ttype, irasm); } });

        return timgr;
    }
}

export {
    MAX_LIST_INLINE_BYTES, LIST_T_CAPACITY,
    FieldOffsetInfo, 
    LayoutTag, TypeInfo,
    TypeInfoManager
};
