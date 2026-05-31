
import { IRAbstractCollectionTypeDecl, IRAbstractEntityTypeDecl, IRAbstractNominalTypeDecl, IRAssembly, IRConceptTypeDecl, IRDatatypeMemberEntityTypeDecl, IRDatatypeTypeDecl, IREntityTypeDecl, IRListTypeDecl, IROptionTypeDecl, IRSomeTypeDecl } from "../irdefs/irassembly.js";
import { IRDashResultTypeSignature, IREListTypeSignature, IRFormatTypeSignature, IRNominalTypeSignature, IRTypeSignature, IRVoidTypeSignature } from "../irdefs/irtype.js";
import { TransformCPPNameManager } from "./namemgr.js";

import assert from "node:assert";

//Duplicated from C++ definitions
const MAX_LIST_INLINE_BYTES = 32; //Bytes -- so 64 total when we add 8 bytes for the size and 8 bytes for the tag

function LIST_T_INLINE_CAPACITY(elem_size: number): number {
    return Math.max(Math.floor(MAX_LIST_INLINE_BYTES / elem_size), 1);
}

function LIST_T_LEAF_CAPACITY(elem_size: number): number {
    //return Math.max(LIST_T_INLINE_CAPACITY(elem_size) * 4, 4);
    return 8;
}

class VirtualInvokeInfo {
    readonly ikey: string;

    readonly enclosingtype: IRTypeSignature;
    readonly fname: string;

    constructor(ikey: string, enclosingtype: IRTypeSignature, fname: string) {
        this.ikey = ikey;
        this.enclosingtype = enclosingtype;
        this.fname = fname;
    }
}

class FieldOffsetInfo {
    readonly fkey: string;
    readonly fid: number;

    readonly enclosingtype: IRTypeSignature;
    readonly fname: string;
    readonly ftype: IRTypeSignature;

    readonly offset: number;

    constructor(fkey: string, fid: number, enclosingtype: IRTypeSignature, fname: string, ftype: IRTypeSignature, offset: number) {
        this.fkey = fkey;
        this.fid = fid;
        this.enclosingtype = enclosingtype;
        this.fname = fname;
        this.ftype = ftype;
        this.offset = offset;
    }
}

enum LayoutTag {
    Value  = "Value",
    Ref    = "Ref"
}

class LayoutInfo {
    readonly tkey: string;
    readonly tsig: IRTypeSignature;

    readonly bytesize: number;
    readonly slotcount: number;

    readonly layoutmask: string; //This is not ptr mask it is ALWAYS the mask for the inline repr

    constructor(tkey: string, tsig: IRTypeSignature, bytesize: number, layoutmask: string) {
        this.tkey = tkey;
        this.tsig = tsig;
        this.bytesize = bytesize;
        this.slotcount = bytesize / 8;
        this.layoutmask = layoutmask;
    }
}

class TypeInfo {
    readonly tkey: string;
    readonly tsig: IRTypeSignature;

    readonly bsqtypeid: number;
    readonly bytesize: number;
    readonly slotcount: number;
    readonly tag: LayoutTag;

    readonly ptrmask: string | undefined; //undefined is for leaf values or structs

    readonly itable: VirtualInvokeInfo[] = [];
    readonly ftable: FieldOffsetInfo[]  = [];

    constructor(tkey: string, tsig: IRTypeSignature, bsqtypeid: number, bytesize: number, tag: LayoutTag, ptrmask: string | undefined) {
        this.tkey = tkey;
        this.tsig = tsig;

        this.bsqtypeid = bsqtypeid;
        this.bytesize = bytesize;
        this.slotcount = bytesize / 8;
        this.tag = tag;

        this.ptrmask = ptrmask;
    }

    getAccessor(): string {
        return this.tag === LayoutTag.Ref ? "->" : ".";
    }
}

class TypeInfoManager {
    private layoutInfoMap: Map<string, LayoutInfo> = new Map<string, LayoutInfo>();
    private typeInfoMap: Map<string, TypeInfo> = new Map<string, TypeInfo>();
    private fieldidctr = 0;

    static readonly c_ref_pass_size: number = 32; //Bytes used for ref passing (pointer + typeid + extra)

    constructor() {
    }

     private static isAllNopMask(mask: string): boolean {
        return !/[1-5]/.test(mask);
    }

    private static staticLayoutToPtrMaskConvert(layoutmask: string): string | undefined {
        return TypeInfoManager.isAllNopMask(layoutmask) ? undefined : layoutmask;
    }

    hasLayoutInfo(tkey: string): boolean {
        return this.layoutInfoMap.has(tkey);
    }

    getLayoutInfo(tkey: string): LayoutInfo {
        assert(this.layoutInfoMap.has(tkey), `TypeInfoManager::getLayoutInfo - Missing type info for key ${tkey}`);
        
        return this.layoutInfoMap.get(tkey) as LayoutInfo;
    }

    addLayoutInfo(tkey: string, typeInfo: LayoutInfo): void {
        assert(!this.layoutInfoMap.has(tkey), `TypeInfoManager::addLayoutInfo - Duplicate type info for key ${tkey}`);

        this.layoutInfoMap.set(tkey, typeInfo);
    }

    hasTypeInfo(tkey: string): boolean {
        return this.typeInfoMap.has(tkey);
    }

    getTypeInfo(tkey: string): TypeInfo {
        assert(this.typeInfoMap.has(tkey), `TypeInfoManager::getTypeInfo - Missing type info for key ${tkey}`);
        
        return this.typeInfoMap.get(tkey) as TypeInfo;
    }

    addTypeInfo(tkey: string, typeInfo: TypeInfo): void {
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
            const posrb_treeleafid = tii.bsqtypeid - 5;
            const posrb_treenodeid = tii.bsqtypeid - 4;
        
            return [
                `{ ${posrb_treeleafid}, &ᐸRuntimeᐳ::PosRBTreeLeaf_${TransformCPPNameManager.convertTypeKey(tkey)}_allocator }`,
                `{ ${posrb_treenodeid}, &ᐸRuntimeᐳ::PosRBTreeNode_${TransformCPPNameManager.convertTypeKey(tkey)}_allocator }`
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
        else {
            layouttag = "Ref";
        }

        assert(typeinfo.itable.length === 0, `TypeInfoManager::emitTypeInfoDecl - ITable emission not yet supported for type key ${tkey}`);

        return `constexpr TypeInfo g_typeinfo_${tk} = { ${typeinfo.bsqtypeid}, ${typeinfo.bytesize}, ${typeinfo.slotcount}, LayoutTag::${layouttag}, BSQ_TYPEINFO_NO_ESLOT, ${typeinfo.ptrmask ?? "BSQ_PTR_MASK_LEAF"}, "${tk}", nullptr };`;
    }

    private emitTypeAsEListSelfDescribing(tinfo: TypeInfo): string {
        const entries = (tinfo.tsig as IREListTypeSignature).entries.map((ee) => this.emitTypeAsStd(ee.tkeystr));
        return `std::tuple<${entries.join(", ")}>`;
    }

    emitTypeAsParameter(tkey: string, isreftagged: boolean, islambda: boolean): string {
        if(islambda) {
            return "const " + TransformCPPNameManager.convertTypeKey(tkey) + "_ldata_&";
        }
        else {
            const typeinfo = this.getTypeInfo(tkey);

            if(typeinfo.tsig instanceof IREListTypeSignature) {
                return "const " + this.emitTypeAsEListSelfDescribing(typeinfo) + "&";
            }

            const rtspec = (isreftagged ? "&" : "");
            if(typeinfo.tag === LayoutTag.Ref) {
                return TransformCPPNameManager.convertTypeKey(tkey) + "*" + rtspec;
            }
            else {
                if(typeinfo.bytesize <= TypeInfoManager.c_ref_pass_size) {
                    return TransformCPPNameManager.convertTypeKey(tkey) + rtspec;
                }
                else {
                    return (!isreftagged ? "const " : "") + TransformCPPNameManager.convertTypeKey(tkey) + "&";                
                }
            }
        }
    }

    emitTypeAsReturn(tkey: string): string {
        if(tkey === "Void") {
            return "void"; //special case for void functions
        }
        else {
            const typeinfo = this.getTypeInfo(tkey);

            if(typeinfo.tsig instanceof IREListTypeSignature) {
                return this.emitTypeAsEListSelfDescribing(typeinfo);
            }

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

        if(typeinfo.tsig instanceof IREListTypeSignature) {
            return this.emitTypeAsEListSelfDescribing(typeinfo);
        }

        if(typeinfo.tag !== LayoutTag.Ref) {
            return TransformCPPNameManager.convertTypeKey(tkey);
        }
        else {
            return TransformCPPNameManager.convertTypeKey(tkey) + "*";            
        }
    }

    emitTypeAsStd(tkey: string): string {
        const typeinfo = this.getTypeInfo(tkey);

        if(typeinfo.tsig instanceof IREListTypeSignature) {
            return this.emitTypeAsEListSelfDescribing(typeinfo);
        }

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

    private isSizeOkForValueLayout(bytesize: number): boolean {
        return bytesize <= 64;
    }

    private static computeValueMaskOfK(k: number): string {
        return Array(k).fill("0").join("");
    }

    private static computeListMaskOfK(k: number, ptrmask: string): string {
        return "5" + Array(k).fill(ptrmask).join("");
    }

    private generateLayoutInfoForEntity(tdecl: IRAbstractEntityTypeDecl, irasm: IRAssembly): LayoutInfo {
        if(tdecl instanceof IRSomeTypeDecl) {
            const oftinfo = this.generateLayoutInfoForType(tdecl.ttype, irasm);
            this.addLayoutInfo(tdecl.tkey, new LayoutInfo(tdecl.tkey, new IRNominalTypeSignature(tdecl.tkey), oftinfo.bytesize, oftinfo.layoutmask));
        }
        else if(tdecl instanceof IRAbstractCollectionTypeDecl) {
            if(tdecl instanceof IRListTypeDecl) {
                const oftinfo = this.generateLayoutInfoForType(tdecl.oftype, irasm);
                
                const ldatasize = LIST_T_INLINE_CAPACITY(oftinfo.bytesize) * oftinfo.bytesize;
                const ltotalsize = 8 + ldatasize; //8 for the count field
                const mask = TypeInfoManager.computeListMaskOfK(LIST_T_INLINE_CAPACITY(oftinfo.bytesize), oftinfo.layoutmask);

                this.addLayoutInfo(tdecl.tkey, new LayoutInfo(tdecl.tkey, new IRNominalTypeSignature(tdecl.tkey), ltotalsize, mask));
                return this.getLayoutInfo(tdecl.tkey);
            }
            else {
                assert(false, `TypeInfoManager::processInfoGenerationForEntity - Unsupported collection type declaration for key ${tdecl.tkey}`);
            }
        }
        else {
            assert((tdecl instanceof IREntityTypeDecl) || (tdecl instanceof IRDatatypeMemberEntityTypeDecl), `TypeInfoManager::processInfoGenerationForEntity - Unsupported entity type declaration for key ${tdecl.tkey}`);

            if(this.isRecursiveTypeKey(tdecl.tkey, irasm)) {
                this.addLayoutInfo(tdecl.tkey, new LayoutInfo(tdecl.tkey, new IRNominalTypeSignature(tdecl.tkey), 8, "1"));
            }
            else {
                let totalbytesize = 0;
                let layoutmask = "";

                for(let i = 0; i < tdecl.saturatedBFieldInfo.length; ++i) {
                    const ftypeinfo = this.generateLayoutInfoForType(tdecl.saturatedBFieldInfo[i].ftype, irasm);

                    totalbytesize += ftypeinfo.bytesize;
                    layoutmask += ftypeinfo.layoutmask;
                }

                // If the entity has no fields, it should still have a size of 8 bytes and 1 slot
                if(tdecl.saturatedBFieldInfo.length === 0) {
                    totalbytesize = 8;
                    layoutmask = "0";
                }

                if(!this.isSizeOkForValueLayout(totalbytesize)) {
                    this.addLayoutInfo(tdecl.tkey, new LayoutInfo(tdecl.tkey, new IRNominalTypeSignature(tdecl.tkey), 8, "1"));                    
                }
                else {
                    this.addLayoutInfo(tdecl.tkey, new LayoutInfo(tdecl.tkey, new IRNominalTypeSignature(tdecl.tkey), totalbytesize, layoutmask));
                }
            }
        }

        return this.getLayoutInfo(tdecl.tkey);
    }

    private generateLayoutInfoForConcept(tdecl: IRAbstractEntityTypeDecl, irasm: IRAssembly): LayoutInfo {
        if(tdecl instanceof IROptionTypeDecl) {
            const oftinfo = this.generateLayoutInfoForType(tdecl.ttype, irasm);

            let spm = TypeInfoManager.isAllNopMask(oftinfo.layoutmask) ? ("0" + oftinfo.layoutmask) : ("2" + TypeInfoManager.computeValueMaskOfK(oftinfo.bytesize));
            this.addLayoutInfo(tdecl.tkey, new LayoutInfo(tdecl.tkey, new IRNominalTypeSignature(tdecl.tkey), oftinfo.bytesize + 8, spm));
        }
        else {
            assert((tdecl instanceof IRConceptTypeDecl) || (tdecl instanceof IRDatatypeTypeDecl), `TypeInfoManager::processInfoGenerationForConcept - Unsupported concept type declaration for key ${tdecl.tkey}`);

            // If the concept has no subtypes, it should still have a size of 8 bytes
            let maxbytesize = 8;
            let allnops = true;
            const subtypes = irasm.concretesubtypes.get(tdecl.tkey) as IRTypeSignature[];
            for(let i = 0; i < subtypes.length; ++i) {
                const ftypeinfo = this.generateLayoutInfoForType(subtypes[i], irasm);
                maxbytesize = Math.max(maxbytesize, ftypeinfo.bytesize);
                allnops = allnops && TypeInfoManager.isAllNopMask(ftypeinfo.layoutmask)
            }

            let layoutmask = (allnops ? "0" : "2") + TypeInfoManager.computeValueMaskOfK(maxbytesize / 8);
            this.addLayoutInfo(tdecl.tkey, new LayoutInfo(tdecl.tkey, new IRNominalTypeSignature(tdecl.tkey), maxbytesize + 8, layoutmask));
        }

        return this.getLayoutInfo(tdecl.tkey);
    }

    private generateLayoutInfoForElist(ttype: IREListTypeSignature, irasm: IRAssembly): LayoutInfo {
        let totalbytesize = 0;
        let layoutmask = "";

        for(let i = 0; i < ttype.entries.length; ++i) {
            const ftypeinfo = this.generateLayoutInfoForType(ttype.entries[i], irasm);
            totalbytesize += ftypeinfo.bytesize;
            layoutmask += ftypeinfo.layoutmask;
        }

        this.addLayoutInfo(ttype.tkeystr, new LayoutInfo(ttype.tkeystr, ttype, totalbytesize, layoutmask));
        return this.getLayoutInfo(ttype.tkeystr);
    }

    private generateLayoutInfoForFormat(ttype: IRFormatTypeSignature, irasm: IRAssembly): LayoutInfo {
        this.addLayoutInfo(ttype.tkeystr, new LayoutInfo(ttype.tkeystr, ttype, 8, "0"));
        return this.getLayoutInfo(ttype.tkeystr);
    }

    private generateLayoutInfoForType(ttype: IRTypeSignature, irasm: IRAssembly): LayoutInfo {
        if(this.hasLayoutInfo(ttype.tkeystr)) {
            return this.getLayoutInfo(ttype.tkeystr);
        }

        if(ttype instanceof IRNominalTypeSignature) {
            const ddecl = irasm.alltypes.get(ttype.tkeystr) as IRAbstractNominalTypeDecl;
            if(ddecl instanceof IRAbstractEntityTypeDecl) {
                return this.generateLayoutInfoForEntity(ddecl, irasm);
            }
            else {
                return this.generateLayoutInfoForConcept(ddecl, irasm);
            }
        }
        else {
            assert(!(ttype instanceof IRVoidTypeSignature), "Don't think we should ever be doing this...");

            if(ttype instanceof IREListTypeSignature) {
                return this.generateLayoutInfoForElist(ttype, irasm);
            }
            else if(ttype instanceof IRDashResultTypeSignature) {
                assert(false, `TypeInfoManager::processInfoGenerationForType - Unsupported dash result type signature for key ${ttype.tkeystr}`);
            }
            else if(ttype instanceof IRFormatTypeSignature) {
                return this.generateLayoutInfoForFormat(ttype, irasm);
            }
            else {
                assert(false, `TypeInfoManager::processInfoGenerationForType - Unsupported type signature for key ${ttype.tkeystr}`);
            }
        }
    }

    private processInfoGenerationForEntity(tdecl: IRAbstractEntityTypeDecl, irasm: IRAssembly): TypeInfo {
        if(tdecl instanceof IRSomeTypeDecl) {
            const oftinfo = this.generateLayoutInfoForType(tdecl.ttype, irasm);

            const ttid = this.typeInfoMap.size;
            this.addTypeInfo(tdecl.tkey, new TypeInfo(tdecl.tkey, new IRNominalTypeSignature(tdecl.tkey), ttid, oftinfo.bytesize, LayoutTag.Value, TypeInfoManager.staticLayoutToPtrMaskConvert(oftinfo.layoutmask)));
        }
        else if(tdecl instanceof IRAbstractCollectionTypeDecl) {
            if(tdecl instanceof IRListTypeDecl) {
                const oftinfo = this.generateLayoutInfoForType(tdecl.oftype, irasm);
                
                const ttid = this.typeInfoMap.size + 5; //+5 for the leaf, node, tree, inline, and tree repr type infos we need to generate for all the parts in the list
                const ldatasize = LIST_T_INLINE_CAPACITY(oftinfo.bytesize) * oftinfo.bytesize;
                const ltdatasize = LIST_T_LEAF_CAPACITY(oftinfo.bytesize) * oftinfo.bytesize;
                const ltotalsize = 8 + ldatasize; //8 for the count field

                const mask = TypeInfoManager.computeListMaskOfK(LIST_T_INLINE_CAPACITY(oftinfo.bytesize), oftinfo.layoutmask);

                //Add placeholders for the implicitly generated list types -- use dummy values for mask here since we just need to know they exist -- list emitter will handle the rest
                this.addTypeInfo(`PosRBTreeLeaf_${tdecl.tkey}`, new TypeInfo(`PosRBTreeLeaf_${tdecl.tkey}`, new IRNominalTypeSignature(`PosRBTreeLeaf_${tdecl.tkey}`), ttid - 5, (ldatasize + 8), LayoutTag.Ref, undefined));
                this.addTypeInfo(`PosRBTreeNode_${tdecl.tkey}`, new TypeInfo(`PosRBTreeNode_${tdecl.tkey}`, new IRNominalTypeSignature(`PosRBTreeNode_${tdecl.tkey}`), ttid - 4, (ldatasize + 32), LayoutTag.Ref, undefined));
                this.addTypeInfo(`PosRBTree_${tdecl.tkey}`, new TypeInfo(`PosRBTree_${tdecl.tkey}`, new IRNominalTypeSignature(`PosRBTree_${tdecl.tkey}`), ttid - 3, 8, LayoutTag.Ref, undefined));
                this.addTypeInfo(`${tdecl.tkey}Inline`, new TypeInfo(`${tdecl.tkey}Inline`, new IRNominalTypeSignature(`${tdecl.tkey}Inline`), ttid - 2, ltdatasize + 8, LayoutTag.Value, undefined));
                this.addTypeInfo(`${tdecl.tkey}Tree`, new TypeInfo(`${tdecl.tkey}Tree`, new IRNominalTypeSignature(`${tdecl.tkey}Tree`), ttid - 1, 16, LayoutTag.Value, undefined));

                this.addTypeInfo(tdecl.tkey, new TypeInfo(tdecl.tkey, new IRNominalTypeSignature(tdecl.tkey), ttid, ltotalsize, LayoutTag.Value, mask));
            }
            else {
                assert(false, `TypeInfoManager::processInfoGenerationForEntity - Unsupported collection type declaration for key ${tdecl.tkey}`);
            }
        }
        else {
            assert((tdecl instanceof IREntityTypeDecl) || (tdecl instanceof IRDatatypeMemberEntityTypeDecl), `TypeInfoManager::processInfoGenerationForEntity - Unsupported entity type declaration for key ${tdecl.tkey}`);

            let totalbytesize = 0;
            let layoutmask = "";

            for(let i = 0; i < tdecl.saturatedBFieldInfo.length; ++i) {
                const ftypeinfo = this.generateLayoutInfoForType(tdecl.saturatedBFieldInfo[i].ftype, irasm);

                totalbytesize += ftypeinfo.bytesize;
                layoutmask += ftypeinfo.layoutmask;
            }

            // If the entity has no fields, it should still have a size of 8 bytes and 1 slot
            if(tdecl.saturatedBFieldInfo.length === 0) {
                totalbytesize = 8;
                layoutmask = "0";
            }

            const ptrmask: string | undefined = TypeInfoManager.staticLayoutToPtrMaskConvert(layoutmask); 
            const ttid = this.typeInfoMap.size;

            if(!this.isRecursiveTypeKey(tdecl.tkey, irasm) && this.isSizeOkForValueLayout(totalbytesize)) {
                this.addTypeInfo(tdecl.tkey, new TypeInfo(tdecl.tkey, new IRNominalTypeSignature(tdecl.tkey), ttid, totalbytesize, LayoutTag.Value, ptrmask));
            }
            else {
                this.addTypeInfo(tdecl.tkey, new TypeInfo(tdecl.tkey, new IRNominalTypeSignature(tdecl.tkey), ttid, totalbytesize, LayoutTag.Ref, ptrmask));
            }
        }

        return this.getTypeInfo(tdecl.tkey);
    }

    private processFieldInfoGenerationForEntity(tdecl: IRAbstractEntityTypeDecl, irasm: IRAssembly): void {
        const typeinfo = this.getTypeInfo(tdecl.tkey);

        let slpos = 0;
        for(let i = 0; i < tdecl.saturatedBFieldInfo.length; i++) {
            const fdecl = tdecl.saturatedBFieldInfo[i];
            typeinfo.ftable.push(new FieldOffsetInfo(fdecl.fkey, this.fieldidctr++, new IRNominalTypeSignature(fdecl.containingtype.tkeystr), fdecl.fname, fdecl.ftype, slpos));

            const ftinfo = this.getTypeInfo(fdecl.ftype.tkeystr);
            slpos += ftinfo.slotcount;
        }
    }

    private processInfoGenerationForConcept(tdecl: IRAbstractEntityTypeDecl, irasm: IRAssembly): TypeInfo {
        if(tdecl instanceof IROptionTypeDecl) {
            const oftinfo = this.generateLayoutInfoForType(tdecl.ttype, irasm);

            const ttid = this.typeInfoMap.size;
            let spm = TypeInfoManager.isAllNopMask(oftinfo.layoutmask) ? ("0" + oftinfo.layoutmask) : ("2" + TypeInfoManager.computeValueMaskOfK(oftinfo.bytesize));
            this.addTypeInfo(tdecl.tkey, new TypeInfo(tdecl.tkey, new IRNominalTypeSignature(tdecl.tkey), ttid, oftinfo.bytesize + 8, LayoutTag.Value, TypeInfoManager.staticLayoutToPtrMaskConvert(spm)));
        }
        else {
            assert((tdecl instanceof IRConceptTypeDecl) || (tdecl instanceof IRDatatypeTypeDecl), `TypeInfoManager::processInfoGenerationForConcept - Unsupported concept type declaration for key ${tdecl.tkey}`);

            // If the concept has no subtypes, it should still have a size of 8 bytes
            let maxbytesize = 8;
            let allnops = true;
            const subtypes = irasm.concretesubtypes.get(tdecl.tkey) as IRTypeSignature[];
            for(let i = 0; i < subtypes.length; ++i) {
                const ftypeinfo = this.generateLayoutInfoForType(subtypes[i], irasm);
                maxbytesize = Math.max(maxbytesize, ftypeinfo.bytesize);
                allnops = allnops && TypeInfoManager.isAllNopMask(ftypeinfo.layoutmask)
            }

            const ttid = this.typeInfoMap.size;
            let eptrmask = (allnops ? "0" : "2") + TypeInfoManager.computeValueMaskOfK(maxbytesize / 8);
            this.addTypeInfo(tdecl.tkey, new TypeInfo(tdecl.tkey, new IRNominalTypeSignature(tdecl.tkey), ttid, maxbytesize + 8, LayoutTag.Value, TypeInfoManager.staticLayoutToPtrMaskConvert(eptrmask)));
        }

        return this.getTypeInfo(tdecl.tkey);
    }

    private processInfoGenerationForElist(ttype: IREListTypeSignature, irasm: IRAssembly): TypeInfo {
        const layoutinfo = this.generateLayoutInfoForType(ttype, irasm);

        const ttid = this.typeInfoMap.size;
        this.addTypeInfo(ttype.tkeystr, new TypeInfo(ttype.tkeystr, ttype, ttid, layoutinfo.bytesize, LayoutTag.Value, TypeInfoManager.staticLayoutToPtrMaskConvert(layoutinfo.layoutmask)));

        return this.getTypeInfo(ttype.tkeystr);
    }

    private processInfoGenerationForFormat(ttype: IRFormatTypeSignature, irasm: IRAssembly): TypeInfo {
        const ttid = this.typeInfoMap.size;
        this.addTypeInfo(ttype.tkeystr, new TypeInfo(ttype.tkeystr, ttype, ttid, 8, LayoutTag.Value, undefined));

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
                return this.processInfoGenerationForElist(ttype, irasm);
            }
            else if(ttype instanceof IRDashResultTypeSignature) {
                assert(false, `TypeInfoManager::processInfoGenerationForType - Unsupported dash result type signature for key ${ttype.tkeystr}`);
            }
            else if(ttype instanceof IRFormatTypeSignature) {
                return this.processInfoGenerationForFormat(ttype, irasm);
            }
            else {
                assert(false, `TypeInfoManager::processInfoGenerationForType - Unsupported type signature for key ${ttype.tkeystr}`);
            }
        }
    }

    static generateTypeInfos(irasm: IRAssembly): TypeInfoManager {
        const timgr = new TypeInfoManager();

        //setup the well-known primitive layouts
        timgr.addLayoutInfo("None", new LayoutInfo("None", new IRNominalTypeSignature("None"), 8, "0"));
        timgr.addLayoutInfo("Bool", new LayoutInfo("Bool", new IRNominalTypeSignature("Bool"), 8, "0"));
        timgr.addLayoutInfo("Int", new LayoutInfo("Int", new IRNominalTypeSignature("Int"), 8, "0"));
        timgr.addLayoutInfo("Nat", new LayoutInfo("Nat", new IRNominalTypeSignature("Nat"), 8, "0"));
        timgr.addLayoutInfo("ChkInt", new LayoutInfo("ChkInt", new IRNominalTypeSignature("ChkInt"), 16, "00"));
        timgr.addLayoutInfo("ChkNat", new LayoutInfo("ChkNat", new IRNominalTypeSignature("ChkNat"), 16, "00"));

        timgr.addLayoutInfo("Float", new LayoutInfo("Float", new IRNominalTypeSignature("Float"), 8, "0"));
        
        timgr.addLayoutInfo("CString", new LayoutInfo("CString", new IRNominalTypeSignature("CString"), 16, "30"));
        timgr.addLayoutInfo("String", new LayoutInfo("String", new IRNominalTypeSignature("String"), 16, "40"));

        timgr.addLayoutInfo("ByteBufferEntry", new LayoutInfo("ByteBufferEntry", new IRNominalTypeSignature("ByteBufferEntry"), 512, "1"));
        timgr.addLayoutInfo("ByteBufferBlock", new LayoutInfo("ByteBufferBlock", new IRNominalTypeSignature("ByteBufferBlock"), 512, "1"));
        timgr.addLayoutInfo("ByteBuffer", new LayoutInfo("ByteBuffer", new IRNominalTypeSignature("ByteBuffer"), 24, "200"));

        timgr.addLayoutInfo("UUIDV4", new LayoutInfo("UUIDV4", new IRNominalTypeSignature("UUIDV4"), 16, "00"));
        timgr.addLayoutInfo("UUIDV7", new LayoutInfo("UUIDV7", new IRNominalTypeSignature("UUIDV7"), 16, "00"));

        timgr.addLayoutInfo("CRegex", new LayoutInfo("CRegex", new IRNominalTypeSignature("CRegex"), 8, "0"));
        timgr.addLayoutInfo("Regex", new LayoutInfo("Regex", new IRNominalTypeSignature("Regex"), 8, "0"));

        //TODO: more primitive types

        for(let i = 0; i < irasm.enums.length; ++i) {
            const etdecl = irasm.enums[i];
            const etkey = TransformCPPNameManager.convertTypeKey(etdecl.tkey);
            timgr.addLayoutInfo(etdecl.tkey, new LayoutInfo(etkey, new IRNominalTypeSignature(etkey), 8, "0"));
        }

        for(let i = 0; i < irasm.typedecls.length; ++i) {
            const tdecl = irasm.typedecls[i];
            const ttkey = TransformCPPNameManager.convertTypeKey(tdecl.tkey);
            const utypeinfo = timgr.getLayoutInfo(TransformCPPNameManager.convertTypeKey(tdecl.valuetype.tkeystr));
            timgr.addLayoutInfo(tdecl.tkey, new LayoutInfo(ttkey, new IRNominalTypeSignature(ttkey), utypeinfo.bytesize, utypeinfo.layoutmask));
        }

        const cstringlayoutinfo = timgr.getLayoutInfo("CString");
        for(let i = 0; i < irasm.cstringoftypedecls.length; ++i) {
            const tdecl = irasm.cstringoftypedecls[i];
            const ttkey = TransformCPPNameManager.convertTypeKey(tdecl.tkey);
            timgr.addLayoutInfo(tdecl.tkey, new LayoutInfo(ttkey, new IRNominalTypeSignature(ttkey), cstringlayoutinfo.bytesize, cstringlayoutinfo.layoutmask));
        }

        const stringlayoutinfo = timgr.getLayoutInfo("String");
        for(let i = 0; i < irasm.stringoftypedecls.length; ++i) {
            const tdecl = irasm.stringoftypedecls[i];
            const ttkey = TransformCPPNameManager.convertTypeKey(tdecl.tkey);
            timgr.addLayoutInfo(tdecl.tkey, new LayoutInfo(ttkey, new IRNominalTypeSignature(ttkey), stringlayoutinfo.bytesize, stringlayoutinfo.layoutmask));
        }

        //setup the well-known primitive types
        timgr.addTypeInfo("None", new TypeInfo("None", new IRNominalTypeSignature("None"), 0, 8, LayoutTag.Value, undefined));
        timgr.addTypeInfo("Bool", new TypeInfo("Bool", new IRNominalTypeSignature("Bool"), 1, 8, LayoutTag.Value, undefined));
        timgr.addTypeInfo("Int", new TypeInfo("Int", new IRNominalTypeSignature("Int"), 2, 8, LayoutTag.Value, undefined));
        timgr.addTypeInfo("Nat", new TypeInfo("Nat", new IRNominalTypeSignature("Nat"), 3, 8, LayoutTag.Value, undefined));
        timgr.addTypeInfo("ChkInt", new TypeInfo("ChkInt", new IRNominalTypeSignature("ChkInt"), 4, 16, LayoutTag.Value, undefined));
        timgr.addTypeInfo("ChkNat", new TypeInfo("ChkNat", new IRNominalTypeSignature("ChkNat"), 5, 16, LayoutTag.Value, undefined));

        timgr.addTypeInfo("Float", new TypeInfo("Float", new IRNominalTypeSignature("Float"), 6, 8, LayoutTag.Value, undefined));
        
        //Add placeholders for the implicitly generated list types -- use dummy values for mask here since we just need to know they exist -- list emitter will handle the rest
        timgr.addTypeInfo("PosRBTreeLeaf_CString", new TypeInfo("PosRBTreeLeaf_CString", new IRNominalTypeSignature("PosRBTreeLeaf_CString"), 7, 40, LayoutTag.Ref, undefined));
        timgr.addTypeInfo("PosRBTreeNode_CString", new TypeInfo("PosRBTreeNode_CString", new IRNominalTypeSignature("PosRBTreeNode_CString"), 8, 64, LayoutTag.Ref, undefined));
        timgr.addTypeInfo("PosRBTree_CString", new TypeInfo("PosRBTree_CString", new IRNominalTypeSignature("PosRBTree_CString"), 9, 8, LayoutTag.Ref, undefined));
        timgr.addTypeInfo("CStringInline", new TypeInfo("CStringInline", new IRNominalTypeSignature("CStringInline"), 10, 16, LayoutTag.Value, undefined));
        timgr.addTypeInfo("CStringTree", new TypeInfo("CStringTree", new IRNominalTypeSignature("CStringTree"), 11, 16, LayoutTag.Value, undefined));
        
        timgr.addTypeInfo("CString", new TypeInfo("CString", new IRNominalTypeSignature("CString"), 12, 16, LayoutTag.Value, "30"));

        //Add placeholders for the implicitly generated list types -- use dummy values for mask here since we just need to know they exist -- list emitter will handle the rest
        timgr.addTypeInfo("PosRBTreeLeaf_String", new TypeInfo("PosRBTreeLeaf_String", new IRNominalTypeSignature("PosRBTreeLeaf_String"), 13, 40, LayoutTag.Ref, undefined));
        timgr.addTypeInfo("PosRBTreeNode_String", new TypeInfo("PosRBTreeNode_String", new IRNominalTypeSignature("PosRBTreeNode_String"), 14, 64, LayoutTag.Ref, undefined));
        timgr.addTypeInfo("PosRBTree_String", new TypeInfo("PosRBTree_String", new IRNominalTypeSignature("PosRBTree_String"), 15, 8, LayoutTag.Ref, undefined));
        timgr.addTypeInfo("StringInline", new TypeInfo("StringInline", new IRNominalTypeSignature("StringInline"), 16, 32, LayoutTag.Value, undefined));
        timgr.addTypeInfo("StringTree", new TypeInfo("StringTree", new IRNominalTypeSignature("StringTree"), 17, 16, LayoutTag.Value, undefined));
        
        timgr.addTypeInfo("String", new TypeInfo("String", new IRNominalTypeSignature("String"), 18, 16, LayoutTag.Value, "40"));

        timgr.addTypeInfo("ByteBufferEntry", new TypeInfo("ByteBufferEntry", new IRNominalTypeSignature("ByteBufferEntry"), 19, 512, LayoutTag.Ref, undefined));
        timgr.addTypeInfo("ByteBufferBlock", new TypeInfo("ByteBufferBlock", new IRNominalTypeSignature("ByteBufferBlock"), 20, 512, LayoutTag.Ref, "1111111111111111111111111111111111111111111111111111111111111111"));
        timgr.addTypeInfo("ByteBuffer", new TypeInfo("ByteBuffer", new IRNominalTypeSignature("ByteBuffer"), 21, 24, LayoutTag.Value, "200"));

        timgr.addTypeInfo("UUIDV4", new TypeInfo("UUIDV4", new IRNominalTypeSignature("UUIDV4"), 22, 16, LayoutTag.Value, undefined));
        timgr.addTypeInfo("UUIDV7", new TypeInfo("UUIDV7", new IRNominalTypeSignature("UUIDV7"), 23, 16, LayoutTag.Value, undefined));

        timgr.addTypeInfo("CRegex", new TypeInfo("CRegex", new IRNominalTypeSignature("CRegex"), 24, 8, LayoutTag.Value, undefined));
        timgr.addTypeInfo("Regex", new TypeInfo("Regex", new IRNominalTypeSignature("Regex"), 25, 8, LayoutTag.Value, undefined));

        //TODO: more primitive types

        for(let i = 0; i < irasm.enums.length; ++i) {
            const etdecl = irasm.enums[i];
            const etkey = TransformCPPNameManager.convertTypeKey(etdecl.tkey);
            const etid = timgr.typeInfoMap.size;
            const enumtd = new TypeInfo(etkey, new IRNominalTypeSignature(etkey), etid, 8, LayoutTag.Value,undefined);

            timgr.addTypeInfo(etdecl.tkey, enumtd);
        }

        for(let i = 0; i < irasm.typedecls.length; ++i) {
            const tdecl = irasm.typedecls[i];
            const ttkey = TransformCPPNameManager.convertTypeKey(tdecl.tkey);
            const ttid = timgr.typeInfoMap.size;

            const utypeinfo = timgr.getTypeInfo(TransformCPPNameManager.convertTypeKey(tdecl.valuetype.tkeystr));
            const typedtd = new TypeInfo(ttkey, new IRNominalTypeSignature(ttkey), ttid, utypeinfo.bytesize, utypeinfo.tag, utypeinfo.ptrmask);
            
            timgr.addTypeInfo(tdecl.tkey, typedtd);
        }

        const cstringtypeinfo = timgr.getTypeInfo("CString");
        for(let i = 0; i < irasm.cstringoftypedecls.length; ++i) {
            const tdecl = irasm.cstringoftypedecls[i];
            const ttkey = TransformCPPNameManager.convertTypeKey(tdecl.tkey);
            const ttid = timgr.typeInfoMap.size;
            const typedtd = new TypeInfo(ttkey, new IRNominalTypeSignature(ttkey), ttid, cstringtypeinfo.bytesize, cstringtypeinfo.tag, cstringtypeinfo.ptrmask);
            
            timgr.addTypeInfo(tdecl.tkey, typedtd);
        }

        const stringtypeinfo = timgr.getTypeInfo("String");
        for(let i = 0; i < irasm.stringoftypedecls.length; ++i) {
            const tdecl = irasm.stringoftypedecls[i];
            const ttkey = TransformCPPNameManager.convertTypeKey(tdecl.tkey);
            const ttid = timgr.typeInfoMap.size;
            const typedtd = new TypeInfo(ttkey, new IRNominalTypeSignature(ttkey), ttid, stringtypeinfo.bytesize, stringtypeinfo.tag, stringtypeinfo.ptrmask);
            
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

        irasm.entities.forEach((tdecl) => { timgr.processFieldInfoGenerationForEntity(tdecl, irasm); });
        irasm.datamembers.forEach((tdecl) => { timgr.processFieldInfoGenerationForEntity(tdecl, irasm); });

        return timgr;
    }
}

export {
    MAX_LIST_INLINE_BYTES, LIST_T_INLINE_CAPACITY, LIST_T_LEAF_CAPACITY,
    VirtualInvokeInfo, FieldOffsetInfo, 
    LayoutTag, TypeInfo,
    TypeInfoManager
};
