
import { IRAbstractEntityTypeDecl, IRAbstractNominalTypeDecl, IRAssembly, IRConceptTypeDecl, IRDatatypeTypeDecl, IREntityTypeDecl, IROptionTypeDecl, IRSomeTypeDecl } from "../irdefs/irassembly.js";
import { IRLambdaParameterPackTypeSignature, IRNominalTypeSignature, IRTypeSignature } from "../irdefs/irtype.js";
import { TransformCPPNameManager } from "./namemgr.js";

import assert from "node:assert";

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
        const typeinfo = this.getTypeInfo(tkey);

        if(typeinfo.tag !== LayoutTag.Ref) {
            return TransformCPPNameManager.convertTypeKey(tkey);
        }
        else {
            return TransformCPPNameManager.convertTypeKey(tkey) + "*";            
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

    private static computeValeMaskOfK(k: number): string {
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
                        eptrmask += ftypeinfo.ptrmask || TypeInfoManager.computeValeMaskOfK(ftypeinfo.slotcount);
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
            assert(false, `TypeInfoManager::processInfoGenerationForConcept - Unsupported concept type declaration for key ${tdecl.tkey}`);
        }
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
            assert(false, `TypeInfoManager::processInfoGenerationForType - Unsupported type signature for key ${ttype.tkeystr}`);
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
        
        timgr.addTypeInfo("CStrBuff", new TypeInfo("CStrBuff", new IRNominalTypeSignature("CStrBuff"), 7, 16, 2, LayoutTag.Value, undefined, undefined));
        timgr.addTypeInfo("CStrNode", new TypeInfo("CStrNode", new IRNominalTypeSignature("CStrNode"), 8, 32, 4, LayoutTag.Ref, "0011", undefined));
        timgr.addTypeInfo("CString", new TypeInfo("CString", new IRNominalTypeSignature("CString"), 9, 24, 3, LayoutTag.Tagged, "200", undefined));

        timgr.addTypeInfo("StrBuff", new TypeInfo("StrBuff", new IRNominalTypeSignature("StrBuff"), 10, 32, 4, LayoutTag.Value, undefined, undefined));
        timgr.addTypeInfo("StrNode", new TypeInfo("StrNode", new IRNominalTypeSignature("StrNode"), 11, 32, 4, LayoutTag.Ref, "0011", undefined));
        timgr.addTypeInfo("String", new TypeInfo("String", new IRNominalTypeSignature("CString"), 12, 40, 5, LayoutTag.Tagged, "2000", undefined));

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
    FieldOffsetInfo, 
    LayoutTag, TypeInfo,
    TypeInfoManager
};
