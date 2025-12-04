
import { IRLambdaParameterPackTypeSignature, IRTypeSignature } from "../irdefs/irtype.js";
import { TransformCPPNameManager } from "./namemgr";

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
    Value = 0,
    Ref,
    Tagged
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

    emitTypeAsParameter(tkey: string, isconst: boolean): string {
        const typeinfo = this.getTypeInfo(tkey);

        const cspec = (isconst ? "const " : "");
        if(typeinfo.tag === LayoutTag.Ref) {
            return cspec + TransformCPPNameManager.convertTypeKey(tkey) + "*";
        }
        else if(typeinfo.tsig instanceof IRLambdaParameterPackTypeSignature) {
            return "const " + TransformCPPNameManager.convertTypeKey(tkey) + "&";
        }
        else {
            if(typeinfo.bytesize <= TypeInfoManager.c_ref_pass_size) {
                return cspec + TransformCPPNameManager.convertTypeKey(tkey);
            }
            else {
                return "const " + TransformCPPNameManager.convertTypeKey(tkey) + "&";                
            }
        }
    }

    emitTypeAsReturn(tkey: string, isconst: boolean): string {
        const typeinfo = this.getTypeInfo(tkey);

        const cspec = (isconst ? "const " : "");
        if(typeinfo.tag !== LayoutTag.Ref) {
            return cspec + TransformCPPNameManager.convertTypeKey(tkey);
        }
        else {
            return cspec + TransformCPPNameManager.convertTypeKey(tkey) + "*";            
        }
    }

    emitTypeAsMemberField(tkey: string, enclosingtinfo: TypeInfo): string {
        const typeinfo = this.getTypeInfo(tkey);

        const cspec = (enclosingtinfo.tag === LayoutTag.Ref) ? "const " : "";
        const lspec = TransformCPPNameManager.convertTypeKey(tkey);
        
        return `${cspec}${lspec}`;
    }

    emitTypeAsStd(tkey: string, isconst: boolean): string {
        const typeinfo = this.getTypeInfo(tkey);

        const cspec = (isconst ? "const " : "");
        if(typeinfo.tag !== LayoutTag.Ref) {
            return cspec + TransformCPPNameManager.convertTypeKey(tkey);
        }
        else {
            return cspec + TransformCPPNameManager.convertTypeKey(tkey) + "*";            
        }
    }
}

export {
    FieldOffsetInfo, 
    LayoutTag, TypeInfo,
    TypeInfoManager
};
