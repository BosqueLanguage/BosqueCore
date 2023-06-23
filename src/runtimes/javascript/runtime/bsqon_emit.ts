import {Decimal} from "npm:decimal.js@10.4.3";
import Fraction from "npm:fraction.js@4.2.0";

import { List as IList, Map as IMap } from "npm:immutable@4.3.0";

import * as $TypeInfo from "./typeinfo.ts";
import * as $Runtime from "./runtime.ts";

class BSQONEmitter {
    readonly m_emitmode: $Runtime.NotationMode;
    readonly m_escapemode: "slash" | "html" | "bsqon";

    readonly m_assembly: $TypeInfo.AssemblyInfo;
    readonly m_defaultns: string;
    readonly m_importmap: {fullns: string, localns: string}[];

    private lookupMustDefType(tname: $TypeInfo.BSQTypeKey): $TypeInfo.BSQType {
        return this.m_assembly.typerefs.get(tname) as $TypeInfo.BSQType;
    }

    constructor(emitmode: $Runtime.NotationMode, escapemode: "slash" | "html" | "bsqon", defaultns: string, importmap: Map<string, string>, assembly: $TypeInfo.AssemblyInfo) {
        this.m_emitmode = emitmode;
        this.m_escapemode = escapemode;

        this.m_assembly = assembly;
        this.m_defaultns = defaultns;

        this.m_importmap = [];
        importmap.forEach((v, k) => {
            this.m_importmap.push({fullns: k, localns: v});
        });
    }

    private escapeString(str: string): string {
        if(this.m_escapemode === "slash") {
            $Runtime.slashEscapeString(str);
        }
        else if(this.m_escapemode === "html") {
            $Runtime.htmlEscapeString(str);
        }
        else {
            return $Runtime.bsqonEscapeString(str);
        }
    }

    private simplifyTypeName(tkey: $TypeInfo.BSQTypeKey): string {
        if(tkey.startsWith(this.m_defaultns)) {
            return tkey.substring(this.m_defaultns.length + "::".length);
        }

        const ins = this.m_importmap.find((im) => tkey.startsWith(im.fullns));
        if(ins !== undefined) {
            return ins.localns + tkey.substring(ins.fullns.length);
        }

        return tkey;
    }

    private emitType(ttype: $TypeInfo.BSQType): string {
        if (ttype instanceof $TypeInfo.UnionType) {
            return ttype.types.map((tt) => this.emitType(this.lookupMustDefType(tt))).join("|");
        }
        else if(ttype instanceof $TypeInfo.ConceptSetType) {
            return ttype.concepts.map((tt) => this.emitType(this.lookupMustDefType(tt))).join("&");
        }
        else if(ttype instanceof $TypeInfo.TupleType) {
            return "[" + ttype.entries.map((tt) => this.emitType(this.lookupMustDefType(tt))).join(", ") + "]";
        }
        else if(ttype instanceof $TypeInfo.RecordType) {
            return "{" + ttype.entries.map((tt) => tt.pname + ": " + this.emitType(this.lookupMustDefType(tt.ptype))).join(", ") + "}";
        }
        else if(ttype instanceof $TypeInfo.StdConceptType) {
            return this.simplifyTypeName(ttype.tkey);
        }
        else if (ttype instanceof $TypeInfo.OptionType) {
            return `Option<${this.emitType(this.lookupMustDefType(ttype.oftype))}>`;
        }
        else if (ttype instanceof $TypeInfo.ResultType) {
            return `Result<${this.emitType(this.lookupMustDefType(ttype.ttype))}, ${this.emitType(this.lookupMustDefType(ttype.etype))}>`;
        }
        else if (ttype instanceof $TypeInfo.StdEntityType) {
            return this.simplifyTypeName(ttype.tkey);
        }
        else if (ttype instanceof $TypeInfo.PrimitiveType) {
            return ttype.tkey;
        }
        else if (ttype instanceof $TypeInfo.EnumType) {
            return this.simplifyTypeName(ttype.tkey);
        }
        else if (ttype instanceof $TypeInfo.TypedeclType) {
            return this.simplifyTypeName(ttype.tkey);
        }
        else if (ttype instanceof $TypeInfo.ValidatorREType) {
            return this.simplifyTypeName(ttype.tkey);
        }
        else if (ttype instanceof $TypeInfo.ValidatorREType) {
            return this.simplifyTypeName(ttype.tkey);
        }
        else if (ttype instanceof $TypeInfo.StringOfType) {
            return `StringOf<${this.emitType(this.lookupMustDefType(ttype.oftype))}>`;
        }
        else if (ttype instanceof $TypeInfo.ASCIIStringOfType) {
            return `ASCIIStringOf<${this.emitType(this.lookupMustDefType(ttype.oftype))}>`;
        }
        else if (ttype instanceof $TypeInfo.SomethingType) {
            return `Something<${this.emitType(this.lookupMustDefType(ttype.oftype))}>`;
        }
        else if (ttype instanceof $TypeInfo.OkType) {
            return `Result<${this.emitType(this.lookupMustDefType(ttype.ttype))}, ${this.emitType(this.lookupMustDefType(ttype.etype))}>::Ok`;
        }
        else if (ttype instanceof $TypeInfo.ErrorType) {
            return `Result<${this.emitType(this.lookupMustDefType(ttype.ttype))}, ${this.emitType(this.lookupMustDefType(ttype.etype))}>::Err`;
        }
        else if (ttype instanceof $TypeInfo.MapEntryType) {
            return `MapEntry<${this.emitType(this.lookupMustDefType(ttype.ktype))}, ${this.emitType(this.lookupMustDefType(ttype.vtype))}>`;
        }
        else if (ttype instanceof $TypeInfo.PathType) {
            return `Path<${this.emitType(this.lookupMustDefType(ttype.oftype))}>`;
        }
        else if (ttype instanceof $TypeInfo.PathFragmentType) {
            return `PathFragment<${this.emitType(this.lookupMustDefType(ttype.oftype))}>`;
        }
        else if (ttype instanceof $TypeInfo.PathGlobType) {
            return `PathGlob<${this.emitType(this.lookupMustDefType(ttype.oftype))}>`;
        }
        else if (ttype instanceof $TypeInfo.ListType) {
            return `List<${this.emitType(this.lookupMustDefType(ttype.oftype))}>`;
        }
        else if (ttype instanceof $TypeInfo.StackType) {
            return `Stack<${this.emitType(this.lookupMustDefType(ttype.oftype))}>`;
        }
        else if (ttype instanceof $TypeInfo.QueueType) {
            return `Queue<${this.emitType(this.lookupMustDefType(ttype.oftype))}>`;
        }
        else if (ttype instanceof $TypeInfo.SetType) {
            return `Set<${this.emitType(this.lookupMustDefType(ttype.oftype))}>`;
        }
        else if (ttype instanceof $TypeInfo.MapType) {
            return `Map<${this.emitType(this.lookupMustDefType(ttype.ktype))}, ${this.emitType(this.lookupMustDefType(ttype.vtype))}>`;
        }
        else {
            return `[Unknown Type: ${ttype.tkey}]`;
        }
    }

    private emitNone(): string {
        if(this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return "none";
        }
        else {
            return "null";
        }
    }

    private emitNothing(): string {
        if(this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return "nothing";
        }
        else {
            return "null";
        }
    }

    private emitBool(b: boolean): string {
        return b ? "true" : "false";
    }
    
    private emitNat(n: number): string {
        return n.toString() + (this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON ? "n" : "");
    }

    private emitInt(i: number): string {
        return i.toString() + (this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON ? "i" : "");
    }

    private emitBigNat(n: bigint): string {
        if(this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return n.toString() + "N";
        }
        else {
            if(n <= BigInt(Number.MAX_SAFE_INTEGER)) {
                return n.toString();
            }
            else {
                return "\"" + n.toString() + "\"";
            }
        }
    }

    private emitBigInt(i: bigint): string {
        if(this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return i.toString() + "I";
        }
        else {
            if(BigInt(Number.MIN_SAFE_INTEGER) <= i && i <= BigInt(Number.MAX_SAFE_INTEGER)) {
                return i.toString();
            }
            else {
                return "\"" + i.toString() + "\"";
            }
        }
    }

    private emitRational(r: Fraction): string {
        if(this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return  `${r.toFraction()}R`;
        }
        else {
            return  `"${r.toFraction()}"`;
        }
    }

    private emitFloat(f: number): string {
        let ff = f.toString();
        if(ff.startsWith(".")) {
            ff = "0" + ff;
        }
        if(ff.indexOf(".") === -1) {
            ff = ff + ".0";
        }

        return ff + (this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON ? "f" : "");
    }

    private emitDecimal(d: Decimal): string {
        let dd = d.toString();
        if(dd.startsWith(".")) {
            dd = "0" + dd;
        }
        if(dd.indexOf(".") === -1) {
            dd = dd + ".0";
        }

        if(this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return dd + "d";
        }
        else {
            return "\"" + dd + "\"";
        }
    }

    private emitString(s: string): string {
        return '"' + this.escapeString(s) + '"';
    }

    private emitASCIIString(s: string): string {
        if (this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return `ascii{"${this.escapeString(s)}"}`;
        }
        else {
            return '"' + this.escapeString(s) + '"';
        }
    }

    private emitByteBuffer(buff: string): string {
        if (this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return `0x${buff}`;
        }
        else {
            return `"${buff}"`;
        }
    }

    private emitDateTime(dt: $Runtime.BSQDateTime): string {
        const dd = `${dt.year.toString().padStart(4, "0")}-${dt.month.toString().padStart(2, "0")}-${dt.day.toString().padStart(2, "0")}`;
        const tt = `${dt.hour.toString().padStart(2, "0")}:${dt.minute.toString().padStart(2, "0")}:${dt.second.toString().padStart(2, "0")}.${dt.millisecond.toString().padStart(3, "0")}`;
        const fdt = `${dd}T${tt}${dt.tz}`;
        
        if(this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return fdt;
        }
        else {
           return "\"" + fdt + "\"";
        }
    }

    private emitUTCDateTime(dt: $Runtime.BSQDateTime): string {
        const dd = `${dt.year.toString().padStart(4, "0")}-${dt.month.toString().padStart(2, "0")}-${dt.day.toString().padStart(2, "0")}`;
        const tt = `${dt.hour.toString().padStart(2, "0")}:${dt.minute.toString().padStart(2, "0")}:${dt.second.toString().padStart(2, "0")}.${dt.millisecond.toString().padStart(3, "0")}`;
        const fdt = `${dd}T${tt}`;
        
        if(this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return fdt;
        }
        else {
           return "\"" + fdt + "\"";
        }
    }

    private emitPlainDate(pd: $Runtime.BSQDate): string {
        const dd = `${pd.year.toString().padStart(4, "0")}-${pd.month.toString().padStart(2, "0")}-${pd.day.toString().padStart(2, "0")}`;
        
        if(this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return dd;
        }
        else {
           return "\"" + dd + "\"";
        }
    }

    private emitPlainTime(pt: $Runtime.BSQTime): string {
        const tt = `${pt.hour.toString().padStart(2, "0")}:${pt.minute.toString().padStart(2, "0")}:${pt.second.toString().padStart(2, "0")}.${pt.millisecond.toString().padStart(3, "0")}`;
        
        if(this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return tt;
        }
        else {
           return "\"" + tt + "\"";
        }
    }

    private emitTickTime(t: bigint): string {
        if(this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return t.toString() + "t";
        }
        else {
            if(t <= BigInt(Number.MAX_SAFE_INTEGER)) {
                return t.toString();
            }
            else {
                return "\"" + t.toString() + "\"";
            }
        }
    }

    private emitLogicalTime(t: bigint): string {
        if(this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return t.toString() + "l";
        }
        else {
            if(t <= BigInt(Number.MAX_SAFE_INTEGER)) {
                return t.toString();
            }
            else {
                return "\"" + t.toString() + "\"";
            }
        }
    }

    private emitISOTimeStamp(ts: $Runtime.BSQDateTime): string {
        const dd = `${ts.year.toString().padStart(4, "0")}-${ts.month.toString().padStart(2, "0")}-${ts.day.toString().padStart(2, "0")}`;
        const tt = `${ts.hour.toString().padStart(2, "0")}:${ts.minute.toString().padStart(2, "0")}:${ts.second.toString().padStart(2, "0")}.${ts.millisecond.toString().padStart(3, "0")}`;
        const fdt = `${dd}T${tt}Z`;
        
        if(this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return fdt;
        }
        else {
           return "\"" + fdt + "\"";
        }
    }

    private emitUUIDv4(u: string): string {
        if(this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return `uuid4{${u}}`;
        }
        else {
            return "\"" + u + "\"";
        }
    }

    private emitUUIDv7(u: string): string {
        if(this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return `uuid7{${u}}`;
        }
        else {
            return "\"" + u + "\"";
        }
    }

    private emitSHAContentHash(h: string): string {
        if(this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return `sha3{${h}}`;
        }
        else {
            return "\"" + h + "\"";
        }
    }

    private emitRegex(re: string): string {
        if(this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return re;
        }
        else {
            return "\"" + re + "\"";
        }    
    }

    private emitLatLongCoordinate(llc: [number, number]): string {
        if (this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return `LatLongCoordinate{${llc[0]}, ${llc[1]}}`;
        }
        else {
            return `[${llc[0]}, ${llc[1]}]`;
        }
    }

    private emitStringOf(ttype: $TypeInfo.StringOfType, str: string): string {
        if (this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return '"' + this.escapeString(str) + '"' + this.emitType(this.lookupMustDefType(ttype.oftype));
        }
        else {
            return '"' + this.escapeString(str) + '"';
        }
    }

    private emitASCIIStringOf(ttype: $TypeInfo.ASCIIStringOfType, str: string): string {
        if (this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return '"' + this.escapeString(str) + '"' + this.emitType(this.lookupMustDefType(ttype.oftype));
        }
        else {
            return '"' + this.escapeString(str) + '"';
        }
    }

    private emitPath(ttype: $TypeInfo.BSQType, str: string): string {
        return "[NOT IMPLEMENTED -- Path]"
    }

    private emitPathFragment(ttype: $TypeInfo.BSQType, str: string): string {
        return "[NOT IMPLEMENTED -- PathFragment]"
    }

    private emitPathGlob(ttype: $TypeInfo.BSQType, str: string): string {
        return "[NOT IMPLEMENTED -- PathGlob]"
    }

    private emitSomething(ttype: $TypeInfo.SomethingType, v: any, fullmode: boolean): string {
        if (this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            if (fullmode || this.m_emitmode === $Runtime.NotationMode.NOTATION_MODE_FULL) {
                return `Something<${this.emitType(this.lookupMustDefType(ttype.oftype))}>(${this.emitValue(this.lookupMustDefType(ttype.oftype), v)})`;
            }
            else {
                return `something(${this.emitValue(this.lookupMustDefType(ttype.oftype), v)})`;
            }
        }
        else {
            return this.emitValue(this.lookupMustDefType(ttype.oftype), v);
        }
    }

    private emitOk(ttype: $TypeInfo.OkType, v: any, fullmode: boolean): string {
        if (this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            if (fullmode || this.m_emitmode === $Runtime.NotationMode.NOTATION_MODE_FULL) {
                return `Result<${this.emitType(this.lookupMustDefType(ttype.ttype))}, ${this.emitType(this.lookupMustDefType(ttype.etype))}>::Ok{${this.emitValue(this.lookupMustDefType(ttype.ttype), v)}}`;
            }
            else {
                return `ok(${this.emitValue(this.lookupMustDefType(ttype.ttype), v)})`;
            }
        }
        else {
            return this.emitValue(this.lookupMustDefType(ttype.ttype), v);
        }
    }

    private emitErr(ttype: $TypeInfo.ErrorType, v: any, fullmode: boolean): string {
        if (this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            if (fullmode || this.m_emitmode === $Runtime.NotationMode.NOTATION_MODE_FULL) {
                return `Result<${this.emitType(this.lookupMustDefType(ttype.ttype))}, ${this.emitType(this.lookupMustDefType(ttype.etype))}>::Err{${this.emitValue(this.lookupMustDefType(ttype.etype), v)}}`;
            }
            else {
                return `err(${this.emitValue(this.lookupMustDefType(ttype.etype), v)})`;
            }
        }
        else {
            return this.emitValue(this.lookupMustDefType(ttype.etype), v);
        }
    }

    private emitMapEntry(ttype: $TypeInfo.MapEntryType, v: [any, any]): string {
        const keytype = this.lookupMustDefType(ttype.ktype);
        const valtype = this.lookupMustDefType(ttype.vtype);

        if(this.m_emitmode === $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return `[${this.emitValue(keytype, v[0])}, ${this.emitValue(valtype, v[1])}]`;
        }
        else {
            return `MapEntry<${this.emitType(keytype)}, ${this.emitType(valtype)}>{${this.emitValue(keytype, v[0])}, ${this.emitValue(valtype, v[1])}}`;
        }
    }

    private emitTuple(ttype: $TypeInfo.TupleType, v: any[], tagged: boolean): string {
        const ttv = "[" + v.map((vv, idx) => this.emitValue(this.lookupMustDefType(ttype.entries[idx]), vv)).join(", ") + "]";
        if(this.m_emitmode === $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return ttv;
        }
        else {
            return tagged ? (`(${this.emitType(ttype)})${ttv}`) : ttv;
        }
    }

    private emitRecord(ttype: $TypeInfo.RecordType, v: {[k: string]: any}, tagged: boolean): string {
        const pkeys = [...Object.keys(v)].sort((a, b) => ((a !== b) ? (a < b ? -1 : 1) : 0));
        const emap = pkeys.map((prop) => {
            const ftype = this.lookupMustDefType(ttype.entries.find((ee) => ee.pname === prop)!.ptype);
            return `${prop}=${this.emitValue(ftype, v[prop])}`;
        });

        const rrv = "{" + emap.join(", ") + "}";
        if(this.m_emitmode === $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return rrv;
        }
        else {
            return tagged ? (`(${this.emitType(ttype)})${rrv}`) : rrv;
        }
    }

    private emitEnum(ttype: $TypeInfo.EnumType, v: string): string {
        const rtn = this.emitType(ttype);
        const eev = v.slice(v.indexOf(rtn));

        if(this.m_emitmode === $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return "\"" + eev + "\"";
        }
        else {
            return eev;
        }
    }
    
    private emitTypedecl(ttype: $TypeInfo.TypedeclType, v: any): string {
        const rval = this.emitValue(this.lookupMustDefType(ttype.basetype), v);

        if(this.m_emitmode === $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return rval;
        }
        else {
            return `${rval}_${this.emitType(ttype)}`;
        }
    }

    private emitStdEntity(ttype: $TypeInfo.StdEntityType, v: {[k: string]: any}): string {
        const emap = ttype.fields.map((ff) => {
            const ftype = this.lookupMustDefType(ff.ftype);
            if(this.m_emitmode === $Runtime.NotationMode.NOTATION_MODE_JSON) {
                return `${ff.fname}: ${this.emitValue(ftype, v[ff.fname])}`;
            }
            else {
                return this.emitValue(ftype, v[ff.fname]);
            }
        });

        const rrv = "{" + emap.join(", ") + "}";
        if(this.m_emitmode === $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return rrv;
        }
        else {
            return `${this.emitType(ttype)}${rrv}`;
        }
    }

    private emitList(ttype: $TypeInfo.ListType, v: IList<any>, tagged: boolean): string {
        if(this.m_emitmode === $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const ltv = "[" + v.map((vv) => this.emitValue(this.lookupMustDefType(ttype.oftype), vv)).join(", ") + "]";
            return ltv;
        }
        else {
            const ltv = "{" + v.map((vv) => this.emitValue(this.lookupMustDefType(ttype.oftype), vv)).join(", ") + "}";
            return (tagged ? this.emitType(ttype) : "List") + ltv;
        }
    }

    private emitStack(ttype: $TypeInfo.StackType, v: IList<any>, tagged: boolean): string {
        return "[Not implemented -- emitStack]";
    }

    private emitQueue(ttype: $TypeInfo.QueueType, v: IList<any>, tagged: boolean): string {
        return "[Not implemented -- emitQueue]";
    }

    private emitSet(ttype: $TypeInfo.SetType, v: IList<any>, tagged: boolean): string {
        return "[Not implemented -- emitSet]";
    }

    private emitMap(ttype: $TypeInfo.MapType, v: IMap<any, any>, tagged: boolean): string {
        const ktype = this.lookupMustDefType(ttype.ktype);
        const vtype = this.lookupMustDefType(ttype.vtype);

        if(this.m_emitmode === $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const ltv = "[" + v.entrySeq().toList().map((vv) => `[${this.emitValue(ktype, vv[0])}, ${this.emitValue(vtype, vv[1])}]`).join(", ") + "]";
            return ltv;
        }
        else {
            const ltv = "{" + v.entrySeq().toList().map((vv) => `${this.emitValue(ktype, vv[0])} => ${this.emitValue(vtype, vv[1])}`).join(", ") + "}";
            return (tagged ? this.emitType(ttype) : "Map") + ltv;
        }
    }

    private emitValuePrimitive(ttype: $TypeInfo.PrimitiveType, v: any): string {
        if(ttype.tkey === "None") {
            return this.emitNone();
        }
        else if(ttype.tkey === "Nothing") {
            return this.emitNothing();
        }
        else if(ttype.tkey === "Bool") {
            return this.emitBool(v as boolean);
        }
        else if(ttype.tkey === "Int") {
            return this.emitInt(v as number);
        }
        else if(ttype.tkey === "Nat") {
            return this.emitNat(v as number);
        }
        else if(ttype.tkey === "BigInt") {
            return this.emitBigInt(v as bigint);
        }
        else if(ttype.tkey === "BigNat") {
            return this.emitBigNat(v as bigint);
        }
        else if(ttype.tkey === "Rational") {
            return this.emitRational(v as Fraction);
        }
        else if(ttype.tkey === "Float") {
            return this.emitFloat(v as number);
        }
        else if(ttype.tkey === "Decimal") {
            return this.emitDecimal(v as Decimal);
        }
        else if(ttype.tkey === "String") {
            return this.emitString(v as string);
        }
        else if(ttype.tkey === "ASCIIString") {
            return this.emitASCIIString(v as string);
        }
        else if(ttype.tkey === "ByteBuffer") {
            return this.emitByteBuffer(v as string);
        }
        else if(ttype.tkey === "DateTime") {
            return this.emitDateTime(v as $Runtime.BSQDateTime);
        }
        else if(ttype.tkey === "UTCDateTime") {
            return this.emitUTCDateTime(v as $Runtime.BSQDateTime);
        }
        else if(ttype.tkey === "PlainDate") {
            return this.emitPlainDate(v as $Runtime.BSQDate);
        }
        else if(ttype.tkey === "PlainTime") {
            return this.emitPlainTime(v as $Runtime.BSQTime);
        }
        else if(ttype.tkey === "TickTime") {
            return this.emitTickTime(v as bigint);
        }
        else if(ttype.tkey === "LogicalTime") {
            return this.emitLogicalTime(v as bigint);
        }
        else if(ttype.tkey === "ISOTimeStamp") {
            return this.emitISOTimeStamp(v as $Runtime.BSQDateTime);
        }
        else if(ttype.tkey === "UUIDv4") {
            return this.emitUUIDv4(v as string);
        }
        else if(ttype.tkey === "UUIDv7") {
            return this.emitUUIDv7(v as string);
        }
        else if(ttype.tkey === "SHAContentHash") {
            return this.emitSHAContentHash(v as string);
        } 
        else if(ttype.tkey === "LatLongCoordinate") {
            return this.emitLatLongCoordinate(v as [number, number]);
        }
        else if(ttype.tkey === "Regex") {
            return this.emitRegex(v as string);
        }
        else {
            return `[Unknown primitive type to emit ${ttype.tkey}]`;
        }
    }

    private emitValueDirect(ttype: $TypeInfo.BSQType, v: any, tagged: boolean): string {
        if(ttype instanceof $TypeInfo.TupleType) {
            return this.emitTuple(ttype, v as any[], false);
        }
        else if(ttype instanceof $TypeInfo.RecordType) {
            return this.emitRecord(ttype, v as {[k: string]: any}, tagged);
        }
        else if(ttype instanceof $TypeInfo.StdEntityType) {
            return this.emitStdEntity(ttype, v as {[k: string]: any});
        }
        else if(ttype instanceof $TypeInfo.EnumType) {
            return this.emitEnum(ttype, v as string);
        }
        else if(ttype instanceof $TypeInfo.TypedeclType) {
            return this.emitTypedecl(ttype, v);
        }
        else if(ttype instanceof $TypeInfo.StringOfType) {
            return this.emitStringOf(ttype, v as string);
        }
        else if(ttype instanceof $TypeInfo.ASCIIStringOfType) {
            return this.emitASCIIStringOf(ttype, v as string);
        }
        else if(ttype instanceof $TypeInfo.SomethingType) {
            return this.emitSomething(ttype, v as string, tagged);
        }
        else if(ttype instanceof $TypeInfo.OkType) {
            return this.emitOk(ttype, v, tagged);
        }
        else if(ttype instanceof $TypeInfo.ErrorType) {
            return this.emitErr(ttype, v, tagged);
        }
        else if(ttype instanceof $TypeInfo.PathType) {
            return this.emitPath(ttype, v as string);
        }
        else if(ttype instanceof $TypeInfo.PathFragmentType) {
            return this.emitPathFragment(ttype, v as string);
        }
        else if(ttype instanceof $TypeInfo.PathGlobType) {
            return this.emitPathGlob(ttype, v as string);
        }
        else if(ttype instanceof $TypeInfo.ListType) {
            return this.emitList(ttype, v as IList<any>, tagged);
        }
        else if(ttype instanceof $TypeInfo.StackType) {
            return this.emitStack(ttype, v as IList<any>, tagged);
        }
        else if(ttype instanceof $TypeInfo.QueueType) {
            return this.emitQueue(ttype, v as IList<any>, tagged);
        }
        else if(ttype instanceof $TypeInfo.SetType) {
            return this.emitSet(ttype, v as IList<any>, tagged);
        }
        else if(ttype instanceof $TypeInfo.MapEntryType) {
            return this.emitMapEntry(ttype, v as [any, any]);
        }
        else if(ttype instanceof $TypeInfo.MapType) {
            return this.emitMap(ttype, v as IMap<any, any>, tagged);
        }
        else {
            return `[Unknown type to emit ${ttype.tkey}]`;
        }
    }

    private emitValueConcept(ttype: $TypeInfo.ConceptType | $TypeInfo.ConceptSetType, v: $Runtime.UnionValue): string {
        if (this.m_emitmode === $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return `[\"${this.emitType(this.lookupMustDefType(v.tkey))}\", ${this.emitValue(this.lookupMustDefType(v.tkey), v.value)}]`;
        }
        else {
            const rtt = this.lookupMustDefType(v.tkey);

            if (ttype instanceof $TypeInfo.OptionType) {
                if (v.value === undefined) {
                    return this.emitNothing();
                }
                else {
                    return this.emitSomething(rtt as $TypeInfo.OptionType, v.value, false);
                }
            }
            else if (ttype instanceof $TypeInfo.ResultType) {
                if(rtt instanceof $TypeInfo.OkType) {
                    return this.emitOk(rtt, v.value, false);
                }
                else {
                    return this.emitErr(rtt as $TypeInfo.ErrorType, v.value, false);
                }
            }
            else if (ttype instanceof $TypeInfo.StdConceptType) {
                return this.emitStdEntity(rtt as $TypeInfo.StdEntityType, v.value);
            }
            else if (ttype instanceof $TypeInfo.ConceptSetType) {
                return this.emitStdEntity(rtt as $TypeInfo.StdEntityType, v.value);
            }
            else {
                return `[Unknown concept type to emit ${ttype.tkey}]`;
            }
        }
    }

    private emitValueUnion(ttype: $TypeInfo.UnionType, v: $Runtime.UnionValue): string {
        //everyone has a none special format option
        if (this.m_emitmode === $Runtime.NotationMode.NOTATION_MODE_JSON) {
            if (v.value === null) {
                return this.emitNone();
            }
            else {
                return `[\"${this.emitType(this.lookupMustDefType(v.tkey))}\", ${this.emitValue(this.lookupMustDefType(v.tkey), v.value)}]`;
            }
        }
        else {
            if (v.value === null) {
                return this.emitNone();
            }

            const rtt = this.lookupMustDefType(v.tkey);
            if(rtt instanceof $TypeInfo.PrimitiveType) {
                return this.emitValuePrimitive(rtt, v.value);
            }
            else {
                const tagged = (ttype.types.length !== 2 || !ttype.types.includes("None"));
                return this.emitValueDirect(rtt, v.value, tagged);
            }
        }
    }

    private emitValue(ttype: $TypeInfo.BSQType, v: any): string {
        if (ttype instanceof $TypeInfo.PrimitiveType) {
            return this.emitValuePrimitive(ttype, v);
        }
        else if ((ttype instanceof $TypeInfo.ConceptType) || (ttype instanceof $TypeInfo.ConceptSetType)) {
            return this.emitValueConcept(ttype, v);
        }
        else if (ttype instanceof $TypeInfo.UnionType) {
            return this.emitValueUnion(ttype, v);
        }
        else {
            return this.emitValueDirect(ttype, v, false);
        }
    }

    static emit(v: any, ttype: $TypeInfo.BSQTypeKey, defaultns: string, importmap: Map<string, string>, assembly: $TypeInfo.AssemblyInfo, mode: $Runtime.NotationMode, escapemode: "slash" | "html"): string {
        const emitter = new BSQONEmitter(mode, escapemode, defaultns, importmap, assembly);
        const result = emitter.emitValue(emitter.lookupMustDefType(ttype), v);

        return result;
    }

    static emitStd(v: any, ttype: $TypeInfo.BSQTypeKey, defaultns: string, assembly: $TypeInfo.AssemblyInfo): string {
        const emitter = new BSQONEmitter($Runtime.NotationMode.NOTATION_MODE_DEFAULT, "bsqon", defaultns, new Map<string, string>(), assembly);
        const result = emitter.emitValue(emitter.lookupMustDefType(ttype), v);

        return result;
    }
}

export {
    BSQONEmitter
}
