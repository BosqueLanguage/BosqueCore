import {Decimal} from "decimal.js";
import Fraction from "fraction.js";

import { List as IList, Map as IMap } from "immutable";

import * as $Constants from "./constants";
import * as $TypeInfo from "./typeinfo";
import * as $Runtime from "./runtime";


class BSQONEmitter {
    readonly m_emitmode: $Runtime.NotationMode;
   
    readonly m_assembly: $TypeInfo.AssemblyInfo;
    readonly m_defaultns: string;
    readonly m_importmap: Map<string, string>;

    private lookupMustDefType(tname: $TypeInfo.BSQTypeKey): $TypeInfo.BSQType {
        return  this.m_assembly.typerefs.get(tname);
    }

    private emitType(t: $TypeInfo.BSQType): string {
        xxxx;
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
            return  "[TODO]R";
        }
        else {
            return  "\"[TODO RATIONAL]\"";
        }
    }

    private emitFloat(f: number): string {
        return f.toString() + (this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON ? "f" : "");
    }

    private emitDecimal(d: Decimal): string {
        if(this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return d.toString() + "d";
        }
        else {
            return "\"" + d.toString() + "\"";
        }
    }

    private emitString(s: string): string {
        return $Runtime.escapeString(s);
    }

    private emitASCIIString(s: string): string {
        if (this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return `ascii{${$Runtime.escapeString(s)}}`;
        }
        else {
            return $Runtime.unescapeString(s);
        }
    }

    private emitByteBuffer(buff: string): string {
        if (this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return `0x${buff}`;
        }
        else {
            return `\"${buff}\"`;
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
        const tt = `${ts.hour.toString().padStart(2, "0")}:${ts.minute.toString().padStart(2, "0")}:${ts.second.toString().padStart(2, "0")}.${dt.millisecond.toString().padStart(3, "0")}`;
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
            return "\"" + $Runtime.escapeString(str) + "\"" + this.emitType(this.lookupMustDefType(ttype.oftype));
        }
        else {
            return "\"" + $Runtime.escapeString(str) + "\"";
        }
    }

    private emitASCIIStringOf(ttype: $TypeInfo.ASCIIStringOfType, str: string): string {
        if (this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return "\"" + $Runtime.escapeString(str) + "\"" + this.emitType(this.lookupMustDefType(ttype.oftype));
        }
        else {
            return "\"" + $Runtime.escapeString(str) + "\"";
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

    private emitSomething(ttype: $TypeInfo.SomethingType, v: any): string {
        if (this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            if (this.m_emitmode === $Runtime.NotationMode.NOTATION_MODE_FULL) {
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











    private emitValue(ttype: $TypeInfo.BSQType, v: any): string {
        xxxx;
    }
}