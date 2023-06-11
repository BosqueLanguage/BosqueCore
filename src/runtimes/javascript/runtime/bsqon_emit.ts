import {Decimal} from "decimal.js";
import Fraction from "fraction.js";

import { List as IList, Map as IMap } from "immutable";

import * as $Constants from "./constants";
import * as $TypeInfo from "./typeinfo";
import * as $Runtime from "./runtime";


class BSQONEmitter {
    readonly m_emitmode: $Runtime.NotationMode;
   
    readonly m_defaultns: string;
    readonly m_importmap: Map<string, string>;

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
        return s;
    }

    private emitASCIIString(s: string): string {
        if (this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            return `ascii{${s}}`;
        }
        else {
            return s;
        }
    }

    private emitByteBuffer(): string {
        let tbval = undefined;
        if(this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            tbval = this.expectTokenAndPop(TokenKind.TOKEN_BYTE_BUFFER).value.slice(3, -1);
        }
        else {
            tbval = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value;
            this.raiseErrorIf(!_s_bytebuffCheckRe.test(tbval), `Expected byte buffer but got ${tbval}`);
        }
    
        return stringInfo.create(tbval, this.lookupMustDefType("ByteBuffer"), undefined, whistory);
    }

    private emitDateTime(): string {
        let dd = undefined;
        if(this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_ISO_DATE_TIME).value;
            dd = generateDateTime(tk);
            this.raiseErrorIf(dd === undefined, `Expected date+time but got ${tk}`);
        }
        else {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value;
            this.raiseErrorIf(!_s_fullTimeCheckRE.test(tk), `Expected date+time but got ${tk}`);
    
            dd = generateDateTime(tk);
            this.raiseErrorIf(dd === undefined, `Expected date+time but got ${tk}`);
        }
    
        return stringInfo.create(dd, this.lookupMustDefType("DateTime"), undefined, whistory);
    }

    private emitUTCDateTime(): string {
        let dd = undefined;
        if(this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_ISO_UTC_DATE_TIME).value;
            dd = generateDateTime(tk);
            this.raiseErrorIf(dd === undefined || dd.tz !== "UTC", `Expected UTC date+time but got ${tk}`);
        }
        else {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value;
            this.raiseErrorIf(!_s_fullTimeUTCCheckRE.test(tk), `Expected UTC date+time but got ${tk}`);
    
            dd = generateDateTime(tk);
            this.raiseErrorIf(dd === undefined || dd.tz !== "UTC", `Expected UTC date+time but got ${tk}`);
        }
    
        return stringInfo.create(dd, this.lookupMustDefType("UTCDateTime"), undefined, whistory);
    }

    private emitPlainDate(): string {
        let dd = undefined;
        if(this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_ISO_DATE).value;
            dd = generateDate(tk);
            this.raiseErrorIf(dd === undefined, `Expected plain date but got ${tk}`);
        }
        else {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value;
            this.raiseErrorIf(!_s_dateOnlyCheckRE.test(tk), `Expected plain date but got ${tk}`);
    
            dd = generateDate(tk);
            this.raiseErrorIf(dd === undefined, `Expected plain date but got ${tk}`);
        }
    
        return stringInfo.create(dd, this.lookupMustDefType("PlainDate"), undefined, whistory);
    }

    private emitPlainTime(): string {
        let dd = undefined;
        if(this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_ISO_TIME).value;
            dd = generateTime(tk);
            this.raiseErrorIf(dd === undefined, `Expected plain time but got ${tk}`);
        }
        else {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value;
            this.raiseErrorIf(!_s_timeOnlyCheckRE.test(tk), `Expected plain time but got ${tk}`);
    
            dd = generateTime(tk);
            this.raiseErrorIf(dd === undefined, `Expected plain time but got ${tk}`);
        }
    
        return stringInfo.create(dd, this.lookupMustDefType("PlainTime"), undefined, whistory);
    }

    private emitTickTime(): string {
        let tt = undefined;
        if(this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            tt = this.expectTokenAndPop(TokenKind.TOKEN_TICK_TIME).value.slice(0, -1);
        }
        else {
            tt = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value;
            this.raiseErrorIf(!_s_tickTimeCheckRE.test(tt), `Expected tick time but got ${tt}`);
        }
    
        return stringInfo.create(BigInt(tt), this.lookupMustDefType("TickTime"), undefined, whistory);
    }

    private emitLogicalTime(): string {
        let tt = undefined;
        if(this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            tt = this.expectTokenAndPop(TokenKind.TOKEN_LOGICAL_TIME).value.slice(0, -1);
        }
        else {
            tt = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value;
            this.raiseErrorIf(!_s_logicalTimeCheckRE.test(tt), `Expected logical time but got ${tt}`);
        }
    
        return stringInfo.create(BigInt(tt), this.lookupMustDefType("LogicalTime"), undefined, whistory);
    }

    private emitISOTimeStamp(): string {
        let dd = undefined;
        if(this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_ISO_TIMESTAMP).value;
            dd = generateDateTime(tk);
            this.raiseErrorIf(dd === undefined || dd.tz !== "UTC", `Expected timestamp but got ${tk}`);
        }
        else {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value;
            this.raiseErrorIf(!_s_isoStampCheckRE.test(tk), `Expected timestamp but got ${tk}`);
    
            dd = generateDateTime(tk);
            this.raiseErrorIf(dd === undefined || dd.tz !== "UTC", `Expected timestamp but got ${tk}`);
        }
    
        return stringInfo.create(dd, this.lookupMustDefType("ISOTimeStamp"), undefined, whistory);
    }

    private emitUUIDv4(): string {
        let uuid = undefined;
        if(this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_UUID).value;
            this.raiseErrorIf(!tk.startsWith("uuid4{"), `Expected UUIDv4 but got ${tk}`);
    
            uuid = tk.slice(6, -1);
        }
        else {
            uuid = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value;
            this.raiseErrorIf(!_s_uuidCheckRE.test(uuid), `Expected UUIDv4 but got ${uuid}`);
        }
    
        return stringInfo.create(uuid, this.lookupMustDefType("UUIDv4"), undefined, whistory);
    }

    private emitUUIDv7(): string {
        let uuid = undefined;
        if(this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const tk = this.expectTokenAndPop(TokenKind.TOKEN_UUID).value;
            this.raiseErrorIf(!tk.startsWith("uuid7{"), `Expected UUIDv7 but got ${tk}`);
    
            uuid = tk.slice(6, -1);
        }
        else {
            uuid = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value;
            this.raiseErrorIf(!_s_uuidCheckRE.test(uuid), `Expected UUIDv7 but got ${uuid}`);
        }
    
        return stringInfo.create(uuid, this.lookupMustDefType("UUIDv7"), undefined, whistory);
    }

    private emitSHAContentHash(): string {
        let sh = undefined;
        if(this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            sh = this.expectTokenAndPop(TokenKind.TOKEN_SHA_HASH).value.slice(5, -1);
        }
        else {
            sh = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value;
            this.raiseErrorIf(!_s_shahashCheckRE.test(sh), `Expected SHA 512 hash but got ${sh}`);
        }
    
        return stringInfo.create(sh, this.lookupMustDefType("SHAContentHash"), undefined, whistory);
    }

    private emitRegex(): string {
        let re = undefined;
        if(this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            re = this.expectTokenAndPop(TokenKind.TOKEN_REGEX).value;
        }
        else {
            re = this.expectTokenAndPop(TokenKind.TOKEN_STRING).value;
            this.raiseErrorIf(!_s_regexCheckRe.test(re), `Expected a regex string but got ${re}`);
        }
    
        return stringInfo.create(re, this.lookupMustDefType("Regex"), undefined, whistory);
    }

    private emitLatLongCoordinate(): string {
        let llc = undefined;
        if (this.m_emitmode !== $Runtime.NotationMode.NOTATION_MODE_JSON) {
            const ttype = this.expectTokenAndPop(TokenKind.TOKEN_TYPE).value;
            this.raiseErrorIf(ttype !== "LatLongCoordinate", `Expected LatLongCoordinate but got ${ttype}`);
    
            this.expectTokenAndPop(TokenKind.TOKEN_LBRACE);
            const lat = this.emitFloat(false);
            this.expectTokenAndPop(TokenKind.TOKEN_COMMA);
            const long = this.emitFloat(false);
            this.expectTokenAndPop(TokenKind.TOKEN_RBRACE);
    
            llc = [lat, long];
        }
        else {
            this.expectTokenAndPop(TokenKind.TOKEN_LBRACKET);
            const lat = this.emitFloat(false);
            this.expectTokenAndPop(TokenKind.TOKEN_COMMA);
            const long = this.emitFloat(false);
            this.expectTokenAndPop(TokenKind.TOKEN_RBRACKET);
    
            llc = [lat, long];
        }

        return stringInfo.create(llc, this.lookupMustDefType("LatLongCoordinate"), undefined, whistory);
    }
}