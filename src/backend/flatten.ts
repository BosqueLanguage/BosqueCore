import { FullyQualifiedNamespace } from "../frontend/type";
import { Expression, ExpressionTag, LiteralCStringExpression, LiteralRegexExpression, LiteralSimpleExpression, LiteralStringExpression } from "../frontend/body";
import { Assembly } from "../frontend/assembly";

import { IRRegex } from "./irsupport";
import {} from "./irassembly";
import { DateRepresentation, DeltaDateRepresentation, DeltaTimeRepresentation, IRExpression, IRLiteralSafeIntExpression, IRLiteralSafeNatExpression, IRLiteralBoolExpression, IRLiteralByteBufferExpression, IRLiteralByteExpression, IRLiteralCCharExpression, IRLiteralComplexExpression, IRLiteralCRegexExpression, IRLiteralCStringExpression, IRLiteralDecimalExpression, IRLiteralDeltaDateTimeExpression, IRLiteralDeltaISOTimeStampExpression, IRLiteralDeltaLogicalTimeExpression, IRLiteralDeltaSecondsExpression, IRLiteralFloatExpression, IRLiteralIntExpression, IRLiteralISOTimeStampExpression, IRLiteralLatLongCoordinateExpression, IRLiteralLogicalTimeExpression, IRLiteralNatExpression, IRLiteralNoneExpression, IRLiteralPlainDateExpression, IRLiteralPlainTimeExpression, IRLiteralRationalExpression, IRLiteralSHAContentHashExpression, IRLiteralStringExpression, IRLiteralTAITimeExpression, IRLiteralTZDateTimeExpression, IRLiteralUnicodeCharExpression, IRLiteralUnicodeRegexExpression, IRLiteralUUIDv4Expression, IRLiteralUUIDv7Expression, IRStatement, TimeRepresentation } from "./irbody";

import assert from "node:assert";

class ASMToIRConverter {
    readonly assembly: Assembly;

    regexs: IRRegex[];
    errCtr: number;

    pendingblocks: IRStatement[][];
    tmpVarCtr: number;

    constructor(assembly: Assembly) {
        this.assembly = assembly;
        
        this.regexs = [];
        this.errCtr = 0;

        this.pendingblocks = [];
        this.tmpVarCtr = 0;
    }

    private static extractLiteralDateInfo(datestr: string): DateRepresentation {
        const y = parseInt(datestr.slice(0, 4), 10);
        const m = parseInt(datestr.slice(5, 7), 10);
        const d = parseInt(datestr.slice(8, 10), 10);

        return new DateRepresentation(y, m, d);
    }

    private static extractLiteralTimeInfo(timestr: string): TimeRepresentation {
        const h = parseInt(timestr.slice(0, 2), 10);
        const m = parseInt(timestr.slice(3, 5), 10);
        const s = parseInt(timestr.slice(6, 8), 10);
        
        return new TimeRepresentation(h, m, s);
    }

    private static extractLiteralDeltaDateInfo(datestr: string): DeltaDateRepresentation {
        const pa = datestr.split("-");
        const y = parseInt(pa[0], 10);
        const m = parseInt(pa[1], 10);
        const d = parseInt(pa[2], 10);

        return new DeltaDateRepresentation(y, m, d);
    }

    private static extractLiteralDeltaTimeInfo(datestr: string): DeltaTimeRepresentation {
        const pa = datestr.split(":");
        const h = parseInt(pa[0], 10);
        const m = parseInt(pa[1], 10);
        const s = parseInt(pa[2], 10);

        return new DeltaTimeRepresentation(h, m, s);
    }

    private processRegex(inns: FullyQualifiedNamespace, regexstr: string): IRRegex {
        const rectr = this.regexs.length;
        
        const inst: IRRegex = xxxx;

        this.regexs.push(inst);
        return inst;
    }

    private flattenExpression(exp: Expression): IRExpression {
        const ttag = exp.tag;

        if(ttag === ExpressionTag.LiteralNoneExpression) {
            return new IRLiteralNoneExpression();
        }
        else if(ttag === ExpressionTag.LiteralBoolExpression) {
            return new IRLiteralBoolExpression((exp as LiteralSimpleExpression).value === "true");
        }
        else if(ttag === ExpressionTag.LiteralNatExpression) {
            return new IRLiteralNatExpression((exp as LiteralSimpleExpression).value.slice(-1));
        }
        else if(ttag === ExpressionTag.LiteralIntExpression) {
            return new IRLiteralIntExpression((exp as LiteralSimpleExpression).value.slice(-1));
        }
        else if(ttag === ExpressionTag.LiteralSafeNatExpression) {
            return new IRLiteralSafeNatExpression((exp as LiteralSimpleExpression).value.slice(-1));
        }
        else if(ttag === ExpressionTag.LiteralSafeIntExpression) {
            return new IRLiteralSafeIntExpression((exp as LiteralSimpleExpression).value.slice(-1));
        }
        else if(ttag === ExpressionTag.LiteralRationalExpression) {
            const rrval = (exp as LiteralSimpleExpression).value;
            const slpos = rrval.indexOf("/");
            
            return new IRLiteralRationalExpression(rrval.slice(0, slpos), rrval.slice(slpos + 1, -1));
        }
        else if(ttag === ExpressionTag.LiteralFloatExpression) {
            return new IRLiteralFloatExpression((exp as LiteralSimpleExpression).value);
        }
        else if(ttag === ExpressionTag.LiteralDecimalExpression) {
            return new IRLiteralDecimalExpression((exp as LiteralSimpleExpression).value);
        }
        else if(ttag === ExpressionTag.LiteralDecimalDegreeExpression) {
            return new IRLiteralDecimalExpression((exp as LiteralSimpleExpression).value.slice(0, -2));
        }
        else if(ttag === ExpressionTag.LiteralLatLongCoordinateExpression) {
            const latsplit = (exp as LiteralSimpleExpression).value.indexOf("lat");
            return new IRLiteralLatLongCoordinateExpression((exp as LiteralSimpleExpression).value.slice(0, latsplit), (exp as LiteralSimpleExpression).value.slice(latsplit + 3, -4));
        }
        else if(ttag === ExpressionTag.LiteralComplexNumberExpression) {
            const cnv = (exp as LiteralSimpleExpression).value;
            let spos = cnv.lastIndexOf("+");
            if(spos === -1) {
                spos = cnv.lastIndexOf("-");
            }

            return new IRLiteralComplexExpression(cnv.slice(0, spos), cnv.slice(spos, -1));
        }
        else if(ttag === ExpressionTag.LiteralByteBufferExpression) {
            const bytes = (exp as LiteralSimpleExpression).value.slice(3, -1).split(",").map((b) => parseInt("0x" + b, 16));
            return new IRLiteralByteBufferExpression(bytes);
        }
        else if(ttag === ExpressionTag.LiteralUUIDv4Expression) {
            const bstring = (exp as LiteralSimpleExpression).value.slice(6, -1).replace(/-/g, "");
            let bytes: number[] = [];
            for(let i = 0; i < bstring.length; i += 2) {
                bytes.push(parseInt("0x" + bstring.slice(i, i + 2), 16));
            }

            return new IRLiteralUUIDv4Expression(bytes);
        }
        else if(ttag === ExpressionTag.LiteralUUIDv7Expression) {
            const bstring = (exp as LiteralSimpleExpression).value.slice(6, -1).replace(/-/g, "");
            let bytes: number[] = [];
            for(let i = 0; i < bstring.length; i += 2) {
                bytes.push(parseInt("0x" + bstring.slice(i, i + 2), 16));
            }

            return new IRLiteralUUIDv7Expression(bytes);
        }
        else if(ttag === ExpressionTag.LiteralSHAContentHashExpression) {
            const bstring = (exp as LiteralSimpleExpression).value.slice(5, -1)
            let bytes: number[] = [];
            for(let i = 0; i < bstring.length; i += 2) {
                bytes.push(parseInt("0x" + bstring.slice(i, i + 2), 16));
            }

            return new IRLiteralSHAContentHashExpression(bytes);
        }
        else if(ttag === ExpressionTag.LiteralTZDateTimeExpression) {
            const dstri = (exp as LiteralSimpleExpression).value.split("T@");
            const datepart = ASMToIRConverter.extractLiteralDateInfo(dstri[0]);
            const timepart = ASMToIRConverter.extractLiteralTimeInfo(dstri[1]);

            return new IRLiteralTZDateTimeExpression(datepart, timepart, dstri[2]);
        }
        else if(ttag === ExpressionTag.LiteralTAITimeExpression) {
            const dstri = (exp as LiteralSimpleExpression).value.split("T");
            const datepart = ASMToIRConverter.extractLiteralDateInfo(dstri[0]);
            const timepart = ASMToIRConverter.extractLiteralTimeInfo(dstri[1]);

            return new IRLiteralTAITimeExpression(datepart, timepart);
        }
        else if(ttag === ExpressionTag.LiteralPlainDateExpression) {
            return new IRLiteralPlainDateExpression(ASMToIRConverter.extractLiteralDateInfo((exp as LiteralSimpleExpression).value));
        }
        else if(ttag === ExpressionTag.LiteralPlainTimeExpression) {
            return new IRLiteralPlainTimeExpression(ASMToIRConverter.extractLiteralTimeInfo((exp as LiteralSimpleExpression).value));
        }
        else if(ttag === ExpressionTag.LiteralLogicalTimeExpression) {
            return new IRLiteralLogicalTimeExpression((exp as LiteralSimpleExpression).value.slice(-2));
        }
        else if(ttag === ExpressionTag.LiteralISOTimeStampExpression) {
            const dstri = (exp as LiteralSimpleExpression).value.slice(0, -1).split("T.");
            const datepart = ASMToIRConverter.extractLiteralDateInfo(dstri[0]);
            const timepart = ASMToIRConverter.extractLiteralTimeInfo(dstri[1]);

            return new IRLiteralISOTimeStampExpression(datepart, timepart, Number.parseInt(dstri[2].slice(0, -1), 10));
        }
        else if(ttag === ExpressionTag.LiteralDeltaDateTimeExpression) {
            const sign = (exp as LiteralSimpleExpression).value[0] as "+" | "-";
            const dstri = (exp as LiteralSimpleExpression).value.slice(1).split("T");
            const deltadatepart = ASMToIRConverter.extractLiteralDeltaDateInfo(dstri[0]);
            const deltatimepart = ASMToIRConverter.extractLiteralDeltaTimeInfo(dstri[1]);
            
            return new IRLiteralDeltaDateTimeExpression(sign, deltadatepart, deltatimepart);
        }
        else if(ttag === ExpressionTag.LiteralDeltaISOTimeStampExpression) {
            const sign = (exp as LiteralSimpleExpression).value[0] as "+" | "-";
            const dstri = (exp as LiteralSimpleExpression).value.slice(1, -1).split("T.");
            const deltadatepart = ASMToIRConverter.extractLiteralDeltaDateInfo(dstri[0]);
            const deltatimepart = ASMToIRConverter.extractLiteralDeltaTimeInfo(dstri[1]);
            const deltamilliseconds = BigInt(dstri[2]);

            return new IRLiteralDeltaISOTimeStampExpression(sign, deltadatepart, deltatimepart, deltamilliseconds);
        }
        else if(ttag === ExpressionTag.LiteralDeltaSecondsExpression) {
            const sign = (exp as LiteralSimpleExpression).value[0] as "+" | "-";
            const seconds = (exp as LiteralSimpleExpression).value.slice(1, -2);

            return new IRLiteralDeltaSecondsExpression(sign, seconds);
        }
        else if(ttag === ExpressionTag.LiteralDeltaLogicalExpression) {
            const sign = (exp as LiteralSimpleExpression).value[0] as "+" | "-";
            const ticks = (exp as LiteralSimpleExpression).value.slice(1, -2);

            return new IRLiteralDeltaLogicalTimeExpression(sign, ticks);
        }
        else if(ttag === ExpressionTag.LiteralUnicodeRegexExpression) {
            const rexp = (exp as LiteralRegexExpression);
            const regexinst = this.processRegex(rexp.inns, rexp.value);

            return new IRLiteralUnicodeRegexExpression(regexinst.regexID, rexp.value);
        }
        else if(ttag === ExpressionTag.LiteralCRegexExpression) {
            const rexp = (exp as LiteralRegexExpression);
            const regexinst = this.processRegex(rexp.inns, rexp.value);

            return new IRLiteralCRegexExpression(regexinst.regexID, rexp.value);
        }
        else if(ttag === ExpressionTag.LiteralByteExpression) {
            const bstr = (exp as LiteralSimpleExpression).value;
            const nval = Number.parseInt(bstr, 16);
            return new IRLiteralByteExpression(nval);
        }
        else if(ttag === ExpressionTag.LiteralCCharExpression) {
            return new IRLiteralCCharExpression(((exp as LiteralSimpleExpression).resolvedValue as string).charCodeAt(0));
        }
        else if(ttag === ExpressionTag.LiteralUnicodeCharExpression) {
            return new IRLiteralUnicodeCharExpression(((exp as LiteralSimpleExpression).resolvedValue as string).charCodeAt(0));
        }
        else if(ttag === ExpressionTag.LiteralCStringExpression) {
            const slexp = exp as LiteralCStringExpression;
            const bbuff = Buffer.from((slexp.resolvedValue as string, "utf8"));
            let bytes: number[] = [];
            for(let i = 0; i < bbuff.length; ++i) {
                bytes.push(bbuff[i]);
            }

            return new IRLiteralCStringExpression(slexp.value, bytes);
        }
        else if(ttag === ExpressionTag.LiteralStringExpression) {
            const slexp = exp as LiteralStringExpression;
            const bbuff = Buffer.from((slexp.resolvedValue as string, "utf8"));
            let bytes: number[] = [];
            for(let i = 0; i < bbuff.length; ++i) {
                bytes.push(bbuff[i]);
            }

            return new IRLiteralStringExpression(slexp.value, bytes);
        }
        else if(ttag === ExpressionTag.LiteralFormatStringExpression) {
            xxxx;
        }
        else if(ttag === ExpressionTag.LiteralFormatCStringExpression) {
            xxxx;
        }
        else {
            assert(false, `ASMToIRConverter: Unsupported expression type -- ${exp.tag}`);
        }
    }
}

export {
    ASMToIRConverter
};
