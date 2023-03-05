import * as assert from "assert";
import { JS, NFA, Words } from "refa";

class RegexParser {
    readonly currentns: string;
    readonly restr: string;
    pos: number;

    constructor(currentns: string, restr: string) {
        this.currentns = currentns;
        this.restr = restr;
        this.pos = 0;
    }

    private done(): boolean {
        return this.restr.length <= this.pos;
    }

    private isToken(tk: string): boolean {
        return this.restr[this.pos] === tk;
    }

    private token(): string {
        return this.restr[this.pos];
    }

    private advance(dist?: number) {
        this.pos = this.pos + (dist !== undefined ? dist : 1);
    }

    private parseBaseComponent(): RegexComponent | string {
        let res: RegexComponent | string;
        if(this.isToken("(")) {
            this.advance();

            res = this.parseComponent();
            if(!this.isToken(")")) {
                return "Un-matched paren";
            }

            this.advance();
        }
        else if(this.isToken("[")) {
            this.advance();

            const compliment = this.isToken("^")
            if(compliment) {
                this.advance();
            }

            let range: {lb: number, ub: number}[] = [];
            while(!this.isToken("]")) {
                const lb = this.token();
                this.advance();

                if (!this.isToken("-")) {
                    range.push({ lb: lb.codePointAt(0) as number, ub: lb.codePointAt(0) as number });
                }
                else {
                    this.advance();

                    const ub = this.token();
                    this.advance();

                    range.push({ lb: lb.codePointAt(0) as number, ub: ub.codePointAt(0) as number });
                }
            }

            if(!this.isToken("]")) {
                return "Invalid range";
            }
            this.advance();

            return new RegexCharRange(compliment, range);
        }
        else if(this.isToken("$")) {
            this.advance();

            if(!this.isToken("{")) {
                return "Invalid regex const";
            }
            this.advance();

            let fname = "";
            while(!this.isToken("}")) {
                fname += this.token();
                this.advance();
            }

            if(!this.isToken("}")) {
                return "Invalid regex const";
            }
            this.advance();

            let ccpos = fname.indexOf("::");

            let ns = ccpos === -1 ? this.currentns : fname.slice(0, ccpos);
            let ccname = ccpos === -1 ? fname : fname.slice(ccpos + 3);

            return new RegexConstClass(ns, ccname);            
        }
        else {
            res = new RegexLiteral(this.token(), this.token());
            this.advance();
        }

        return res;
    }

    private parseCharClassOrEscapeComponent(): RegexComponent | string {
        if(this.isToken(".")) {
            this.advance();
            return new RegexDotCharClass();
        }
        else if(this.isToken("\\")) {
            this.advance();
            if(this.isToken("\\") || this.isToken("/") 
                || this.isToken(".") || this.isToken("*") || this.isToken("+") || this.isToken("?") || this.isToken("|")
                || this.isToken("(") || this.isToken(")") || this.isToken("[") || this.isToken("]") || this.isToken("{") || this.isToken("}")
                || this.isToken("$")) {
                const cc = this.token();
                this.advance();

                return new RegexLiteral(`\\${cc}`, cc);
            }
            else {
                const cc = this.token();
                this.advance();

                return new RegexLiteral(`\\${cc}`, `\\${cc}`);
            }
        }
        else {
            return this.parseBaseComponent();
        }
    }

    private parseRepeatComponent(): RegexComponent | string {
        let rcc = this.parseCharClassOrEscapeComponent();
        if(typeof(rcc) === "string") {
            return rcc;
        }

        while(this.isToken("*") || this.isToken("+") || this.isToken("?") || this.isToken("{")) {
            if(this.isToken("*")) {
                rcc = new RegexStarRepeat(rcc);
                this.advance();
            }
            else if(this.isToken("+")) {
                rcc = new RegexPlusRepeat(rcc);
                this.advance();
            }
            else if(this.isToken("?")) {
                rcc = new RegexOptional(rcc);
                this.advance();
            }
            else {
                this.advance();
                let nre = new RegExp(/[0-9]+/, "y");
                nre.lastIndex = this.pos;

                const nmin = nre.exec(this.restr);
                if(nmin === null) {
                    return "Invalid number";
                }
                this.advance(nmin[0].length);

                const min = Number.parseInt(nmin[0]);
                let max = min;
                if (this.isToken(",")) {
                    this.advance();
                    nre.lastIndex = this.pos;

                    const nmax = nre.exec(this.restr);
                    if (nmax === null) {
                        return "Invalid number";
                    }
                    this.advance(nmax[0].length);

                    max = Number.parseInt(nmax[0]);
                }

                if(!this.isToken("}")) {
                    return "Un-matched paren";
                }
                this.advance();

                rcc = new RegexRangeRepeat(rcc, min, max);
            }
        }   

        return rcc;
    }

    private parseSequenceComponent(): RegexComponent | string {
        let sre: RegexComponent[] = [];

        while(!this.done() && !this.isToken("|") && !this.isToken(")")) {
            const rpe = this.parseRepeatComponent();
            if(typeof(rpe) === "string") {
                return rpe;
            }

            if(sre.length === 0) {
                sre.push(rpe);
            }
            else {
                const lcc = sre[sre.length - 1];
                if(lcc instanceof RegexLiteral && rpe instanceof RegexLiteral) {
                    sre[sre.length - 1] = RegexLiteral.mergeLiterals(lcc, rpe);
                }
                else {
                    sre.push(rpe);
                }
            }
        }

        if(sre.length === 0) {
            return "Malformed regex";
        }

        if (sre.length === 1) {
            return sre[0];
        }
        else {
            return new RegexSequence(sre);
        }
    }

    private parseAlternationComponent(): RegexComponent | string {
        const rpei = this.parseSequenceComponent();
        if (typeof (rpei) === "string") {
            return rpei;
        }

        let are: RegexComponent[] = [rpei];

        while (!this.done() && this.isToken("|")) {
            this.advance();
            const rpe = this.parseSequenceComponent();
            if (typeof (rpe) === "string") {
                return rpe;
            }

            are.push(rpe);
        }

        if(are.length === 1) {
            return are[0];
        }
        else {
            return new RegexAlternation(are);
        }
    }

    parseComponent(): RegexComponent | string {
        return this.parseAlternationComponent();
    }
}

class BSQRegex {
    readonly regexstr: string;
    readonly re: RegexComponent;

    constructor(restr: string, re: RegexComponent) {
        this.regexstr = restr;
        this.re = re;
    }

    acceptsString(str: string): boolean {
        const jsre = RegExp(this.re.compileToJS());

        const { expression, maxCharacter } = JS.Parser.fromLiteral(jsre).parse();
	    const nfa = NFA.fromRegex(expression, { maxCharacter });

        return nfa.test(Words.fromStringToUnicode(str));
    }

    static parse(currentns: string, rstr: string): BSQRegex | string {
        const reparser = new RegexParser(currentns, rstr.substring(1, rstr.length - 1));
        const rep = reparser.parseComponent();
       
        if(typeof(rep) === "string") {
            return rep;
        }
        else {
            return new BSQRegex(rstr, rep);
        }
    }

    jemit(): any {
        return { regexstr: this.regexstr, re: this.re.jemit() };
    }

    static jparse(obj: any): BSQRegex {
        return new BSQRegex(obj.regexstr, RegexComponent.jparse(obj.re));
    }
}

abstract class RegexComponent {
    useParens(): boolean {
        return false;
    }

    abstract jemit(): any;

    abstract compileToJS(): string;

    static jparse(obj: any): RegexComponent {
        const tag = obj[0];
        switch (tag) {
            case "RegexLiteral":
                return RegexLiteral.jparse(obj);
            case "RegexCharRange":
                return RegexCharRange.jparse(obj);
            case "RegexDotCharClass":
                return RegexDotCharClass.jparse(obj);
            case "RegexConstRegexClass":
                return RegexConstClass.jparse(obj);
            case "RegexStarRepeat":
                return RegexStarRepeat.jparse(obj);
            case "RegexPlusRepeat":
                return RegexPlusRepeat.jparse(obj);
            case "RegexRangeRepeat":
                return RegexRangeRepeat.jparse(obj);
            case "RegexOptional":
                return RegexOptional.jparse(obj);
            case "RegexAlternation":
                return RegexAlternation.jparse(obj);
            default:
                return RegexSequence.jparse(obj);
        }
    }
}

class RegexLiteral extends RegexComponent {
    readonly restr: string;
    readonly escstr: string;

    constructor(restr: string, escstr: string) {
        super();

        this.restr = restr;
        this.escstr = escstr;
    }

    jemit(): any {
        return ["RegexLiteral", {restr: this.restr, escstr: this.escstr}];
    }

    static jparse(obj: any): RegexComponent {
        return new RegexLiteral(obj[1].restr, obj[1].escstr);
    }

    static mergeLiterals(l1: RegexLiteral, l2: RegexLiteral): RegexLiteral {
        return new RegexLiteral(l1.restr + l2.restr, l1.escstr + l2.escstr);
    }

    compileToJS(): string {
        return this.restr;
    }
}

class RegexCharRange extends RegexComponent {
    readonly compliment: boolean;
    readonly range: {lb: number, ub: number}[];

    constructor(compliment: boolean, range: {lb: number, ub: number}[]) {
        super();

        assert(range.length !== 0);

        this.compliment = compliment;
        this.range = range;
    }

    jemit(): any {
        return ["RegexCharRange", {compliment: this.compliment, range: this.range }];
    }

    static jparse(obj: any): RegexComponent {
        return new RegexCharRange(obj[1].compliment, obj[1].range);
    }

    private static valToSStr(cc: number): string {
        assert(cc >= 9);

        if(cc === 9) {
            return "\\t";
        }
        else if (cc === 10) {
            return "\\n";
        }
        else if (cc === 13) {
            return "\\r";
        }
        else {
            return String.fromCodePoint(cc);
        }
    }

    compileToJS(): string {
        //
        //TODO: probably need to do some escaping here as well
        //
        const rng = this.range.map((rr) => (rr.lb == rr.ub) ? RegexCharRange.valToSStr(rr.lb) : `${RegexCharRange.valToSStr(rr.lb)}-${RegexCharRange.valToSStr(rr.ub)}`);
        return `[${this.compliment ? "^" : ""}${rng.join("")}]`;
    }
}

class RegexDotCharClass extends RegexComponent {
    constructor() {
        super();
    }

    jemit(): any {
        return ["RegexDotCharClass", {}];
    } 

    static jparse(obj: any): RegexComponent {
        return new RegexDotCharClass();
    }

    compileToJS(): string {
        return ".";
    }
}

class RegexConstClass extends RegexComponent {
    readonly ns: string;
    readonly ccname: string;

    constructor(ns: string, ccname: string) {
        super();

        this.ns = ns;
        this.ccname = ccname;
    }

    jemit(): any {
        return ["RegexConstRegexClass", { ns: this.ns, ccname: this.ccname }];
    }

    static jparse(obj: any): RegexComponent {
        return new RegexConstClass(obj[1].ns, obj[1].ccname);
    }

    compileToJS(): string {
        assert(false, `Should be replaced by const ${this.ns}::${this.ccname}`);
        return `${this.ns}::${this.ccname}`;
    }
}

class RegexStarRepeat extends RegexComponent {
    readonly repeat: RegexComponent;

    constructor(repeat: RegexComponent) {
        super();

        this.repeat = repeat;
    }

    jemit(): any {
        return ["RegexStarRepeat", { repeat: this.repeat.jemit() }];
    }

    static jparse(obj: any): RegexComponent {
        return new RegexStarRepeat(RegexComponent.jparse(obj[1].repeat));
    }

    compileToJS(): string {
        return this.repeat.useParens() ? `(${this.repeat.compileToJS()})*` : `${this.repeat.compileToJS()}*`;
    }
}

class RegexPlusRepeat extends RegexComponent {
    readonly repeat: RegexComponent;

    constructor(repeat: RegexComponent) {
        super();

        this.repeat = repeat;
    }

    jemit(): any {
        return ["RegexPlusRepeat", { repeat: this.repeat.jemit() }];
    }

    static jparse(obj: any): RegexComponent {
        return new RegexPlusRepeat(RegexComponent.jparse(obj[1].repeat));
    }

    compileToJS(): string {
        return this.repeat.useParens() ? `(${this.repeat.compileToJS()})+` : `${this.repeat.compileToJS()}+`;
    }
}

class RegexRangeRepeat extends RegexComponent {
    readonly repeat: RegexComponent;
    readonly min: number;
    readonly max: number;

    constructor(repeat: RegexComponent, min: number, max: number) {
        super();

        this.repeat = repeat;
        this.min = min;
        this.max = max;
    }

    jemit(): any {
        return ["RegexRangeRepeat", { repeat: this.repeat.jemit(), min: this.min, max: this.max }];
    }

    static jparse(obj: any): RegexComponent {
        return new RegexRangeRepeat(RegexComponent.jparse(obj[1].repeat), obj[1].min, obj[1].max);
    }

    compileToJS(): string {
        return this.repeat.useParens() ? `(${this.repeat.compileToJS()}){${this.min},${this.max}}` : `${this.repeat.compileToJS()}{${this.min},${this.max}}`;
    }
}

class RegexOptional extends RegexComponent {
    readonly opt: RegexComponent;

    constructor(opt: RegexComponent) {
        super();

        this.opt = opt;
    }

    jemit(): any {
        return ["RegexOptional", { opt: this.opt.jemit() }];
    }

    static jparse(obj: any): RegexComponent {
        return new RegexOptional(RegexComponent.jparse(obj[1].opt));
    }

    compileToJS(): string {
        return this.opt.useParens() ? `(${this.opt.compileToJS()})?` : `${this.opt.compileToJS()}?`;
    }
}

class RegexAlternation extends RegexComponent {
    readonly opts: RegexComponent[];

    constructor(opts: RegexComponent[]) {
        super();

        this.opts = opts;
    }

    useParens(): boolean {
        return true;
    }

    jemit(): any {
        return ["RegexAlternation", { opts: this.opts.map((opt) => opt.jemit()) }];
    }

    static jparse(obj: any): RegexComponent {
        return new RegexAlternation(obj[1].opts.map((opt: any) => RegexComponent.jparse(opt)));
    }

    compileToJS(): string {
        return this.opts.map((opt) => opt.compileToJS()).join("|");
    }
}

class RegexSequence extends RegexComponent {
    readonly elems: RegexComponent[];

    constructor(elems: RegexComponent[]) {
        super();

        this.elems = elems;
    }

    useParens(): boolean {
        return true;
    }

    jemit(): any {
        return ["RegexSequence", { elems: this.elems.map((elem) => elem.jemit()) }];
    }

    static jparse(obj: any): RegexComponent {
        return new RegexSequence(obj[1].elems.map((elem: any) => RegexComponent.jparse(elem)));
    }

    compileToJS(): string {
        return this.elems.map((elem) => elem.compileToJS()).join("");
    }
}

export {
    BSQRegex,
    RegexComponent,
    RegexLiteral, RegexCharRange, RegexDotCharClass, RegexConstClass, RegexStarRepeat, RegexPlusRepeat, RegexRangeRepeat, RegexOptional, RegexAlternation, RegexSequence
};
