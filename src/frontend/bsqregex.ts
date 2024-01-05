import { JS, NFA, Words } from "refa";

const s_escape_names: [number, string][] = [
    [0, "0;"],
    [1, "SOH;"],
    [2, "STX;"],
    [3, "ETX;"],
    [4, "EOT;"],
    [5, "ENQ;"],
    [6, "ACK;"],
    [7, "a;"],
    [8, "b;"],
    [9, "t;"],
    [10, "n;"],
    [11, "v;"],
    [12, "f;"],
    [13, "r;"],
    [14, "SO;"],
    [15, "SI;"],
    [16, "DLE;"],
    [17, "DC1;"],
    [18, "DC2;"],
    [19, "DC3;"],
    [20, "DC4;"],
    [21, "NAK;"],
    [22, "SYN;"],
    [23, "ETB;"],
    [24, "CAN;"],
    [25, "EM;"],
    [26, "SUB;"],
    [27, "e;"],
    [28, "FS;"],
    [29, "GS;"],
    [30, "RS;"],
    [31, "US;"],
    [127, "DEL;"],

    [32, "space;"],
    [33, "bang;"],
    [34, "quote;"],
    [35, "hash;"],
    [36, "dollar;"],
    [37, "%;"],
    [37, "percent;"],
    [38, "amp;"],
    [39, "tick;"],
    [40, "lparen;"],
    [41, "rparen;"],
    [42, "star;"],
    [43, "plus;"],
    [44, "comma;"],
    [45, "dash;"],
    [46, "dot;"],
    [47, "slash;"],
    [58, "colon;"],
    [59, "semicolon;"],
    [60, "langle;"],
    [61, "equal;"],
    [62, "rangle;"],
    [63, "question;"],
    [64, "at;"], 
    [91, "lbracket;"],
    [92, "backslash;"],
    [93, "rbracket;"],
    [94, "caret;"],
    [95, "underscore;"],
    [96, "backtick;"],
    [123, "lbrace;"],
    [124, "pipe;"],
    [125, "rbrace;"],
    [126, "tilde;"]
];

function unescapeRegexDataValue(rstr: string, inliteral: boolean): string | undefined {
    if(rstr.startsWith("%")) {
        let rrstr = rstr.slice(1);
        if(/\d+;/.test(rrstr)) {
            const ccode = Number.parseInt(rrstr.slice(0, rrstr.length - 1), 16);
            if(!Number.isSafeInteger(ccode)) {
                return undefined;
            }
            else {
                return String.fromCharCode(ccode);
            }
        }
        else if(inliteral && rstr === ";") {
            return "\"";
        }
        else {
            const mm = s_escape_names.find((en) => rrstr === en[1]);
            if(mm === undefined) {
                return undefined;
            }
            else {
                return String.fromCharCode(mm[0]);
            }
        }
    }
    else {
        return rstr;
    }
}

function escapeEntryForRegexDataAsBSQON(c: string, inliteral: boolean): string {
    if( c === '%') {
        return "%%;";
    }
    else if(c === "\n") {
        return "%n;";
    }
    else if(c === "\t") {
        return "%t;";
    }
    else if(c === "\r") {
        return "%r;";
    }
    else if(inliteral && c === "\"") {
        return "%;";
    }
    else if(!inliteral && c === "-") {
        return "%;";
    }
    else if(!inliteral && c === "[") {
        return "%lbracket;";
    }
    else if(!inliteral && c === "]") {
        return "%rbracket;";
    }
    else {
        let cp = c.codePointAt(0) as number;
        if(32 <= cp && cp <= 126) {
            return c;
        }
        else {
            return "%" + cp.toString(16) + ";";
        }
    }
}

function escapeEntryForRegexLiteralAsECMAScript(c: string): string {
    if(c === '\\') {
        return "\\\\";
    }
    else if(c === '/') {
        return "\\/";
    }
    else if(c === "\n") {
        return "\\n";
    }
    else if(c === "\t") {
        return "\\t";
    }
    else if(c === "\r") {
        return "\\r";
    }
    else if(c === "^") {
        return "\\^";
    }
    else if(c === "$") {
        return "\\$";
    }
    else if(c === ".") {
        return "\\.";
    }
    else if(c === "*") {
        return "\\*";
    }
    else if(c === "+") {
        return "\\+";
    }
    else if(c === "?") {
        return "\\?";
    }
    else if(c === "(") {
        return "\\(";
    }
    else if(c === ")") {
        return "\\)";
    }
    else if(c === "{") {
        return "\\{";
    }
    else if(c === "}") {
        return "\\}";
    }
    else if(c === "[") {
        return "\\[";
    }
    else if(c === "]") {
        return "\\]";
    }
    else if(c === "|") {
        return "\\|";
    }
    else {
        let cp = c.codePointAt(0) as number;
        if(32 <= cp && cp <= 126) {
            return c;
        }
        else {
            return "\\u{" + cp.toString(16) + "}";
        }
    }
}

function escapeEntryForRegexRangeAsECMAScript(c: string): string {
    let cp = c.codePointAt(0) as number;
        if(cp === 32 || (48 <= cp && cp <= 57) || (65 <= cp && cp <= 90) || (97 <= cp && cp <= 122)) {
            return c;
        }
        else {
            return "\\u{" + cp.toString(16) + "}";
        }
}

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
            let tv = this.token();
            let ccs = Array.from(tv).map((c) =>c.charCodeAt(0));
            res = new RegexLiteral(ccs, this.token(), this.token());

            this.advance();
        }

        return res;
    }

    private parseCharClassOrEscapeComponent(): RegexComponent | string {
        if(this.isToken(".")) {
            this.advance();
            return new RegexDotCharClass();
        }
        else if(this.isToken("%")) {
            let epos = this.restr.indexOf(";", this.pos);
            let estr = this.restr.slice(this.pos, epos + 1);
            this.advance(estr.length);

            let uesi = escapeCharCodeForRegex(estr);
            return new RegexLiteral([uesi.charcode], uesi.bsqonesc, uesi.jsesc);
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

                while(this.isToken(" ")) {
                    this.advance();
                }

                const min = Number.parseInt(nmin[0]);
                let max = min;
                if (this.isToken(",")) {
                    this.advance();

                    while(this.isToken(" ")) {
                        this.advance();
                    }

                    if (!this.isToken("}")) {
                        nre.lastIndex = this.pos;

                        const nmax = nre.exec(this.restr);
                        if (nmax === null) {
                            return "Invalid number";
                        }
                        this.advance(nmax[0].length);

                        max = Number.parseInt(nmax[0]);
                    }
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

    literalemit(): string {
        return this.re.literalemit();
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

    bsqonemit(): string {
        return `TreeIR::BSQRegex{"${escapeString(this.regexstr)}", ${this.re.bsqonemit()}}`;
    }
}

abstract class RegexComponent {
    useParens(): boolean {
        return false;
    }

    abstract literalemit(): string;

    abstract jemit(): any;

    abstract compileToJS(): string;

    static jparse(obj: any): RegexComponent {
        const tag = obj[0];
        switch (tag) {
            case "TreeIR::RegexLiteral":
                return RegexLiteral.jparse(obj);
            case "TreeIR::RegexCharRange":
                return RegexCharRange.jparse(obj);
            case "TreeIR::RegexDotCharClass":
                return RegexDotCharClass.jparse(obj);
            case "TreeIR::RegexConstRegexClass":
                return RegexConstClass.jparse(obj);
            case "TreeIR::RegexStarRepeat":
                return RegexStarRepeat.jparse(obj);
            case "TreeIR::RegexPlusRepeat":
                return RegexPlusRepeat.jparse(obj);
            case "TreeIR::RegexRangeRepeat":
                return RegexRangeRepeat.jparse(obj);
            case "TreeIR::RegexOptional":
                return RegexOptional.jparse(obj);
            case "TreeIR::RegexAlternation":
                return RegexAlternation.jparse(obj);
            default:
                return RegexSequence.jparse(obj);
        }
    }

    abstract bsqonemit(): string;
}

class RegexLiteral extends RegexComponent {
    readonly charcodes: number[];
    readonly bsqonstr: string; //chars or escapes BSQ regxes
    readonly jsstr: string; //chars or escapes for JS regexs

    constructor(charcodes: number[], bsqonstr: string, jsstr: string) {
        super();

        this.charcodes = charcodes;
        this.bsqonstr = bsqonstr;
        this.jsstr = jsstr;
    }

    literalemit(): string {
        return this.bsqonstr;
    }

    jemit(): any {
        return ["TreeIR::RegexLiteral", {restr: this.restr, escstr: this.escstr}];
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

    bsqonemit(): string {
        return `TreeIR::RegexLiteral{"${escapeString(this.restr)}", "${escapeString(this.escstr)}"}`;
    }
}

class RegexCharRange extends RegexComponent {
    readonly compliment: boolean;
    readonly range: {lb: number, ub: number}[];

    constructor(compliment: boolean, range: {lb: number, ub: number}[]) {
        super();

        this.compliment = compliment;
        this.range = range;
    }

    jemit(): any {
        return ["TreeIR::RegexCharRange", {compliment: this.compliment, range: this.range }];
    }

    static jparse(obj: any): RegexComponent {
        return new RegexCharRange(obj[1].compliment, obj[1].range);
    }

    private static valToSStr(cc: number): string {
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

    bsqonemit(): string {
        const rngl = this.range.map((rr) => `{lb=${rr.lb}n, ub=${rr.ub}n}`);
        const rng = `[${rngl.join(", ")}]`;
        return `TreeIR::RegexCharRange{${this.compliment}, ${rng}}`;
    }
}

class RegexDotCharClass extends RegexComponent {
    constructor() {
        super();
    }

    jemit(): any {
        return ["TreeIR::RegexDotCharClass", {}];
    } 

    static jparse(obj: any): RegexComponent {
        return new RegexDotCharClass();
    }

    compileToJS(): string {
        return ".";
    }

    bsqonemit(): string {
        return `TreeIR::RegexDotCharClass{}`;
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
        return ["TreeIR::RegexConstRegexClass", { ns: this.ns, ccname: this.ccname }];
    }

    static jparse(obj: any): RegexComponent {
        return new RegexConstClass(obj[1].ns, obj[1].ccname);
    }

    compileToJS(): string {
        return `${this.ns}::${this.ccname}`;
    }

    bsqonemit(): string {
        return `[NOT SUPPORTED]`;
    }
}

class RegexStarRepeat extends RegexComponent {
    readonly repeat: RegexComponent;

    constructor(repeat: RegexComponent) {
        super();

        this.repeat = repeat;
    }

    jemit(): any {
        return ["TreeIR::RegexStarRepeat", { repeat: this.repeat.jemit() }];
    }

    static jparse(obj: any): RegexComponent {
        return new RegexStarRepeat(RegexComponent.jparse(obj[1].repeat));
    }

    compileToJS(): string {
        return this.repeat.useParens() ? `(${this.repeat.compileToJS()})*` : `${this.repeat.compileToJS()}*`;
    }

    bsqonemit(): string {
        return `TreeIR::RegexStarRepeat{${this.repeat.bsqonemit()}}`;
    }
}

class RegexPlusRepeat extends RegexComponent {
    readonly repeat: RegexComponent;

    constructor(repeat: RegexComponent) {
        super();

        this.repeat = repeat;
    }

    jemit(): any {
        return ["TreeIR::RegexPlusRepeat", { repeat: this.repeat.jemit() }];
    }

    static jparse(obj: any): RegexComponent {
        return new RegexPlusRepeat(RegexComponent.jparse(obj[1].repeat));
    }

    compileToJS(): string {
        return this.repeat.useParens() ? `(${this.repeat.compileToJS()})+` : `${this.repeat.compileToJS()}+`;
    }

    bsqonemit(): string {
        return `TreeIR::RegexPlusRepeat{${this.repeat.bsqonemit()}}`;
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
        return ["TreeIR::RegexRangeRepeat", { repeat: this.repeat.jemit(), min: this.min, max: this.max }];
    }

    static jparse(obj: any): RegexComponent {
        return new RegexRangeRepeat(RegexComponent.jparse(obj[1].repeat), obj[1].min, obj[1].max);
    }

    compileToJS(): string {
        return this.repeat.useParens() ? `(${this.repeat.compileToJS()}){${this.min},${this.max}}` : `${this.repeat.compileToJS()}{${this.min},${this.max}}`;
    }

    bsqonemit(): string {
        return `TreeIR::RegexRangeRepeat{${this.repeat.bsqonemit()}, ${this.min}n, ${this.max}n}`;
    }
}

class RegexOptional extends RegexComponent {
    readonly opt: RegexComponent;

    constructor(opt: RegexComponent) {
        super();

        this.opt = opt;
    }

    jemit(): any {
        return ["TreeIR::RegexOptional", { opt: this.opt.jemit() }];
    }

    static jparse(obj: any): RegexComponent {
        return new RegexOptional(RegexComponent.jparse(obj[1].opt));
    }

    compileToJS(): string {
        return this.opt.useParens() ? `(${this.opt.compileToJS()})?` : `${this.opt.compileToJS()}?`;
    }

    bsqonemit(): string {
        return `TreeIR::RegexOptional{${this.opt.bsqonemit()}`;
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
        return ["TreeIR::RegexAlternation", { opts: this.opts.map((opt) => opt.jemit()) }];
    }

    static jparse(obj: any): RegexComponent {
        return new RegexAlternation(obj[1].opts.map((opt: any) => RegexComponent.jparse(opt)));
    }

    compileToJS(): string {
        return this.opts.map((opt) => opt.compileToJS()).join("|");
    }

    bsqonemit(): string {
        return `TreeIR::RegexAlternation{${this.opts.map((opt) => opt.bsqonemit()).join(", ")}}`;
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
        return ["TreeIR::RegexSequence", { elems: this.elems.map((elem) => elem.jemit()) }];
    }

    static jparse(obj: any): RegexComponent {
        return new RegexSequence(obj[1].elems.map((elem: any) => RegexComponent.jparse(elem)));
    }

    compileToJS(): string {
        return this.elems.map((elem) => elem.compileToJS()).join("");
    }

    bsqonemit(): string {
        return `TreeIR::RegexSequence{${this.elems.map((elem) => elem.bsqonemit()).join(", ")}}`;
    }
}

export {
    BSQRegex,
    RegexComponent,
    RegexLiteral, RegexCharRange, RegexDotCharClass, RegexConstClass, RegexStarRepeat, RegexPlusRepeat, RegexRangeRepeat, RegexOptional, RegexAlternation, RegexSequence
};
