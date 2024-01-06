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

function unescapeRegexDataValue(rstr: string, inliteral: boolean): [number, string] | undefined {
    let rrstr = rstr.slice(1);
    if (/\d+;/.test(rrstr)) {
        const ccode = Number.parseInt(rrstr.slice(0, rrstr.length - 1), 16);
        if (!Number.isSafeInteger(ccode)) {
            return undefined;
        }
        else {
            return [ccode, String.fromCharCode(ccode)];
        }
    }
    else if (inliteral && rstr === ";") {
        return [34, "\""];
    }
    else {
        const mm = s_escape_names.find((en) => rrstr === en[1]);
        if (mm === undefined) {
            return undefined;
        }
        else {
            return [mm[0], String.fromCharCode(mm[0])];
        }
    }
}

function escapeEntryForRegexLiteralAsBSQON(c: string): string {
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
    else if(c === "\"") {
        return "%;";
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

function escapeEntryForRegexRangeAsBSQON(c: string): string {
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
    else if(c === "-") {
        return "%;";
    }
    else if(c === "[") {
        return "%lbracket;";
    }
    else if(c === "]") {
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

function escapeEntryForRegexRangeAsECMAScript(cp: number): string {
    if (cp === 32 || (48 <= cp && cp <= 57) || (65 <= cp && cp <= 90) || (97 <= cp && cp <= 122)) {
        return String.fromCharCode(cp);
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

    private parseLiteral(): RegexLiteral | string {
        let codes: number[] = [];
        let cvals = "";

        this.advance();
        if(this.done()) {
            return "Unclosed regex literal";
        }

        while(!this.isToken("\"")) {
            const c = this.token();
            this.advance();

            if(c !== "%") {
                codes.push(c.codePointAt(0) as number);
                cvals += c;
            }
            else {
                const eepos = this.restr.indexOf(";", this.pos);
                if(eepos === -1) {
                    return "Invalid escape sequence -- missing ;";
                }

                const sstr = this.restr.slice(this.pos, eepos);
                this.advance(sstr.length);

                const usc = unescapeRegexDataValue(sstr, true);
                if(usc === undefined) {
                    return "Invalid escape sequence";
                }

                codes.push(usc[0]);
                cvals += usc[1];
            }
        }

        this.advance();
        return new RegexLiteral(codes, cvals);
    }

    private parseRange(): RegexCharRange | string {
        this.advance();

        const iscompliment = this.isToken("^");
        if(iscompliment) {
            this.advance();
        }

        let range: {lb: [number, string], ub: [number, string]}[] = [];
        while (!this.isToken("]")) {
            const lb = this.token();
            this.advance();

            let lcode: [number, string] = [0, "NUL"];
            if(lb !== "%") {
                lcode = [lb.codePointAt(0) as number, lb];
            }
            else {
                const eepos = this.restr.indexOf(";", this.pos);
                if(eepos === -1) {
                    return "Invalid escape sequence -- missing ;";
                }

                const lcstr = this.restr.slice(this.pos, eepos);
                const lcc = unescapeRegexDataValue(lcstr, false);
                if(lcc === undefined) {
                    return "Invalid escape sequence";
                }

                this.advance(lcstr.length);
                lcode = lcc;
            }

            if (!this.isToken("-")) {
                range.push({ lb: lcode, ub: lcode });
            }
            else {
                this.advance();

                const ub = this.token();
                this.advance();

                let ucode: [number, string] = [0, "NUL"];
                if(ub !== "%") {
                    ucode = [ub.codePointAt(0) as number, ub];
                }
                else {
                    const eepos = this.restr.indexOf(";", this.pos);
                    if (eepos === -1) {
                        return "Invalid escape sequence -- missing ;";
                    }

                    const ucstr = this.restr.slice(this.pos, eepos);
                    const ucc = unescapeRegexDataValue(ucstr, false);
                    if(ucc === undefined) {
                        return "Invalid escape sequence";
                    }
    
                    this.advance(ucstr.length);
                    ucode = ucc;
                }

                range.push({ lb: lcode, ub: ucode });
            }
        }

        if (!this.isToken("]")) {
            return "Invalid range";
        }
        this.advance();

        return new RegexCharRange(iscompliment, range);
    }

    private parseNamedComponent(): RegexConstClass | string {
        this.advance();

        if (!this.isToken("{")) {
            return "Invalid regex const";
        }
        this.advance();

        let fname = "";
        while (!this.isToken("}")) {
            fname += this.token();
            this.advance();
        }

        if (!this.isToken("}")) {
            return "Invalid regex const";
        }
        this.advance();

        let ccpos = fname.indexOf("::");

        let ns = ccpos === -1 ? this.currentns : fname.slice(0, ccpos);
        let ccname = ccpos === -1 ? fname : fname.slice(ccpos + 3);

        return new RegexConstClass(ns, ccname);
    }

    private parseNegatedComponent(): RegexNegatedComponent | string {
        this.advance();

        const cc = this.parseCharClassOrEscapeComponent();
        if(typeof(cc) === "string") {
            return cc;
        }

        return new RegexNegatedComponent(cc);
    }

    private parseBaseComponent(): RegexComponent | string {
        if(this.done()) {
            return "Unexpected end of regex"
        }

        if(this.isToken("(")) {
            this.advance();

            const res = this.parseComponent();
            if(!this.isToken(")")) {
                return "Un-matched paren";
            }
            this.advance();

            return res;
        }
        else if(this.isToken("^")) {
            return this.parseNegatedComponent();
        }
        else if(this.isToken("\"")) {
            return this.parseLiteral();
        }
        else if(this.isToken("[")) {
            return this.parseRange();
        }
        else if(this.isToken("$")) {
            return this.parseNamedComponent();            
        }
        else {
            return `Unknown regex component -- starting with "${this.token()}"`
        }
    }

    private parseCharClassOrEscapeComponent(): RegexComponent | string {
        if(this.isToken(".")) {
            this.advance();
            return new RegexDotCharClass();
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
                let max: number | undefined = min;
                if (this.isToken(",")) {
                    this.advance();

                    while(this.isToken(" ")) {
                        this.advance();
                    }

                    max = undefined;
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
    readonly regexid: string | undefined; //either the scoped key for the regex or undefined if this is a literal
    readonly re: RegexComponent;

    constructor(regexid: string, re: RegexComponent) {
        this.regexid = regexid;
        this.re = re;
    }

    acceptsString(str: string, regexmap: Map<string, BSQRegex>): boolean {
        const jsre = RegExp(this.re.compileToECMA(regexmap));

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
        return { regexid: this.regexid || null, re: this.re.jemit() };
    }

    static jparse(obj: any): BSQRegex {
        return new BSQRegex(obj.regexid || undefined, RegexComponent.jparse(obj.re));
    }

    bsq_emit(): string {
        return `TreeIR::BSQRegex{${this.regexid !== undefined ? ("\"" + this.regexid + "\"") : "none"}, ${this.re.bsqonemit()}}`;
    }

    bsqon_literal_regexemit(): string {
        return this.re.bsqon_literal_emit();
    }
}

abstract class RegexComponent {
    useParens(): boolean {
        return false;
    }

    abstract bsqon_literal_emit(): string;

    abstract jemit(): any;

    abstract compileToECMA(regexmap: Map<string, BSQRegex>): string;

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
            case "TreeIR::RegexNegatedComponent":
                return RegexNegatedComponent.jparse(obj);
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
    readonly literalstr: string;

    constructor(charcodes: number[], literalstr: string) {
        super();

        this.charcodes = charcodes;
        this.literalstr = literalstr;
    }

    bsqon_literal_emit(): string {
        return "\"" + escapeEntryForRegexLiteralAsBSQON(this.literalstr) + "\"";
    }

    jemit(): any {
        return ["TreeIR::RegexLiteral", {charcodes: this.charcodes, literalstr: this.literalstr}];
    }

    static jparse(obj: any): RegexComponent {
        return new RegexLiteral(obj[1].charcodes, obj[1].literalstr);
    }

    compileToECMA(regexmap: Map<string, BSQRegex>): string {
        return escapeEntryForRegexLiteralAsECMAScript(this.literalstr);
    }

    bsqonemit(): string {
        return `TreeIR::RegexLiteral{[${this.charcodes.map((cc) => cc.toString()).join(", ")}], "${escapeEntryForRegexLiteralAsBSQON(this.literalstr)}"}`;
    }
}

class RegexCharRange extends RegexComponent {
    readonly iscompliment: boolean;
    readonly range: {lb: [number, string], ub: [number, string]}[];

    constructor(iscompliment: boolean, range: {lb: [number, string], ub: [number, string]}[]) {
        super();

        this.iscompliment = iscompliment;
        this.range = range;
    }

    bsqon_literal_emit(): string {
        const rng = this.range.map((rr) => (rr.lb[0] == rr.ub[0]) ? escapeEntryForRegexRangeAsBSQON(rr.lb[1]) : `${escapeEntryForRegexRangeAsBSQON(rr.lb[1])}-${escapeEntryForRegexRangeAsBSQON(rr.ub[1])}`);
        return `[${this.iscompliment ? "^" : ""}${rng.join("")}]`;
    }

    jemit(): any {
        return ["TreeIR::RegexCharRange", {iscompliment: this.iscompliment, range: this.range }];
    }

    static jparse(obj: any): RegexComponent {
        return new RegexCharRange(obj[1].iscompliment, obj[1].range);
    }

    compileToECMA(regexmap: Map<string, BSQRegex>): string {
        const rng = this.range.map((rr) => (rr.lb[0] == rr.ub[0]) ? escapeEntryForRegexRangeAsECMAScript(rr.lb[0]) : `${escapeEntryForRegexRangeAsECMAScript(rr.lb[0])}-${escapeEntryForRegexRangeAsECMAScript(rr.ub[0])}`);
        return `[${this.iscompliment ? "^" : ""}${rng.join("")}]`;
    }

    bsqonemit(): string {
        const rngl = this.range.map((rr) => `{lb=[${rr.lb[0]}n, "${rr.lb[1]}"], ub=[${rr.ub[0]}n, "${rr.ub[1]}"]}`);
        const rng = `[${rngl.join(", ")}]`;
        return `TreeIR::RegexCharRange{${rng}}`;
    }
}

class RegexDotCharClass extends RegexComponent {
    constructor() {
        super();
    }

    bsqon_literal_emit(): string {
        return ".";
    }

    jemit(): any {
        return ["TreeIR::RegexDotCharClass", {}];
    } 

    static jparse(obj: any): RegexComponent {
        return new RegexDotCharClass();
    }

    compileToECMA(regexmap: Map<string, BSQRegex>): string {
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

    bsqon_literal_emit(): string {
        return "${" + `${this.ns}::${this.ccname}` + "}" ;
    }

    jemit(): any {
        return ["TreeIR::RegexConstRegexClass", { ns: this.ns, ccname: this.ccname }];
    }

    static jparse(obj: any): RegexComponent {
        return new RegexConstClass(obj[1].ns, obj[1].ccname);
    }

    compileToECMA(regexmap: Map<string, BSQRegex>): string {
        return (regexmap.get(`${this.ns}::${this.ccname}`) as BSQRegex).re.compileToECMA(regexmap);
    }

    bsqonemit(): string {
        return `TreeIR::RegexConstClass{${this.ns}::${this.ccname}}`;
    }
}

class RegexNegatedComponent extends RegexComponent {
    readonly nregex: RegexComponent;

    constructor(nregex: RegexComponent) {
        super();

        this.nregex = nregex;
    }

    bsqon_literal_emit(): string {
        return "^(" + this.nregex.bsqon_literal_emit() + ")";
    }

    jemit(): any {
        return ["TreeIR::RegexNegatedComponent", { nregex: this.nregex.jemit() }];
    }

    static jparse(obj: any): RegexComponent {
        return new RegexNegatedComponent(RegexComponent.jparse(obj[1].nregex));
    }

    compileToECMA(regexmap: Map<string, BSQRegex>): string {
        return "{TODO: -- negation in regex}";
    }

    bsqonemit(): string {
        return `TreeIR::RegexNegatedComponent{${this.nregex.bsqonemit()}}`;
    }
}

class RegexStarRepeat extends RegexComponent {
    readonly repeat: RegexComponent;

    constructor(repeat: RegexComponent) {
        super();

        this.repeat = repeat;
    }

    bsqon_literal_emit(): string {
        return this.repeat.useParens() ? `(${this.repeat.bsqon_literal_emit()})*` : `${this.repeat.bsqon_literal_emit()}*`;
    }

    jemit(): any {
        return ["TreeIR::RegexStarRepeat", { repeat: this.repeat.jemit() }];
    }

    static jparse(obj: any): RegexComponent {
        return new RegexStarRepeat(RegexComponent.jparse(obj[1].repeat));
    }

    compileToECMA(regexmap: Map<string, BSQRegex>): string {
        return this.repeat.useParens() ? `(${this.repeat.compileToECMA(regexmap)})*` : `${this.repeat.compileToECMA(regexmap)}*`;
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

    bsqon_literal_emit(): string {
        return this.repeat.useParens() ? `(${this.repeat.bsqon_literal_emit()})+` : `${this.repeat.bsqon_literal_emit()}+`;
    }

    jemit(): any {
        return ["TreeIR::RegexPlusRepeat", { repeat: this.repeat.jemit() }];
    }

    static jparse(obj: any): RegexComponent {
        return new RegexPlusRepeat(RegexComponent.jparse(obj[1].repeat));
    }

    compileToECMA(regexmap: Map<string, BSQRegex>): string {
        return this.repeat.useParens() ? `(${this.repeat.compileToECMA(regexmap)})+` : `${this.repeat.compileToECMA(regexmap)}+`;
    }

    bsqonemit(): string {
        return `TreeIR::RegexPlusRepeat{${this.repeat.bsqonemit()}}`;
    }
}

class RegexRangeRepeat extends RegexComponent {
    readonly repeat: RegexComponent;
    readonly min: number;
    readonly max: number | undefined;

    constructor(repeat: RegexComponent, min: number, max: number | undefined) {
        super();

        this.repeat = repeat;
        this.min = min;
        this.max = max;
    }

    bsqon_literal_emit(): string {
        if(this.max === undefined) {
            return this.repeat.useParens() ? `(${this.repeat.bsqon_literal_emit()}){${this.min},}` : `${this.repeat.bsqon_literal_emit()}{${this.min},}`;
        }
        else if(this.min === this.max) {
            return this.repeat.useParens() ? `(${this.repeat.bsqon_literal_emit()}){${this.min}}` : `${this.repeat.bsqon_literal_emit()}{${this.min}}`;
        }
        else {
            return this.repeat.useParens() ? `(${this.repeat.bsqon_literal_emit()}){${this.min},${this.max}}` : `${this.repeat.bsqon_literal_emit()}{${this.min},${this.max}}`;
        }
    }

    jemit(): any {
        return ["TreeIR::RegexRangeRepeat", { repeat: this.repeat.jemit(), min: this.min, max: this.max !== undefined ? this.max : null }];
    }

    static jparse(obj: any): RegexComponent {
        return new RegexRangeRepeat(RegexComponent.jparse(obj[1].repeat), obj[1].min, obj[1].max !== null ? obj[1].max : undefined);
    }

    compileToECMA(regexmap: Map<string, BSQRegex>): string {
        if(this.max === undefined) {
            return this.repeat.useParens() ? `(${this.repeat.compileToECMA(regexmap)}){${this.min},}` : `${this.repeat.compileToECMA(regexmap)}{${this.min},}`;
        }
        else if(this.min === this.max) {
            return this.repeat.useParens() ? `(${this.repeat.compileToECMA(regexmap)}){${this.min}}` : `${this.repeat.compileToECMA(regexmap)}{${this.min}}`;
        }
        else {
            return this.repeat.useParens() ? `(${this.repeat.compileToECMA(regexmap)}){${this.min},${this.max}}` : `${this.repeat.compileToECMA(regexmap)}{${this.min},${this.max}}`;
        }
    }

    bsqonemit(): string {
        return `TreeIR::RegexRangeRepeat{${this.repeat.bsqonemit()}, ${this.min}n, ${this.max !== undefined ? `${this.max}n` : "none"}}`;
    }
}

class RegexOptional extends RegexComponent {
    readonly opt: RegexComponent;

    constructor(opt: RegexComponent) {
        super();

        this.opt = opt;
    }

    bsqon_literal_emit(): string {
        return this.opt.useParens() ? `(${this.opt.bsqon_literal_emit()})?` : `${this.opt.bsqon_literal_emit()}?`;
    }

    jemit(): any {
        return ["TreeIR::RegexOptional", { opt: this.opt.jemit() }];
    }

    static jparse(obj: any): RegexComponent {
        return new RegexOptional(RegexComponent.jparse(obj[1].opt));
    }

    compileToECMA(regexmap: Map<string, BSQRegex>): string {
        return this.opt.useParens() ? `(${this.opt.compileToECMA(regexmap)})?` : `${this.opt.compileToECMA(regexmap)}?`;
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

    bsqon_literal_emit(): string {
        return this.opts.map((opt) => opt.bsqon_literal_emit()).join("|");
    }

    jemit(): any {
        return ["TreeIR::RegexAlternation", { opts: this.opts.map((opt) => opt.jemit()) }];
    }

    static jparse(obj: any): RegexComponent {
        return new RegexAlternation(obj[1].opts.map((opt: any) => RegexComponent.jparse(opt)));
    }

    compileToECMA(regexmap: Map<string, BSQRegex>): string {
        return this.opts.map((opt) => opt.compileToECMA(regexmap)).join("|");
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

    bsqon_literal_emit(): string {
        return this.elems.map((elem) => elem.bsqon_literal_emit()).join("");
    }

    jemit(): any {
        return ["TreeIR::RegexSequence", { elems: this.elems.map((elem) => elem.jemit()) }];
    }

    static jparse(obj: any): RegexComponent {
        return new RegexSequence(obj[1].elems.map((elem: any) => RegexComponent.jparse(elem)));
    }

    compileToECMA(regexmap: Map<string, BSQRegex>): string {
        return this.elems.map((elem) => elem.compileToECMA(regexmap)).join("");
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
