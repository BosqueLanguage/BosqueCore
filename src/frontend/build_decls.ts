
class SourceInfo {
    readonly line: number;
    readonly column: number;
    readonly pos: number;
    readonly span: number;

    constructor(line: number, column: number, cpos: number, span: number) {
        this.line = line;
        this.column = column;
        this.pos = cpos;
        this.span = span;
    }

    static implicitSourceInfo(): SourceInfo {
        return new SourceInfo(-1, -1, -1, -1);
    }

    static computeInfoSpan(start: SourceInfo, end: SourceInfo): SourceInfo {
        return new SourceInfo(start.line, start.column, start.pos, (start.pos - end.pos) + end.span);
    }
}

type CodeFileInfo = { 
    srcpath: string, 
    filename: string, 
    contents: string
};

class CodeFormatter {
    private level: number;

    constructor() {
        this.level = 0;
    }

    indentPush() {
        this.level++;
    }
    
    indentPop() {
        this.level--;
    }
    
    indent(code: string): string {
        return "    ".repeat(this.level) + code;
    }   
}

type BuildLevel = "spec" | "debug" | "test" | "release" | "safety";

function isBuildLevelEnabled(check: BuildLevel, enabled: BuildLevel): boolean {
    if(enabled === "safety") {
        return true;
    }
    
    if(enabled === "spec") {
        return check === "spec" || check === "debug" || check === "test" || check === "release";
    }
    else if(enabled === "debug") {
        return check === "debug" || check === "test" || check === "release";
    }
    else if(enabled === "test") {
        return check === "test" || check === "release";
    }
    else {
        return check === "release";
    }
}

class PackageConfig {
    readonly macrodefs: string[]; 
    readonly src: CodeFileInfo[];

    constructor(macrodefs: string[], src: CodeFileInfo[]) {
        this.macrodefs = macrodefs;
        this.src = src;
    }

    jemit(): object {
        return { macrodefs: this.macrodefs, src: this.src };
    }

    static jparse(jobj: any): PackageConfig {
        return new PackageConfig(jobj.macrodefs, jobj.src);
    }
}

export {
    BuildLevel, isBuildLevelEnabled,
    CodeFormatter,
    SourceInfo, CodeFileInfo, PackageConfig,
};
