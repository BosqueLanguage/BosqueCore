
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
}

type CodeFileInfo = { 
    srcpath: string, 
    filename: string, 
    contents: string
};

type BuildLevel = "spec" | "test" | "release" | "safety";

function isBuildLevelEnabled(check: BuildLevel, enabled: BuildLevel): boolean {
    if(enabled === "safety") {
        return true;
    }
    
    if(enabled === "spec") {
        return check === "spec" ||  check === "test" || check === "release";
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
    SourceInfo, CodeFileInfo, PackageConfig,
};
