import * as fs from "fs";
import * as path from "path";

import { fileURLToPath } from 'url';
const __dirname = path.dirname(fileURLToPath(import.meta.url));

import { CodeFileInfo, PackageConfig } from "../frontend/build_decls.js";
import { Assembly } from "../frontend/assembly.js";
import { Parser, ParserError } from "../frontend/parser.js";
import { TypeChecker, TypeError } from "../frontend/checker.js";

const bosque_dir: string = path.join(__dirname, "../../../");

class Status {
    enabled: Boolean = true;
   
    enable() {
        this.enabled = true;
    }    

    output(msg: string) {
        if(this.enabled) {
            process.stdout.write(msg);
        }
    }

    error(msg: string) {
        if(this.enabled) {
            process.stderr.write(msg);
        }
    }    
}
let status = new Status();

function workflowLoadUserSrc(files: string[]): CodeFileInfo[] | undefined {
    try {
        let code: CodeFileInfo[] = [];

        for (let i = 0; i < files.length; ++i) {
            const realpath = path.resolve(files[i]);
            status.output(`    ++ loading ${realpath}...\n`);

            code.push({ srcpath: realpath, filename: path.basename(realpath), contents: fs.readFileSync(realpath).toString() });
        }

        return code;
    }
    catch (ex) {
        status.error(`Failed to load user src file!\n`);
        return undefined;
    }
}

function workflowLoadCoreSrc(): CodeFileInfo[] | undefined {
    try {
        let code: CodeFileInfo[] = [];

        const coredir = path.join(bosque_dir, "bin/core");
        const corefiles = fs.readdirSync(coredir);
        for (let i = 0; i < corefiles.length; ++i) {
            const cfpath = path.join(coredir, corefiles[i]);
            code.push({ srcpath: cfpath, filename: corefiles[i], contents: fs.readFileSync(cfpath).toString() });
        }

        return code;
    }
    catch (ex) {
        status.error(`Failed to load core src file!\n`);
        return undefined;
    }
}

function workflowLoadAllSrc(files: string[]): CodeFileInfo[] | undefined {
    const core = workflowLoadCoreSrc();
    const user = workflowLoadUserSrc(files);

    if(core === undefined || user === undefined) {
        return undefined;
    }
    else {
        return [...core, ...user];
    }
}

function parseArgv(dir: string, ...argv: string[]): [string[], string, string] {
    let fullargs = argv.slice(2);
    if(fullargs.length === 0) {
        status.error("No input files specified!\n");
        process.exit(1);
    }

    let mainns = "Main";
    let mainnsidx = fullargs.findIndex((v) => v === "--namespace");
    if(mainnsidx !== -1) {
        mainns = fullargs[mainnsidx + 1];
        fullargs = fullargs.slice(0, mainnsidx).concat(fullargs.slice(mainnsidx + 2));
    }

    let outdir = path.join(path.dirname(path.resolve(fullargs[0])), dir);
    let outdiridx = fullargs.findIndex((v) => v === "--output");
    if(outdiridx !== -1) {
        outdir = fullargs[outdiridx + 1];
        fullargs = fullargs.slice(0, outdiridx).concat(fullargs.slice(outdiridx + 2));
    }
   
    return [fullargs, mainns, outdir];
}

function generateASMGeneral(usercode: PackageConfig, macrodefs: string[]): [Assembly | undefined, ParserError[], TypeError[]]{
    const corecode = workflowLoadCoreSrc() as CodeFileInfo[];

    const pstart = Date.now();
    status.output(`Parsing...\n`);
    const parseres = Parser.parse(corecode, usercode.src, macrodefs);
    const pend = Date.now();

    let tasm: Assembly | undefined = undefined;
    let parseerrors: ParserError[] = [];
    let typeerrors: TypeError[] = [];

    if(Array.isArray(parseres)) {
        parseerrors = parseres;
    }
    else {
        status.output(`    Parsing successful [${(pend - pstart) / 1000}s]\n\n`);

        const tcstart = Date.now();
        status.output(`Type checking...\n`);
        tasm = parseres;
        typeerrors = TypeChecker.checkAssembly(tasm);
        const tcend = Date.now();

        if(typeerrors.length === 0) {
            status.output(`    Type checking successful [${(tcend - tcstart) / 1000}s]\n\n`);
        }
    }

    return [tasm, parseerrors, typeerrors];
}

function generateASM(usercode: PackageConfig): [Assembly | undefined, ParserError[], TypeError[]]{
    return generateASMGeneral(usercode, ["EXEC_LIBS", "STRIPPED_CORE"]);
}

function generateASMSMT(usercode: PackageConfig): [Assembly | undefined, ParserError[], TypeError[]]{
    // TODO: support for smt libraries in bosque (or perhaps unnecessary?)
    //return generateASMGeneral(usercode, ["SMT_LIBS"]);
    return generateASMGeneral(usercode, ["EXEC_LIBS", "STRIPPED_CORE"]);
}

function getSimpleFilename(fn: string): string {
    return path.basename(fn);
}

function checkAssembly(srcfiles: string[], asmtype: "smt" | "cpp"): Assembly | undefined {
    const lstart = Date.now();
    status.output("Loading user sources...\n");
    const usersrcinfo = workflowLoadUserSrc(srcfiles);
    if(usersrcinfo === undefined) {
        status.error("Failed to load user sources!\n");
        return;
    }
    const dend = Date.now();
    status.output(`    User sources loaded [${(dend - lstart) / 1000}s]\n\n`);

    const userpackage = new PackageConfig([], usersrcinfo)
    const [asm, perrors, terrors] = asmtype === "cpp"
        ? generateASM(userpackage) 
        : generateASMSMT(userpackage);

    if(perrors.length === 0 && terrors.length === 0) {
        return asm;
    }
    else {
        status.error("Failed to generate assembly!\n");

        //TODO -- need to do filename in error and sort nicely
        perrors.sort((a, b) => (a.srcfile !== b.srcfile) ? a.srcfile.localeCompare(b.srcfile) : a.sinfo.line - b.sinfo.line);
        for(let i = 0; i < perrors.length; ++i) {
            status.error(`Parser Error @ ${getSimpleFilename(perrors[i].srcfile)}#${perrors[i].sinfo.line}: ${perrors[i].message}\n`);
        }

        terrors.sort((a, b) => (a.file !== b.file) ? a.file.localeCompare(b.file) : a.line - b.line);
        if(terrors.length !== 0) {
            for(let i = 0; i < terrors.length; ++i) {
                status.error(`Type Error @ ${getSimpleFilename(terrors[i].file)}#${terrors[i].line}: ${terrors[i].msg}\n`);
            }
        }

        return undefined;
    }
}

export { 
    Status,
    workflowLoadUserSrc, workflowLoadCoreSrc, workflowLoadAllSrc, 
    generateASM, generateASMSMT, checkAssembly, 
    parseArgv
};