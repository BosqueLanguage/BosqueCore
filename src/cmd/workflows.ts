import * as fs from "fs";
import * as path from "path";

import { fileURLToPath } from 'url';
const __dirname = path.dirname(fileURLToPath(import.meta.url));

import { CodeFileInfo, PackageConfig, PackageInfo } from "../frontend/build_decls.js";
import { Assembly } from "../frontend/assembly.js";
import { Parser, ParserError } from "../frontend/parser.js";
import { TypeChecker, TypeError } from "../frontend/checker.js";
import { Status } from "./status_output.js"

const bosque_dir: string = path.join(__dirname, "../../");

function workflowLoadUserSrc(files: string[]): CodeFileInfo[] | undefined {
    try {
        let code: CodeFileInfo[] = [];

        for (let i = 0; i < files.length; ++i) {
            const realpath = path.resolve(files[i]);
            Status.output(`    ++ loading ${realpath}...\n`);

            code.push({ srcpath: realpath, filename: path.basename(realpath), contents: fs.readFileSync(realpath).toString() });
        }

        return code;
    }
    catch (ex) {
        Status.error(`Failed to load user src file!\n`);
        return undefined;
    }
}

function workflowLoadCoreSrc(): CodeFileInfo[] | undefined {
    try {
        let code: CodeFileInfo[] = [];

        const coredir = path.join(bosque_dir, "core");
        const corefiles = fs.readdirSync(coredir);
        for (let i = 0; i < corefiles.length; ++i) {
            const cfpath = path.join(coredir, corefiles[i]);
            code.push({ srcpath: cfpath, filename: corefiles[i], contents: fs.readFileSync(cfpath).toString() });
        }

        return code;
    }
    catch (ex) {
        Status.error(`Failed to load core src file!\n`);
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

function workflowLoadPackageSrc(packagePaths: string[]): PackageInfo[] | undefined {
    try {
        let packages: PackageInfo[] = [];

        for (let i = 0; i < packagePaths.length; ++i) {
            const pkgpath = path.resolve(packagePaths[i]);
            const packageconfig = JSON.parse(fs.readFileSync(path.join(pkgpath, "package.json")).toString());
            
            const pp = {
                name: packageconfig.name as string, 
                packagepath: pkgpath, 
                bosquesrc: packageconfig.bosquesrc, 
                hfiles: packageconfig.hfiles,
                cppfiles: packageconfig.cppfiles,
                buildlinks: packageconfig.buildlinks
            };

            packages.push(pp);
        }

        return packages;
    }
    catch (ex) {
        Status.error(`Failed to load external package!\n`);
        return undefined;
    }
}

function isBsqSrcExtension(filename: string): boolean {
    return filename.endsWith(".bsq") || filename.endsWith(".bsqtest");
}

function parseArgv(dir: string, ...argv: string[]): [string[], string, string, boolean, string[]] {
    let fullargs = argv.slice(2);
    if(fullargs.length === 0) {
        Status.error("No input files specified!\n");
        process.exit(1);
    }

    let emitir = false;
    let emitiridx = fullargs.findIndex((v) => v === "--iremit");
    if(emitiridx !== -1) {
        emitir = true;
        fullargs = fullargs.slice(0, emitiridx).concat(fullargs.slice(emitiridx + 1));
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

    let bsqfiles: string[] = [];
    let packages: string[] = [];
    let i = 0;
    while(i < fullargs.length) {
        if(fullargs[i] === "--package" && i + 1 < fullargs.length) {
            packages.push(fullargs[i + 1]);
            i += 2;
        }
        else {
            if(isBsqSrcExtension(fullargs[i])) {
                bsqfiles.push(fullargs[i]);
            }
            else {
                Status.error(`Unrecognized input file (skipping in compilation): ${fullargs[i]}\n`);
            }
            i++;
        }
    }

    return [bsqfiles, mainns, outdir, emitir, packages];
}

function generateASMGeneral(usercode: PackageConfig, macrodefs: string[]): [Assembly | undefined, ParserError[], TypeError[]]{
    const corecode = workflowLoadCoreSrc() as CodeFileInfo[];

    const pstart = Date.now();
    Status.output(`Parsing...\n`);
    const parseres = Parser.parse(corecode, usercode.src, macrodefs);
    const pend = Date.now();

    let tasm: Assembly | undefined = undefined;
    let parseerrors: ParserError[] = [];
    let typeerrors: TypeError[] = [];

    if(Array.isArray(parseres)) {
        parseerrors = parseres;
    }
    else {
        Status.output(`    Parsing successful [${(pend - pstart) / 1000}s]\n\n`);

        const tcstart = Date.now();
        Status.output(`Type checking...\n`);
        tasm = parseres;
        typeerrors = TypeChecker.checkAssembly(tasm);
        const tcend = Date.now();

        if(typeerrors.length === 0) {
            Status.output(`    Type checking successful [${(tcend - tcstart) / 1000}s]\n\n`);
        }
    }

    return [tasm, parseerrors, typeerrors];
}

function generateASMTest(usercode: PackageConfig): [Assembly | undefined, ParserError[], TypeError[]]{
    return generateASMGeneral(usercode, ["EXEC_LIBS", "STRIPPED_CORE"]);
}

function generateASMExec(usercode: PackageConfig): [Assembly | undefined, ParserError[], TypeError[]]{
    return generateASMGeneral(usercode, ["EXEC_LIBS"]);
}

function getSimpleFilename(fn: string): string {
    return path.basename(fn);
}

function checkAssembly(srcfiles: string[]): Assembly | undefined {
    const lstart = Date.now();
    Status.output("Loading user sources...\n");
    const usersrcinfo = workflowLoadUserSrc(srcfiles);
    if(usersrcinfo === undefined) {
        Status.error("Failed to load user sources!\n");
        return;
    }
    const dend = Date.now();
    Status.output(`    User sources loaded [${(dend - lstart) / 1000}s]\n\n`);

    const userpackage = new PackageConfig([], usersrcinfo)
    const [asm, perrors, terrors] = generateASMExec(userpackage);

    if(perrors.length === 0 && terrors.length === 0) {
        return asm;
    }
    else {
        Status.error("Failed to generate assembly!\n");

        //TODO -- need to do filename in error and sort nicely
        perrors.sort((a, b) => (a.srcfile !== b.srcfile) ? a.srcfile.localeCompare(b.srcfile) : a.sinfo.line - b.sinfo.line);
        for(let i = 0; i < perrors.length; ++i) {
            Status.error(`Parser Error @ ${getSimpleFilename(perrors[i].srcfile)}#${perrors[i].sinfo.line}: ${perrors[i].message}\n`);
        }

        terrors.sort((a, b) => (a.file !== b.file) ? a.file.localeCompare(b.file) : a.line - b.line);
        if(terrors.length !== 0) {
            for(let i = 0; i < terrors.length; ++i) {
                Status.error(`Type Error @ ${getSimpleFilename(terrors[i].file)}#${terrors[i].line}: ${terrors[i].msg}\n`);
            }
        }

        return undefined;
    }
}

export { 
    workflowLoadUserSrc, workflowLoadCoreSrc, workflowLoadAllSrc, workflowLoadPackageSrc,
    generateASMTest, generateASMExec, checkAssembly, 
    parseArgv
};