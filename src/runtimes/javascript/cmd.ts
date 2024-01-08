
import * as FS from "fs";
import * as Path from "path";

import { BuildLevel, CodeFileInfo, PackageConfig } from "../../frontend/build_decls";
import { TIRAssembly } from "../../frontend/tree_ir/tir_assembly";
import { TypeChecker } from "../../frontend/typechecker/type_checker";
import { AssemblyEmitter } from "./compiler/assembly_emitter";

const bosque_dir: string = Path.join(__dirname, "../../../");
const bsq_runtime_src = [
    Path.join(bosque_dir, "src/runtimes/javascript/runtime/constants.ts"),
    Path.join(bosque_dir, "src/runtimes/javascript/runtime/runtime.ts"),
    Path.join(bosque_dir, "src/runtimes/javascript/runtime/bsqon_emit.ts"),
    Path.join(bosque_dir, "src/runtimes/javascript/runtime/bsqon_parse.ts"),
    Path.join(bosque_dir, "src/runtimes/javascript/runtime/prorogue.ts"),
    Path.join(bosque_dir, "src/frontend/tree_ir/typeinfo.ts")
];

let fullargs = process.argv;

function workflowLoadUserSrc(files: string[]): CodeFileInfo[] {
    try {
        let code: CodeFileInfo[] = [];

        for (let i = 0; i < files.length; ++i) {
            const realpath = Path.resolve(files[i]);
            process.stdout.write(`loading ${realpath}...\n`);

            code.push({ srcpath: realpath, filename: Path.basename(files[i]), contents: FS.readFileSync(realpath).toString() });
        }

        return code;
    }
    catch (ex) {
        process.stderr.write(`Failed to load user src file!\n`);
        process.exit(1);
    }
}

function workflowLoadCoreSrc(): CodeFileInfo[] {
    try {
        let code: CodeFileInfo[] = [];

        const coredir = Path.join(bosque_dir, "bin/core");
        const corefiles = FS.readdirSync(coredir);
        for (let i = 0; i < corefiles.length; ++i) {
            const cfpath = Path.join(coredir, corefiles[i]);
            code.push({ srcpath: cfpath, filename: corefiles[i], contents: FS.readFileSync(cfpath).toString() });
        }

        return code;
    }
    catch (ex) {
        process.stderr.write(`Failed to load core src file!\n`);
        process.exit(1);
    }
}

function generateTASM(usercode: PackageConfig, buildlevel: BuildLevel, entrypoints: {ns: string, fname: string}[]): [TIRAssembly, Map<string, string[]>, Map<string, string>] {
    const corecode = workflowLoadCoreSrc() as CodeFileInfo[];
    const coreconfig = new PackageConfig(["EXEC_LIBS"], corecode);

    let depsmap = new Map<string, string[]>();
    const { tasm, errors, aliasmap } = TypeChecker.generateTASM([coreconfig, usercode], buildlevel, entrypoints, depsmap);
    if (errors.length !== 0) {
        for (let i = 0; i < errors.length; ++i) {
            process.stdout.write(`Parse error -- ${errors[i]}\n`);
        }

        process.exit(1);
    }

    /*
    const stasm = (tasm as TIRAssembly).bsqemit();
    const rtasm = TIRAssembly.bsqparse(stasm);
    const ertasm = rtasm.bsqemit();
    if(JSON.stringify(stasm, undefined, 2) !== JSON.stringify(ertasm, undefined, 2)) {
        process.stdout.write("ARGH\n\n");
        process.stdout.write(JSON.stringify(detailedDiff(stasm, ertasm), undefined, 2) + "\n\n");
        process.stdout.write(JSON.stringify(diff(stasm, ertasm), undefined, 2) + "\n\n");
        process.exit(1);
    }
    */

    return [tasm as TIRAssembly, depsmap, aliasmap];
}

function generateTSFiles(tasm: TIRAssembly, depsmap: Map<string, string[]>, asdeno: boolean): {nsname: string, contents: string}[] {
    const tsemittier = new AssemblyEmitter(tasm, depsmap);
    return tsemittier.generateTSCode(asdeno)
}

function workflowEmitToDir(into: string, usercode: PackageConfig, buildlevel: BuildLevel, entrypoints: {ns: string, fname: string}[], asdeno: boolean) {
    try {
        process.stdout.write("generating assembly...\n");
        const [tasm, deps, aliasmap] = generateTASM(usercode, buildlevel, entrypoints);

        //TODO: want to support multiple entrypoints later (at least for Node.js packaging)
        const epns = tasm.namespaceMap.get(entrypoints[0].ns);
        if(epns === undefined) {
            process.stderr.write(`entrypoint namespace ${entrypoints[0].ns} not found\n`);
            process.exit(1);
        }

        const epf = tasm.invokeMap.get(`${entrypoints[0].ns}::${entrypoints[0].fname}`);
        if(epf === undefined) {
            process.stderr.write(`entrypoint ${entrypoints[0].ns}::${entrypoints[0].fname} not found\n`);
            process.exit(1);
        }

        process.stdout.write("emitting TS code...\n");
        const tscode = generateTSFiles(tasm, deps, asdeno);

        process.stdout.write(`writing TS code into ${into}...\n`);
        if(!FS.existsSync(into)) {
            FS.mkdirSync(into);
        }

        //copy the runtime files
        process.stdout.write(`copying runtime...\n`);
        bsq_runtime_src.forEach((src) => {
            const ppth = Path.join(into, Path.basename(src));
            FS.copyFileSync(src, ppth);
        });

        //generate the typeinfo file and write
        process.stdout.write(`writing metadata ...\n`);
        const entrytypes = epf.params.map((pp) => pp.type).concat([epf.resultType]);
        const tinfo = tasm.generateTypeInfo(entrytypes, aliasmap);
        const tinfopath = Path.join(into, "metadata.ts");
        FS.writeFileSync(tinfopath, `export const metainfo = ${JSON.stringify(tinfo.emit(), undefined, 2)};\n`);

        //write all of the user code files
        for (let i = 0; i < tscode.length; ++i) {
            const ppth = Path.join(into, tscode[i].nsname);

            process.stdout.write(`writing ${ppth}...\n`);
            FS.writeFileSync(ppth, tscode[i].contents);
        }

        //generate the main file and write -- reading from the command line or a file

        const iext = asdeno ? ".ts" : "";

        const mainf = Path.join(into, "_main.ts");
        FS.writeFileSync(mainf, `import * as process from "node:process"; import {Buffer} from "node:buffer";\n import fs from "node:fs";\nimport path from "node:path";\n`
            + `import * as $TypeInfo from "./typeinfo${iext}";\n`
            + `import * as $JASM from "./metadata${iext}";\n`
            + `import * as $Runtime from "./runtime${iext}";\n`
            + `import * as $Parse from "./bsqon_parse${iext}";\n`
            + `import * as $Emit from "./bsqon_emit${iext}";\n`
            + `import * as $Prorogue from "./prorogue${iext}";\n`
            + `import * as $${mainNamespace} from "./${mainNamespace}${iext}";\n\n`
            + `const assembly = $TypeInfo.AssemblyInfo.parse($JASM.metainfo);\n`
            + `$TypeInfo.setLoadedTypeInfo(assembly);\n\n`
            + `async function read(stream) { const chunks = []; for await (const chunk of stream) chunks.push(chunk); return Buffer.concat(chunks).toString('utf8'); }\n`
            + `const filearg = process.argv.slice(2).find((aarg) => aarg.startsWith("--input="));\n`
            + (epf.params.length === 0 ? `const arg_string = "";\n\n` : `const arg_string = filearg === undefined ? await read(process.stdin) : fs.readFileSync(path.normalize(filearg.substring(8))).toString();\n\n`)
            + `let bsq_args: any[] = [];\n`
            + `try {\n`
            + `    bsq_args = $Parse.BSQONParser.parseInputsStd(arg_string, [${epf.params.map((pp) => '"' + pp.type + '"').join(", ")}], "${epns.ns}", assembly);\n`
            //+ `    process.stderr.write(${epf.params.map((pp, ii) => `actual_args[${ii}]`).join(" + ")} + "\\n");\n`
            + `    //TODO: implement entity and typedecl checks\n`
            + `    if(bsq_args.entityChecks.length !== 0 || bsq_args.typedeclChecks.length !== 0) {\n`
            + `        bsq_args.typedeclChecks.forEach((ee) => $Runtime.validators.get(ee[0])(ee[1]));\n`
            + `        bsq_args.entityChecks.forEach((ee) => $Runtime.validators.get(ee[0])(ee[1]));\n`
            + `    }\n`
            + `} catch(exp) {\n`
            + `    process.stdout.write("error in parse -- " + JSON.stringify(exp, undefined, 2) + "\\n");\n`
            + `    process.exit(0);\n`
            + `}\n\n`
            + `try {\n`
            + `    const res_val = $${mainNamespace}.${mainFunction}(${epf.params.map((pp, ii) => `bsq_args.result[${ii}]`).join(", ")});\n`
            + `    const bsqonres_val = $Emit.BSQONEmitter.emitStd(res_val, "${epf.resultType}", "${epns.ns}", assembly);\n`
            + `    console.log(bsqonres_val);\n`
            + `    $Prorogue.listNewProroguedImpls();\n`
            + `} catch(exe) {\n`
            + `    process.stdout.write("error in eval -- " + JSON.stringify(exe, undefined, 2) + "\\n");\n`
            + `    process.exit(0);\n`
            + `}\n`);
    } catch(e) {
        process.stderr.write(`TS emit error -- ${e}\n`);
        process.exit(1);
    }
}

function buildTSDefault(into: string, srcfiles: string[]) {
    process.stdout.write("loading user sources...\n");
    const usersrcinfo = workflowLoadUserSrc(srcfiles);
    const userpackage = new PackageConfig([], usersrcinfo);

    workflowEmitToDir(into, userpackage, "test", [{ns: mainNamespace, fname: mainFunction}], true);

    process.stdout.write("done!\n");
}

let mainNamespace = "Main";
const nfs = fullargs.find((e) => e.startsWith("--namespace="));
if(nfs !== undefined) {
    mainNamespace = nfs.slice("--namespace=".length);
    fullargs = fullargs.filter((e) => e !== nfs);
}

let mainFunction = "main";
const mfs = fullargs.find((e) => e.startsWith("--function="));
if(mfs !== undefined) {
    mainFunction = mfs.slice("--function=".length);
    fullargs = fullargs.filter((e) => e !== mfs);
}

if(fullargs.length > 2 && fullargs[2] === "--outdir") {
    buildTSDefault(fullargs[3], fullargs.slice(4));
}
else {
    buildTSDefault("./tsout", fullargs.slice(2));
}