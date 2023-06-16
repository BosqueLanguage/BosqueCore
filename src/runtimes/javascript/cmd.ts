
import * as FS from "fs";
import * as Path from "path";

import { BuildLevel, CodeFileInfo, PackageConfig } from "../../frontend/build_decls";
import { TIRAssembly, TIRInvoke, TIRTypeKey } from "../../frontend/tree_ir/tir_assembly";
import { TypeChecker } from "../../frontend/typechecker/type_checker";
import { AssemblyEmitter } from "./compiler/assembly_emitter";

const bosque_dir: string = Path.join(__dirname, "../../../");
const bsq_runtime_src = [
    Path.join(bosque_dir, "bin/runtimes/javascript/runtime/constants.ts"),
    Path.join(bosque_dir, "bin/runtimes/javascript/runtime/typeinfo.ts"),
    Path.join(bosque_dir, "bin/runtimes/javascript/runtime/runtime.ts"),
    Path.join(bosque_dir, "bin/runtimes/javascript/runtime/bsqon_emit.ts"),
    Path.join(bosque_dir, "bin/runtimes/javascript/runtime/bsqon_parse.ts")
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
        process.stderr.write("Failed to load file!\n");
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
        process.stderr.write("Failed to load file!\n");
        process.exit(1);
    }
}

function generateTASM(usercode: PackageConfig, buildlevel: BuildLevel, entrypoints: {ns: string, fname: string}[]): [TIRAssembly, Map<string, string[]>, Map<string, string>] {
    const corecode = workflowLoadCoreSrc() as CodeFileInfo[];
    const coreconfig = new PackageConfig(["EXEC_LIBS"], corecode);

    let depsmap = new Map<string, string[]>();
    const { tasm, errors, aliasmap } = TypeChecker.generateTASM([coreconfig, usercode], buildlevel, false, entrypoints, depsmap);
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

function generateTSFiles(tasm: TIRAssembly, depsmap: Map<string, string[]>): {nsname: string, contents: string}[] {
    const tsemittier = new AssemblyEmitter(tasm, depsmap);
    return tsemittier.generateTSCode()
}

function workflowEmitToDir(into: string, usercode: PackageConfig, buildlevel: BuildLevel, entrypoints: {ns: string, fname: string}[]) {
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
        const tscode = generateTSFiles(tasm, deps);

        process.stdout.write(`writing TS code into ${into}...\n`);
        if(!FS.existsSync(into)) {
            FS.mkdirSync(into);
            FS.mkdirSync(Path.join(into, "src"));
        }

        //copy the runtime files
        process.stdout.write(`copying runtime...\n`);
        bsq_runtime_src.forEach((src) => {
            const ppth = Path.join(into, "src", Path.basename(src));
            FS.copyFileSync(src, ppth);
        });

        //generate the typeinfo file and write
        process.stdout.write(`writing metadata ...\n`);
        const entrytypes = epf.params.map((pp) => pp.type).concat([epf.resultType]);
        const tinfo = tasm.generateTypeInfo(entrytypes, aliasmap);
        const tinfopath = Path.join(into, "src", "metadata.ts");
        FS.writeFileSync(tinfopath, `export const metainfo = ${JSON.stringify(tinfo.emit(), undefined, 2)};\n`);

        //write all of the user code files
        for (let i = 0; i < tscode.length; ++i) {
            const ppth = Path.join(into, "src", tscode[i].nsname + ".ts");

            process.stdout.write(`writing ${ppth}...\n`);
            FS.writeFileSync(ppth, tscode[i].contents);
        }

        //generate a package.json file
        process.stdout.write(`writing build configs ...\n`);
        FS.writeFileSync(Path.join(into, "package.json"), JSON.stringify({
                "compilerOptions": {
                    "module": "Node16",
                    "alwaysStrict": true,
                    "strict": true,
                    //"noImplicitAny": true,
                    "noImplicitReturns": true,
                    "noImplicitThis": true,
                    "noUnusedLocals": true,
                    "strictNullChecks": true,
                    "target": "es2020",
                    "sourceMap": true,
                    "outDir": "bin"
                },
                "include": [
                    "src/*.ts"
                ]
            }
        ));

        //generate the main file and write -- reading from the command line or a file

        if(fileargs) {
            const loadlogic = "[" + epf.params.map((pp, ii) => `$API.bsqMarshalParse("${pp.type}", actual_args[${ii}])`).join(", ") + "]";
            const emitlogic = `$API.bsqMarshalEmit("${epf.resultType}", res_val)`;

            const mainf = Path.join(into, "_main_.mjs");
            FS.writeFileSync(mainf, `"use strict";\n`
                + `import * as FS from "fs";\n`
                + `import * as $API from "./api.mjs";\n`
                + `import * as ${mainNamespace} from "./${mainNamespace}.mjs";\n\n`
                + `const actual_args = JSON.parse(FS.readFileSync(process.argv[2], "utf8"));\n`
                + `if(!Array.isArray(actual_args) || actual_args.length !== ${epf.params.length}) { process.stdout.write("error -- expected ${epf.params.length} args\\n"); process.exit(0); }\n\n`
                + `const bsq_args = ${loadlogic};\n`
                + `try {\n`
                + `    const res_val = $${mainNamespace}.${mainFunction}(...bsq_args);\n`
                + `    const jres_val = ${emitlogic};\n`
                + `    console.log(JSON.stringify(jres_val));\n`
                + `} catch(ex) {\n`
                + `    process.stdout.write("error -- " + ex.msg + "\\n");\n`
                + `}\n`);
        }
        else if(fileasm) {
            const loadlogic = `$API.bsqMarshalParse("${epf.params[0].type}", actual_arg)`
            const emitlogic = `$API.bsqMarshalEmit("${epf.resultType}", res_val)`;

            const mainf = Path.join(into, "_main_.mjs");
            FS.writeFileSync(mainf, `"use strict";\n`
                + `import * as FS from "fs";\n`
                + `import * as $API from "./api.mjs";\n`
                + `import * as $${mainNamespace} from "./${mainNamespace}.mjs";\n\n`
                + `const actual_arg = JSON.parse(FS.readFileSync(process.argv[2], "utf8"));\n`
                + `const bsq_arg = ${loadlogic};\n`
                + `try {\n`
                + `    const res_val = $${mainNamespace}.${mainFunction}(bsq_arg);\n`
                + `    const jres_val = ${emitlogic};\n`
                + `    console.log(JSON.stringify(jres_val));\n`
                + `} catch(ex) {\n`
                + `    process.stdout.write("error -- " + ex.msg + "\\n");\n`
                + `}\n`);
        }
        else {
            const mainf = Path.join(into, "main.ts");
            FS.writeFileSync(mainf, `import * as $TypeInfo from "./typeinfo";\n`
                + `import * as $JASM from "./metadata.ts";\n`
                + `import * as $Parse from "./bsqon_parse";\n`
                + `import * as $Emit from "./bsqon_emit";\n`
                + `import * as $${mainNamespace} from "./${mainNamespace}";\n\n`
                + `const assembly = $TypeInfo.parse($JASM.metainfo);\n`
                + `const actual_args = process.argv.slice(2);\n`
                + `if(actual_args.length !== ${epf.params.length}) { process.stdout.write("error -- expected ${epf.params.length} args but got " + actual_args.length + " args\\n"); process.exit(0); }\n\n`
                + `const bsq_args = ${epf.params}.map((pp, ii) => $Parse.parseStdInput(actual_args[ii], assembly.loadType(pp.type), ${epns.ns}, assembly);\n`
                + `try {\n`
                + `    const res_val = $${mainNamespace}.${mainFunction}(...bsq_args);\n`
                + `    const bsqonres_val = $Emit.emitStd(res_val, assembly.loadType(${epf.resultType}), ${epns.ns}, assembly);\n`
                + `    console.log(JSON.stringify(jres_val));\n`
                + `} catch(ex) {\n`
                + `    process.stdout.write("error -- " + ex.msg + "\\n");\n`
                + `}\n`);
        }
    } catch(e) {
        process.stderr.write(`TS emit error -- ${e}\n`);
        process.exit(1);
    }
}

function buildTSDefault(into: string, srcfiles: string[]) {
    process.stdout.write("loading user sources...\n");
    const usersrcinfo = workflowLoadUserSrc(srcfiles);
    const userpackage = new PackageConfig([], usersrcinfo);

    workflowEmitToDir(into, userpackage, "test", [{ns: mainNamespace, fname: mainFunction}]);

    //run tsc to get the js build
    process.stdout.write("running tsc (SKIPPED)...\n");

    process.stdout.write("done!\n");
}

const fileargs = fullargs.includes("--fileargs");
if(fileargs) {
    fullargs = fullargs.filter((aa) => aa !== "--fileargs");
}

const fileasm = fullargs.includes("--fileasm");
if(fileasm) {
    fullargs = fullargs.filter((aa) => aa !== "--fileasm");
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