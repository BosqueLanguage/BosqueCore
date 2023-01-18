
import * as FS from "fs";
import * as Path from "path";

import * as assert from "assert";

import { BuildLevel, CodeFileInfo, PackageConfig } from "../../frontend/build_decls";
import { TIRAssembly, TIRInvoke } from "../../frontend/tree_ir/tir_assembly";
import { TypeChecker } from "../../frontend/typechecker/type_checker";
import { AssemblyEmitter } from "./compiler/assembly_emitter";

const bosque_dir: string = Path.join(__dirname, "../../../");
const core_path = Path.join(bosque_dir, "bin/runtimes/javascript/runtime/corelibs.mjs");
const runtime_path = Path.join(bosque_dir, "bin/runtimes/javascript/runtime/runtime.mjs");

const core_code = FS.readFileSync(core_path).toString();
const runtime_code = FS.readFileSync(runtime_path).toString();

const fullargs = process.argv;

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

function generateTASM(usercode: PackageConfig, buildlevel: BuildLevel, istestbuild: boolean, entrypoints: {ns: string, fname: string}[]): [TIRAssembly, Map<string, string[]>] {
    const corecode = workflowLoadCoreSrc() as CodeFileInfo[];
    const coreconfig = new PackageConfig(["EXEC_LIBS"], corecode);

    let depsmap = new Map<string, string[]>();
    const { tasm, errors } = TypeChecker.generateTASM([coreconfig, usercode], buildlevel, istestbuild, true, false, entrypoints, depsmap);
    if (errors.length !== 0) {
        for (let i = 0; i < errors.length; ++i) {
            process.stdout.write(`Parse error -- ${errors[i]}\n`);
        }

        process.exit(1);
    }

    //
    //TODO: functionalization and assignment uniqueness 
    //

    //
    //TODO: call-graph, rec-data graph, and order constructions (maybe safety too)
    //

    return [tasm as TIRAssembly, depsmap];
}

function generateJSFiles(tasm: TIRAssembly, depsmap: Map<string, string[]>, corecode: string, runtimecode: string): {nsname: string, contents: string}[] {
    const jsemittier = new AssemblyEmitter(tasm, depsmap);
    return jsemittier.generateJSCode(corecode, runtimecode)
}


function workflowEmitToDir(into: string, usercode: PackageConfig, corecode: string, runtimecode: string, buildlevel: BuildLevel, istestbuild: boolean, entrypoints: {ns: string, fname: string}[]) {
    try {
        process.stdout.write("generating assembly...\n");
        const [tasm, deps] = generateTASM(usercode, buildlevel, istestbuild, entrypoints);

        process.stdout.write("emitting JS code...\n");
        const jscode = generateJSFiles(tasm, deps, corecode, runtimecode);
        
        process.stdout.write(`writing JS code into ${into}...\n`);
        if(!FS.existsSync(into)) {
            FS.mkdirSync(into);
        }

        for(let i = 0; i < jscode.length; ++i) {
            const ppth = Path.join(into, jscode[i].nsname);

            process.stdout.write(`writing ${ppth}...\n`);

            if(jscode[i].nsname !== "Main.mjs") {
                FS.writeFileSync(ppth, jscode[i].contents);
            }
            else {
                assert(entrypoints.length === 1, "TODO: want to support multiple entrypoints later (at lease for Node.js packaging)");
                const epf = tasm.invokeMap.get(`${entrypoints[0].ns}::${entrypoints[0].fname}`) as TIRInvoke;

                const loadlogic = "[" + epf.params.map((pp, ii) => `$Runtime.bsqMarshalParse("${pp.type}", actual_args[${ii}])`).join(", ") + "]";
                const emitlogic = `$Runtime.bsqMarshalEmit("${epf.resultType}", res_val)`;

                FS.writeFileSync(ppth, jscode[i].contents + "\n\n" 
                + `const actual_args = process.argv.slice(2);\n`
                + `const bsq_args = ${loadlogic};\n`
                + `const res_val = main(...bsq_args);\n`
                + `const jres_val = ${emitlogic};\n`
                + `console.log(JSON.stringify(jres_val));\n`);
            }
        }

    } catch(e) {
        process.stderr.write(`JS emit error -- ${e}\n`);
        process.exit(1);
    }
}

function buildJSDefault(into: string, srcfiles: string[]) {
    process.stdout.write("loading user sources...\n");
    const usersrcinfo = workflowLoadUserSrc(srcfiles);
    const userpackage = new PackageConfig([], usersrcinfo);

    workflowEmitToDir(into, userpackage, core_code, runtime_code, "test", false, [{ns: "Main", fname: "main"}]);

    process.stdout.write("done!\n");
}

if(fullargs.length > 2 && fullargs[2] === "--outdir") {
    buildJSDefault(fullargs[3], fullargs.slice(4));
}
else {
    buildJSDefault("./jsout", fullargs.slice(2));
}