
import * as FS from "fs";
import * as Path from "path";

import { BuildLevel, CodeFileInfo, PackageConfig } from "../../frontend/build_decls";
import { TIRAssembly, TIRInvoke } from "../../frontend/tree_ir/tir_assembly";
import { TypeChecker } from "../../frontend/typechecker/type_checker";
import { AssemblyEmitter } from "./compiler/assembly_emitter";

const bosque_dir: string = Path.join(__dirname, "../../../");
const core_path = Path.join(bosque_dir, "bin/runtimes/javascript/runtime/corelibs.mjs");
const runtime_path = Path.join(bosque_dir, "bin/runtimes/javascript/runtime/runtime.mjs");
const api_path = Path.join(bosque_dir, "bin/runtimes/javascript/runtime/api.mjs");

const core_code = FS.readFileSync(core_path).toString();
const runtime_code = FS.readFileSync(runtime_path).toString();
const api_code = FS.readFileSync(api_path).toString();

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

function generateTASM(usercode: PackageConfig, buildlevel: BuildLevel, entrypoints: {ns: string, fname: string}[]): [TIRAssembly, Map<string, string[]>] {
    const corecode = workflowLoadCoreSrc() as CodeFileInfo[];
    const coreconfig = new PackageConfig(["EXEC_LIBS"], corecode);

    let depsmap = new Map<string, string[]>();
    const { tasm, errors } = TypeChecker.generateTASM([coreconfig, usercode], buildlevel, false, entrypoints, depsmap);
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

    return [tasm as TIRAssembly, depsmap];
}

function generateJSFiles(tasm: TIRAssembly, depsmap: Map<string, string[]>, corecode: string, runtimecode: string, apicode: string): {nsname: string, contents: string}[] {
    const jsemittier = new AssemblyEmitter(tasm, depsmap);
    return jsemittier.generateJSCode(corecode, runtimecode, apicode)
}


function workflowEmitToDir(into: string, usercode: PackageConfig, corecode: string, runtimecode: string, apicode: string, buildlevel: BuildLevel, entrypoints: {ns: string, fname: string}[]) {
    try {
        process.stdout.write("generating assembly...\n");
        const [tasm, deps] = generateTASM(usercode, buildlevel, entrypoints);

        process.stdout.write("emitting JS code...\n");
        const jscode = generateJSFiles(tasm, deps, corecode, runtimecode, apicode);
        
        process.stdout.write(`writing JS code into ${into}...\n`);
        if(!FS.existsSync(into)) {
            FS.mkdirSync(into);
        }

        for(let i = 0; i < jscode.length; ++i) {
            const ppth = Path.join(into, jscode[i].nsname);

            process.stdout.write(`writing ${ppth}...\n`);
            FS.writeFileSync(ppth, jscode[i].contents);
        }

        //TODO: want to support multiple entrypoints later (at least for Node.js packaging)
        const epf = tasm.invokeMap.get(`${entrypoints[0].ns}::${entrypoints[0].fname}`) as TIRInvoke;

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
            const loadlogic = "[" + epf.params.map((pp, ii) => `$API.bsqMarshalParse("${pp.type}", JSON.parse($API.cmdunescape(actual_args[${ii}].substring(1, actual_args[${ii}].length - 1))))`).join(", ") + "]";
            const emitlogic = `$API.bsqMarshalEmit("${epf.resultType}", res_val)`;

            const mainf = Path.join(into, "_main_.mjs");
            FS.writeFileSync(mainf, `"use strict";\n`
                + `import * as $API from "./api.mjs";\n`
                + `import * as $${mainNamespace} from "./${mainNamespace}.mjs";\n\n`
                + `const actual_args = process.argv.slice(2);\n`
                + `if(actual_args.length !== ${epf.params.length}) { process.stdout.write("error -- expected ${epf.params.length} args but got " + actual_args.length + " args\\n"); process.exit(0); }\n\n`
                + `const bsq_args = ${loadlogic};\n`
                + `try {\n`
                + `    const res_val = $${mainNamespace}.${mainFunction}(...bsq_args);\n`
                + `    const jres_val = ${emitlogic};\n`
                + `    console.log(JSON.stringify(jres_val));\n`
                + `} catch(ex) {\n`
                + `    process.stdout.write("error -- " + ex.msg + "\\n");\n`
                + `}\n`);
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

    workflowEmitToDir(into, userpackage, core_code, runtime_code, api_code, "test", [{ns: mainNamespace, fname: mainFunction}]);

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
    buildJSDefault(fullargs[3], fullargs.slice(4));
}
else {
    buildJSDefault("./jsout", fullargs.slice(2));
}