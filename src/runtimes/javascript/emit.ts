import * as FS from "fs";
import * as Path from "path";


import { BuildLevel, CodeFileInfo, PackageConfig } from "../../frontend/build_decls";
import { TIRAssembly } from "../../frontend/tree_ir/tir_assembly";
import { TypeChecker } from "../../frontend/typechecker/type_checker";

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

    return [tasm as TIRAssembly, depsmap];
}

function workflowEmitToDir(into: string, usercode: PackageConfig, corecode: string, runtimecode: string, apicode: string, buildlevel: BuildLevel, istestbuild: boolean, entrypoints: {ns: string, fname: string}[]) {
    try {
        process.stdout.write("generating assembly...\n");
        const [tasm] = generateTASM(usercode, buildlevel, istestbuild, entrypoints);

        process.stdout.write("emitting IR code...\n");
        const ircode = tasm.bsqemit();
        
        process.stdout.write(`writing IR code into ${into}...\n`);
        const ppth = Path.normalize(into);
        FS.writeFileSync(ppth, JSON.stringify(ircode, undefined, 2));

    } catch(e) {
        process.stderr.write(`JS emit error -- ${e}\n`);
        process.exit(1);
    }
}

function buildIRDefault(into: string, srcfiles: string[]) {
    process.stdout.write("loading user sources...\n");
    const usersrcinfo = workflowLoadUserSrc(srcfiles);
    const userpackage = new PackageConfig([], usersrcinfo);

    workflowEmitToDir(into, userpackage, core_code, runtime_code, api_code, "test", false, [{ns: mainNamespace, fname: mainFunction}]);

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

if(fullargs.length > 2 && fullargs[2] === "--outfile") {
    buildIRDefault(fullargs[3], fullargs.slice(4));
}
else {
    buildIRDefault("./ir.json", fullargs.slice(2));
}