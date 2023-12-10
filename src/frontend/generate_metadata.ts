
import * as FS from "fs";
import * as Path from "path";

import { BuildLevel, CodeFileInfo, PackageConfig } from "./build_decls";
import { TIRAssembly } from "./tree_ir/tir_assembly";
import { TypeChecker } from "./typechecker/type_checker";

const bosque_dir: string = Path.join(__dirname, "../../");
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

    return [tasm as TIRAssembly, depsmap, aliasmap];
}

function workflowEmitToDir(into: string, usercode: PackageConfig, entrypoints: {ns: string, fname: string}[]) {
    try {
        process.stdout.write("generating assembly...\n");
        const [tasm, _, aliasmap] = generateTASM(usercode, "release", entrypoints);

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

        //generate the typeinfo file and write
        process.stdout.write(`writing metadata ...\n`);
        const entrytypes = epf.params.map((pp) => pp.type).concat([epf.resultType]);
        const tinfo = tasm.generateTypeInfo(entrytypes, aliasmap);
        const tinfopath = Path.join(into, "metadata.json");

        if(into === "--stdout") {
            process.stdout.write(JSON.stringify(tinfo.emit(), undefined, 2));
        }
        else {
            FS.writeFileSync(tinfopath, JSON.stringify(tinfo.emit(), undefined, 2));
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

    workflowEmitToDir(into, userpackage, [{ns: mainNamespace, fname: mainFunction}]);

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
else if(fullargs.length > 1 && fullargs[1] === "--stdout") {
    buildTSDefault("--stdout", fullargs.slice(3));
}
else {
    buildTSDefault(".", fullargs.slice(2));
}
