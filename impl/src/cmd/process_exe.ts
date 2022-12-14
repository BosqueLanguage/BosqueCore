//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as fs from "fs";
import * as path from "path";
import * as net from "net";
import * as readline from "readline";

import * as chalk from "chalk";

import { help, isStdInArgs, extractArgs, loadUserSrc, tryLoadPackage, extractEntryPoint, extractConfig } from "./args_load";
import { ConfigFuzz, ConfigRun, Package } from "./package_load";
import { PackageConfig, SymbolicActionMode } from "../compiler/mir_assembly";
import { workflowRunICPPFile } from "../tooling/icpp/transpiler/iccp_workflows";
import { generateStandardVOpts, workflowEvaluate, workflowInputFuzz } from "../tooling/checker/smt_workflows";

function processRunAction(args: string[], debug: boolean) {
    if (args.length === 0) {
        args.push("./package.json");
    }

    let workingdir = process.cwd();
    let pckg: Package | undefined = undefined;
    if (path.extname(args[0]) === ".json") {
        workingdir = path.dirname(path.resolve(args[0]));
        pckg = tryLoadPackage(path.resolve(args[0]));
    }
    else {
        const implicitpckg = path.resolve(workingdir, "package.json");
        if (fs.existsSync(implicitpckg)) {
            pckg = tryLoadPackage(implicitpckg);
        }
    }

    if (pckg === undefined) {
        process.stderr.write(chalk.red("Could not parse 'package' option\n"));

        help("run");
        process.exit(1);
    }

    const entrypoint = extractEntryPoint(args, workingdir, pckg.src.entrypoints);
    if (entrypoint === undefined) {
        process.stderr.write(chalk.red("Could not parse 'entrypoint' option\n"));

        help("run");
        process.exit(1);
    }

    let fargs: any[] | undefined = undefined;
    if (!isStdInArgs(args)) {
        fargs = extractArgs(args);
        if (fargs === undefined) {
            process.stderr.write(chalk.red("Could not parse 'arguments' option\n"));

            help("run");
            process.exit(1);
        }
    }

    const cfg = extractConfig<ConfigRun>(args, pckg, workingdir, "run");
    if (cfg === undefined) {
        process.stderr.write(chalk.red("Could not parse 'config' option\n"));

        help("run");
        process.exit(1);
    }

    const srcfiles = loadUserSrc(workingdir, [...pckg.src.entrypoints, ...pckg.src.bsqsource]);
    if (srcfiles === undefined) {
        process.stderr.write(chalk.red("Failed when loading source files\n"));
        process.exit(1);
    }

    const usersrcinfo = srcfiles.map((sf) => {
        return { srcpath: sf, filename: path.basename(sf), contents: fs.readFileSync(sf).toString() };
    });
    const userpackage = new PackageConfig([...cfg.macros, ...cfg.globalmacros], usersrcinfo);

    if (fargs === undefined) {
        // bosque run|debug [package_path.json] [--entrypoint fname] [--config cname]

        let rl = readline.createInterface({
            input: process.stdin,
            output: process.stdout
        });

        rl.question(">> ", (input) => {
            try {
                const jargs = JSON.parse(input);

                process.stdout.write(`Evaluating...\n`);

                workflowRunICPPFile(jargs, userpackage, debug, cfg.buildlevel, false, debug, {}, entrypoint, (result: string | undefined) => {
                    if (result !== undefined) {
                        process.stdout.write(`${result}\n`);
                    }
                    else {
                        process.stdout.write(`failure\n`);
                    }

                    process.exit(0);
                });
            }
            catch (ex) {
                process.stderr.write(`Failure ${ex}\n`);
                process.exit(1);
            }
        });
    }
    else {
        // bosque run|debug [package_path.json] [--entrypoint fname] [--config cname] --args "[...]"
        workflowRunICPPFile(fargs, userpackage, debug, cfg.buildlevel, false, debug, {}, entrypoint, (result: string | undefined) => {
            process.stdout.write(`${result}\n`);

            process.exit(0);
        });
    }
}

function processAttachAction() {
    let dbgserver = net.createServer((socket) => {
        socket.on("data", (data) => {
            let residx = data.indexOf(0);
            let rstr = "";
            try {
                rstr = data.slice(0, residx).toString();
                
                if(!rstr.startsWith("$")) {
                    process.stdout.write(rstr);
                }
            }
            catch(ex) {
                console.log(`DEBUGGER FAILURE -- ${ex}`);
            }
        });

        process.stdin.on("data", (data) => {
            let buff = Buffer.from(data + "\0");
            socket.write(buff);
        });
    }).listen(1337, "127.0.0.1");

    dbgserver.close();
}

function processRunSymbolicAction(args: string[]) {
    const timeout = 10000;
    const eval_opts = generateStandardVOpts(SymbolicActionMode.EvaluateSymbolic);

    if(args.length === 0) {
        args.push("./package.json");
    }

    let workingdir = process.cwd();
    let pckg: Package | undefined = undefined;
    if (path.extname(args[0]) === ".json") {
        workingdir = path.dirname(path.resolve(args[0]));
        pckg = tryLoadPackage(path.resolve(args[0]));
    }
    else {
        const implicitpckg = path.resolve(workingdir, "package.json");
        if (fs.existsSync(implicitpckg)) {
            pckg = tryLoadPackage(implicitpckg);
        }
    }

    if (pckg === undefined) {
        process.stderr.write(chalk.red("Could not parse 'package' option\n"));

        help("symrun");
        process.exit(1);
    }

    const entrypoint = extractEntryPoint(args, workingdir, pckg.src.entrypoints);
    if (entrypoint === undefined) {
        process.stderr.write(chalk.red("Could not parse 'entrypoint' option\n"));

        help("symrun");
        process.exit(1);
    }

    let fargs: any[] | undefined = undefined;
    if (!isStdInArgs(args)) {
        fargs = extractArgs(args);
        if (fargs === undefined) {
            process.stderr.write(chalk.red("Could not parse 'arguments' option\n"));

            help("symrun");
            process.exit(1);
        }
    }

    const cfg = extractConfig<ConfigRun>(args, pckg, workingdir, "run");
    if (cfg === undefined) {
        process.stderr.write(chalk.red("Could not parse 'config' option\n"));

        help("symrun");
        process.exit(1);
    }

    const srcfiles = loadUserSrc(workingdir, [...pckg.src.entrypoints, ...pckg.src.bsqsource]);
    if (srcfiles === undefined) {
        process.stderr.write(chalk.red("Failed when loading source files\n"));
        process.exit(1);
    }

    const usersrcinfo = srcfiles.map((sf) => {
        return { srcpath: sf, filename: path.basename(sf), contents: fs.readFileSync(sf).toString() };
    });
    const userpackage = new PackageConfig([...cfg.macros, ...cfg.globalmacros], usersrcinfo);

    if(fargs === undefined) {
        // bosque runsym [package_path.json] [--entrypoint fname] [--config cname]
        
        let rl = readline.createInterface({
            input: process.stdin,
            output: process.stdout
        });

        rl.question(">> ", (input) => {
            try {
                const jinput = JSON.parse(input) as any[];
                workflowEvaluate(userpackage, "debug", false, timeout, eval_opts, entrypoint, jinput, (res: string) => {
                    try {
                        const jres = JSON.parse(res);

                        if (jres["status"] === "unreachable") {
                            process.stdout.write(`No valid (non error) result exists for this input!\n`);
                        }
                        else if (jres["status"] === "output") {
                            process.stdout.write(`Generated output in ${jres["time"]} millis!\n`);
                            process.stdout.write(JSON.stringify(jres["value"], undefined, 2) + "\n");
                        }
                        else if (jres["status"] === "unknown") {
                            process.stdout.write(`Solver unknown -- ${jres["info"]} -- :(\n`);
                        }
                        else {
                            process.stdout.write(`Failed with -- ${JSON.stringify(jres)}`);
                        }

                        process.exit(0);
                    }
                    catch (ex) {
                        process.stderr.write(`Failure ${ex}\n`);
                        process.exit(1);
                    }
                });
            }
            catch (ex) {
                process.stderr.write(`Failure ${ex}\n`);
                process.exit(1);
            }
        });
    }
    else {
        // bosque runsym [package_path.json] [--entrypoint fname] [--config cname] --args "[...]"
        workflowEvaluate(userpackage, "debug", false, timeout, eval_opts, entrypoint, fargs, (res: string) => {
            try {
                const jres = JSON.parse(res);

                if (jres["status"] === "unreachable") {
                    process.stdout.write(`No valid (non error) result exists for this input!\n`);
                }
                else if (jres["status"] === "output") {
                    process.stdout.write(`Generated output in ${jres["time"]} millis!\n`);
                    process.stdout.write(JSON.stringify(jres["value"], undefined, 2) + "\n");
                }
                else if (jres["status"] === "unknown") {
                    process.stdout.write(`Solver unknown -- ${jres["info"]} -- :(\n`);
                }
                else {
                    process.stdout.write(`Failed with -- ${JSON.stringify(jres)}`);
                }

                process.exit(0);
            }
            catch (ex) {
                process.stderr.write(`Failure ${ex}\n`);
                process.exit(1);
            }
        });
    }
}

function processFuzzAction(args: string[]) {
    const timeout = 10000;
    const sym_opts = generateStandardVOpts(SymbolicActionMode.InputFuzzSymbolic);

    let workingdir = process.cwd();
    let pckg: Package | undefined = undefined;
    if (path.extname(args[0]) === ".json") {
        workingdir = path.dirname(path.resolve(args[0]));
        pckg = tryLoadPackage(path.resolve(args[0]));
    }
    else {
        const implicitpckg = path.resolve(workingdir, "package.json");
        if (fs.existsSync(implicitpckg)) {
            pckg = tryLoadPackage(implicitpckg);
        }
    }

    if (pckg === undefined) {
        process.stderr.write(chalk.red("Could not parse 'package' option\n"));

        help("fuzz");
        process.exit(1);
    }

    const entrypoint = extractEntryPoint(args, workingdir, pckg.src.entrypoints);
    if (entrypoint === undefined) {
        process.stderr.write(chalk.red("Could not parse 'entrypoint' option\n"));

        help("fuzz");
        process.exit(1);
    }

    const cfg = extractConfig<ConfigFuzz>(args, pckg, workingdir, "fuzz");
    if (cfg === undefined) {
        process.stderr.write(chalk.red("Could not parse 'config' option\n"));

        help("fuzz");
        process.exit(1);
    }

    const srcfiles = loadUserSrc(workingdir, [...pckg.src.entrypoints, ...pckg.src.bsqsource]);
    if (srcfiles === undefined) {
        process.stderr.write(chalk.red("Failed when loading source files\n"));
        process.exit(1);
    }

    const usersrcinfo = srcfiles.map((sf) => {
        return { srcpath: sf, filename: path.basename(sf), contents: fs.readFileSync(sf).toString() };
    });
    const userpackage = new PackageConfig([...cfg.macros, ...cfg.globalmacros], usersrcinfo);

    //bosque fuzz [package_path.json] [--config cname]

    if(cfg.params.flavors.includes("random")) {
        //TODO: random fuzz generation
    }

    if(cfg.params.flavors.includes("solver")) {
        const start = Date.now();
        workflowInputFuzz(userpackage, "debug", false, timeout, sym_opts, entrypoint, (info: string) => process.stdout.write(info + "\n"), (res: string) => {
            try {
                const jres = JSON.parse(res);

                if (jres["result"] === "input") {
                    const end = Date.now();
                    process.stdout.write(`Generated input in ${end - start} millis!\n`);
                    process.stdout.write(JSON.stringify(jres["info"], undefined, 2) + "\n");
                }
                else {
                    process.stdout.write(`Failed with -- ${jres["info"]}` + "\n");
                }

                process.exit(0);
            }
            catch (ex) {
                process.stderr.write(`Failure ${ex}\n`);
                process.exit(1);
            }
        });
    }
}

export {
    processRunAction, processAttachAction, processRunSymbolicAction, processFuzzAction
};
