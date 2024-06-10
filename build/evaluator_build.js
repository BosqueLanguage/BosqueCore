"use strict";

import * as fsx from "fs-extra";
import * as path from "node:path";
import * as proc from "node:child_process";

import { fileURLToPath } from 'url';
const __dirname = path.dirname(fileURLToPath(import.meta.url));

const rootsrc = path.join(__dirname, "../", "src/tooling/checker/evaluator");
const apisrc = path.join(__dirname, "../", "src/tooling/api_parse");
const cppfiles = [rootsrc, apisrc].map((pp) => pp + "/*.cpp");

const includebase = path.join(__dirname, "include");
const includeheaders = [path.join(includebase, "headers/json"), path.join(includebase, "headers/z3")];
const outexec = path.join(__dirname, "output/chk");
const outobj = path.join(__dirname, "output", "obj");

const mode = process.argv[2] || "debug";

let compiler = "";
let ccflags = "";
let includes = " ";
let outfile = "";
let z3lib = "";
    compiler = "g++";
    ccflags = (mode === "debug" ? "-g" : "-O2") + " -Wall -Wextra -Wuninitialized -Wno-unused-parameter -Werror -std=c++2a";
    includes = includeheaders.map((ih) => `-I ${ih}`).join(" ");
    z3lib = path.join(includebase, "/linux/z3/bin/libz3.a")
    outfile = "-o " + outexec + "/chk";

const command = `${compiler} ${ccflags} ${includes} ${outfile} ${cppfiles.join(" ")} ${z3lib}`;

fsx.ensureDirSync(outexec);
fsx.ensureDirSync(outobj);
fsx.removeSync(outexec);

console.log(command);

try {
    const outstr = proc.execSync(command).toString();
    console.log(`${outstr}`);

    if(process.platform === "win32") {
        fsx.copyFileSync(path.join(includebase, "win/z3/bin/libz3.dll"), path.join(outexec, "libz3.dll"));
    }
}
catch (ex) {
    console.log(ex.toString());
    process.exit(1);
}
