"use strict";

import { exec } from "node:child_process";
import * as path from "node:path";

import { fileURLToPath } from 'url';
const __dirname = path.dirname(fileURLToPath(import.meta.url));

const builddir = __dirname;
const tscdir = path.dirname(__dirname);

let donecopy = false;
let donets = false;

let haderror = false;

function doneop(iserror, msg) {
    haderror = haderror || iserror;

    process.stdout.write(msg + "\n");
    if(donecopy && donets) {
        if(!haderror) {
            process.stdout.write("done!\n");
            process.exit(0);
        }
        else {
            process.stdout.write("error!\n");
            process.exit(1);
        }
    }
}

const mode = process.argv[2] || "debug";

exec("tsc -p tsconfig.json", {cwd: tscdir}, (err, stdout, stderr) => {
    donets = true;
    doneop(err !== null, err !== null ? err + stderr + stdout : "done tsc..."); 
});

exec("node ./resource_copy.js", {cwd: builddir}, (err, stdout, stderr) => {
    donecopy = true;
    doneop(err !== null, err !== null ? stderr : "done copy..."); 
});

/*
exec(`node ./evaluator_build.js ${mode}`, {cwd: builddir}, (err, stdout, stderr) => {
    donesmt = true;
    doneop(err !== null, err !== null ? stdout : "done smt...");
});
*/