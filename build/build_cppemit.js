"use strict";

import { exec } from "node:child_process";

import * as fs from "node:fs";
import * as path from "node:path";

import { fileURLToPath } from 'url';
const __dirname = path.dirname(fileURLToPath(import.meta.url));

const bsqdir = path.dirname(__dirname);
const cmdpath = path.join(bsqdir, "bin/src/cmd/bosque.js");

const binoutdir = path.join(bsqdir, "bin/cpp");

const smtcoredir = path.join(bsqdir, "src/backend/cpp/cpprepr");
const smtcoretestdir = path.join(bsqdir, "src/backend/cpp/test");

const allsrcdirs = [smtcoredir, smtcoretestdir];
let allsources = [];
for(let i = 0; i < allsrcdirs.length; ++i) {
    const srcdir = allsrcdirs[i];
    const srcfiles = fs.readdirSync(srcdir);
    for(let j = 0; j < srcfiles.length; ++j) {
        const srcfile = srcfiles[j];
        if(srcfile.endsWith(".bsq") || srcfile.endsWith(".bsqtest")) {
            allsources.push(path.join(srcdir, srcfile));
        }
    }
}

exec(`node ${cmdpath} --testgen --namespace CPPEmitter --output ${binoutdir} ${allsources.join(" ")}`, {cwd: bsqdir}, (err, stdout, stderr) => {
    if(err !== null) {
        console.log(err);
        console.log(stderr);
        process.exit(1);
    }
    else {
        console.log(stdout);
        console.log("done cpp emit...");
        process.exit(0);
    }
});
