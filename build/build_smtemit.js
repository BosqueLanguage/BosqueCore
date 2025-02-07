"use strict";

import { exec } from "node:child_process";

import * as fs from "node:fs";
import * as path from "node:path";

import { fileURLToPath } from 'url';
const __dirname = path.dirname(fileURLToPath(import.meta.url));

const bsqdir = path.dirname(__dirname);
const cmdpath = path.join(bsqdir, "bin/src/cmd/bosque.js");

const binoutdir = path.join(bsqdir, "bin/smtemit");

const allsrcdirs = [
    path.join(bsqdir, "src/bsqir/asm"),
    path.join(bsqdir, "src/bsqir/simplifier"),
    path.join(bsqdir, "src/backend/smtcore/transformer"),
    path.join(bsqdir, "src/backend/smtcore/smtrepr")
];

let allsources = [];
for(let i = 0; i < allsrcdirs.length; ++i) {
    const srcdir = allsrcdirs[i];
    const srcfiles = fs.readdirSync(srcdir);
    for(let j = 0; j < srcfiles.length; ++j) {
        const srcfile = srcfiles[j];
        if(srcfile.endsWith(".bsq")) {
            allsources.push(path.join(srcdir, srcfile));
        }
    }
}

exec(`node ${cmdpath} --namespace SMTEmitter --output ${binoutdir} ${allsources.join(" ")}`, {cwd: bsqdir}, (err, stdout, stderr) => {
    if(err !== null) {
        console.log(err);
        console.log(stderr);
        process.exit(1);
    }
    else {
        console.log(stdout);
        console.log("done smt emit...");
        process.exit(0);
    }
});
