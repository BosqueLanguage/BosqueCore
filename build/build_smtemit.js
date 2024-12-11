"use strict";

import { exec } from "node:child_process";
import * as path from "node:path";

import { fileURLToPath } from 'url';
const __dirname = path.dirname(fileURLToPath(import.meta.url));

const bsqdir = path.dirname(__dirname);
const cmdpath = path.join(bsqdir, "bin/src/cmd/bosque.js");

const binoutdir = path.join(bsqdir, "bin/smtemit");
const smtcoredir = path.join(bsqdir, "src/backend/smtcore/smtrepr");

const allsrcdirs = [smtcoredir];
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

console.log(`building sources ...`);
for(let i = 0; i < allsources.length; ++i) {
    console.log(`  ${allsources[i]}`);
}

exec(`node ${cmdpath} --output ${binoutdir} ${allsources.join(" ")}`, {cwd: tscdir}, (err, stdout, stderr) => {
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