"use strict";

import * as path from "node:path";
import * as fsx from "fs-extra";

import { fileURLToPath } from 'url';
const __dirname = path.dirname(fileURLToPath(import.meta.url));

const rootsrc = path.join(__dirname, "../", "src");
const rootbin = path.join(__dirname, "../", "bin");

function copyResourceDir(dirfrom, dirto) {
    const srcpath = path.join(rootsrc, dirfrom);
    const dstpath = path.join(rootbin, dirto);

    process.stdout.write(`Copying ${srcpath} to ${dstpath}\n`);
    fsx.ensureDirSync(dstpath);
    fsx.emptyDirSync(dstpath);
    fsx.copySync(srcpath, dstpath);
}

process.stdout.write(`Copying resources...\n`);

copyResourceDir("core", "core");

process.stdout.write(`done!\n`);
