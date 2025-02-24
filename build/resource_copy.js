"use strict";

import { execSync } from "node:child_process";
import * as path from "node:path";
import * as fs from "node:fs";

import { fileURLToPath } from 'url';
const __dirname = path.dirname(fileURLToPath(import.meta.url));

const rootsrc = path.join(__dirname, "../", "src");
const rootbin = path.join(__dirname, "../", "bin");

function copyResourceDir(dirfrom, dirto) {
    const srcpath = path.join(rootsrc, dirfrom);
    const dstpath = path.join(rootbin, dirto);

    process.stdout.write(`Copying ${srcpath} to ${dstpath}\n`);
    fs.mkdirSync(dstpath, {recursive: true});
    execSync(`rm -rf ${dstpath}*`);
    execSync(`cp -R ${srcpath}* ${dstpath}`);
}

process.stdout.write(`Copying resources...\n`);

copyResourceDir("core/", "core/");
copyResourceDir("backend/jsemitter/runtime/", "jsruntime/");
copyResourceDir("backend/smtcore/runtime/", "smtruntime/");

copyResourceDir("samples/", "samples/");

process.stdout.write(`done!\n`);
