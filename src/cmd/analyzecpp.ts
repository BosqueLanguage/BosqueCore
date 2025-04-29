import * as fs from "fs";
import * as path from "path";
import { fileURLToPath } from 'url';
import { Assembly } from "../frontend/assembly.js";

const __dirname = path.dirname(fileURLToPath(import.meta.url));

const bosque_dir: string = path.join(__dirname, "../../../");
const outdir: string = path.join(bosque_dir, "bin/cpp");
/*
import { Assembly } from "../frontend/assembly.js";

const __dirname = path.dirname(fileURLToPath(import.meta.url));

const bosque_dir: string = path.join(__dirname, "../../../");
*/

// Doesnt really do much but spit out a file at outname directory for now
// Would be good to call this generateCPPFile somewhere internally to this file
// then export the wrapper method 
function generateCPPFile(asm: Assembly) {


    fs.writeFileSync(outdir, "");
}

export { generateCPPFile };