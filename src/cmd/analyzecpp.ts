import * as fs from "fs";

/*
import { Assembly } from "../frontend/assembly.js";
import * as path from "path";
import { fileURLToPath } from 'url';

const __dirname = path.dirname(fileURLToPath(import.meta.url));

const bosque_dir: string = path.join(__dirname, "../../../");
*/

// Doesnt really do much but spit out a file at outname directory for now
// Would be good to call this generateCPPFile somewhere internally to this file
// then export the wrapper method 
function generateCPPFile(cppcomponents: string, outname: string) {
    let code: string = cppcomponents;

    fs.writeFileSync(outname, code);
}

export { generateCPPFile };