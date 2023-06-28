import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from 'node:url';

import * as process from "node:process";
import { execSync } from "node:child_process";

import * as $TypeInfo from "./typeinfo.ts";
import * as $BSQONParse from "./bsqon_parse.ts";
import * as $BSQONEmit from "./bsqon_emit.ts";

const proroguedImplMap = new Map<string, {args: string, result: string}[]>();

function processProroguedCall(file: string, line: number, name: string, ptypes: $TypeInfo.BSQTypeKey[], rtype: $TypeInfo.BSQTypeKey, ns: string, samples: { args: string, result: string }[], args: any[]): any {
    const pargs = `[${args.map((v: any) => $BSQONEmit.BSQONEmitter.emitStd(v, rtype, ns, $TypeInfo.loaded_typeinfo)).join(", ")}]`;

    const sfound = samples.find((s) => s.args === pargs);
    if (sfound !== undefined) {
        const res = $BSQONParse.BSQONParser.parseValueStd(sfound.result, rtype, ns, $TypeInfo.loaded_typeinfo);
        return res;
    }
    else {
        const pifound = (proroguedImplMap.get(name) ?? []).find((s) => s.args === pargs);
        if (pifound !== undefined) {
            const res = $BSQONParse.BSQONParser.parseValueStd(pifound.result, rtype, ns, $TypeInfo.loaded_typeinfo);
            return res;
        }
        else {
            try {
                const __dirname = path.dirname(fileURLToPath(import.meta.url));
                const iifile = path.join(__dirname, "_prorogue_tmp.bsq");

                const iicontents = `//function ${name}(${ptypes.join(", ")}): ${rtype} -- ${file}:${line}\n` + pargs;
                fs.writeFileSync(iifile, iicontents, { encoding: "utf8" });
                execSync(`code -n -w ${iifile}`);

                const ff = fs.readFileSync(iifile, { encoding: "utf8" });
                const rr = ff.slice(iicontents.length).trim();

                const res = $BSQONParse.BSQONParser.parseValueStd(rr, rtype, ns, $TypeInfo.loaded_typeinfo);

                if (!proroguedImplMap.has(name)) {
                    proroguedImplMap.set(name, []);
                }

                proroguedImplMap.get(name)!.push({ args: pargs, result: rr });
                return res;
            } catch (e) {
                process.stdout.write(`Prorogued input failed -- ${e}\n`);
                process.exit(1);
            }
        }
    }
}

export { 
    processProroguedCall
};
