import * as fs from "node:fs";
import { execSync } from "node:child_process";

import * as $TypeInfo from "./typeinfo.ts";
import * as $BSQONParse from "./bsqon_parse.ts";
import * as $BSQONEmit from "./bsqon_emit.ts";

const proroguedImplMap = new Map<string, {args: string, result: string}[]>();

function processProroguedCall(file: string, line: number, name: string, ptypes: $TypeInfo.BSQTypeKey[], rtype: $TypeInfo.BSQTypeKey, ns: string, samples: { args: string, result: string }[], args: any[]): any {
    const pargs = `[${args.map((v: any) => $BSQONEmit.emitStd(v, rtype, ns, $TypeInfo.loaded_typeinfo)).join(", ")}]`;

    const sfound = samples.find((s) => s.args === pargs);
    if (sfound) {
        const res = $BSQONParse.parseValueStd(sfound.result, rtype, ns, $TypeInfo.loaded_typeinfo);
        return res;
    }
    else {
        process.stdout.write(`Prorogued args not matched -- ${name} in ${file}:${line}\n`);

        try {
            const iifile = __dirname + "/_prorogue_tmp.bsq";
            fs.writeFileSync(iifile, pargs, { encoding: "utf8" });
            execSync(`code -n -w ${iifile}`);

            const ff = fs.readFileSync(iifile, { encoding: "utf8" });
            const rr = ff.slice(pargs.length).trim();

            const res = $BSQONParse.parseValueStd(rr, rtype, ns, $TypeInfo.loaded_typeinfo);

            if (!proroguedImplMap.has(name)) {
                proroguedImplMap.set(name, []);
            }

            proroguedImplMap.get(name)!.push({ args: pargs, result: res });
            return res;
        } catch (e) {
            process.stdout.write(`Prorogued input failed -- ${e}\n`);
            process.exit(1);
        }
    }
}

export { 
    processProroguedCall
};
