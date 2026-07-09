"use strict";

import { sampledir, runTestSet } from "../../../bin/test/documentation/docs_nf.js";
import { describe, it } from "node:test";

import { join } from "node:path";
import { readFileSync } from "node:fs";

const tttfilename = join(sampledir, "raytrace/raytrace.bsq");
const dtype = "%%" + readFileSync(tttfilename, "utf8").toString();

describe ("raytrace exec", () => {
    it("runit", function () {
        runTestSet(`${dtype}`, [['10n', 'List<Main::Color>{ Main::Color{ 0.0f, 0.0f, 0.0f }, Main::Color{ 0.0f, 0.0f, 0.0f }, Main::Color{ 0.912800854668f, 0.875920012055f, 0.737616852257f }, Main::Color{ 0.867587211523f, 0.832533182775f, 0.701080574968f }, Main::Color{ 0.590167481439f, 0.566322330674f, 0.476903015304f }, Main::Color{ 0.132674841403f, 0.12206326804f, 0.134199786989f }, Main::Color{ 0.00934055269352f, 3.4421654936e-34f, 0.0536147724608f }, Main::Color{ 0.00821649139011f, 9.75964523467e-11f, 0.0471626600457f }, Main::Color{ 0.0176059785484f, 5.6053074132e-179f, 0.0995893736073f }, Main::Color{ 0.0179945180439f, 3.8143983688e-110f, 0.101787172774f } }']], []);
    });
});
