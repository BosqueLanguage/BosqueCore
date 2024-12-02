import { runMainCode } from "../../../bin/test/apps/apps_nf.js";
import { describe, it } from "node:test";

const init = "public function main(): Float { var system = NBodySystem::create(); let step = 0.01f; return system.energy(); }";
const step1 = "public function main(): Float { var system = NBodySystem::create(); let step = 0.01f; system = system.advance(step); return system.energy(); }";

const step3 = "public function main(): Float { var system = NBodySystem::create(); let step = 0.01f; system = system.advance(step); system = system.advance(step); system = system.advance(step); return system.energy(); }";

describe ("NBody", () => {
    it("init value", function () {
        runMainCode("nbody/nbody.bsq", init, [-0.16907516382852444, "Float"]); 
    });

    it("step 1", function () {
        runMainCode("nbody/nbody.bsq", step1, [-0.16907495402506748, "Float"]); 
    });

    it("step 3", function () {
        runMainCode("nbody/nbody.bsq", step3, [-0.1690745314240226, "Float"]); 
    });
});
