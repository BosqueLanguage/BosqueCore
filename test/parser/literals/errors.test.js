import { parseTestExpError } from "/home/mark/Code/BosqueCore/bin/test/parser/parse_nf.js";
import { describe, it } from "node:test";

describe ("Parser -- Errors", () => {
    it("should fail simple nats", function () {
        parseTestExpError("2", "Un-annotated numeric literals are not supported", "Nat");
    });
});

