import {assert} from "chai";
import { parseExpOk } from "../parse_nf";

describe ("Parser -- special literals", function () {
    it("should parse none", function () {
        assert.isOk(parseExpOk("none", "none"));
    });

    it("should parse nothing", function () {
        assert.isOk(parseExpOk("nothing", "nothing"));
    });

    it("should parse true", function () {
        assert.isOk(parseExpOk("true", "true"));
    });

    it("should parse false", function () {
        assert.isOk(parseExpOk("false", "false"));
    });
});
