"use strict";

const assert = require("assert");
const { parseExpOk } = require("/home/mark/Code/BosqueCore/bin/test/parser/parse_nf.js");

describe ("Parser -- special literals", function () {
    it("should parse none", function () {
        assert.equal(parseExpOk("none"), "none");
    });

    it("should parse nothing", function () {
        assert.equal(parseExpOk("nothing"), "nothing");
    });

    it("should parse true", function () {
        assert.equal(parseExpOk("true"), "true");
    });

    it("should parse false", function () {
        assert.equal(parseExpOk("false"), "false");
    });
});
