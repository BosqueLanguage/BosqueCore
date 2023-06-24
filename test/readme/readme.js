"use strict";

const expect = require("chai").expect;

const {generatePaths, codegen, invokeExecutionOn, cleanTest} = require("../codeproc.js");

describe('Readme add2', function () {
    const testopt = ["readme", "add"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('add2(3n, 4n)', function () {
        it('expected 7n', function () {
            expect(invokeExecutionOn(jsmain, "3n", "4n")).to.eql("7n");
        });
    });
    describe('add2(3n, 0n)', function () {
        it('expected 3n', function () {
            expect(invokeExecutionOn(jsmain, "3n", "0n")).to.eql("3n");
        });
    });
});

describe('Readme allPositive', function () {
    const testopt = ["readme", "allpositive"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('allPositive(List{1i, 3i, 4i})', function () {
        it('expected true', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, 3i, 4i}")).to.eql("true");
        });
    });
    describe('allPositive(List{})', function () {
        it('expected true', function () {
            expect(invokeExecutionOn(jsmain, "List{}")).to.eql("true");
        });
    });
    describe('allPositive(List{1i, -3i, 4i})', function () {
        it('expected false', function () {
            expect(invokeExecutionOn(jsmain, "List{1i, -3i, 4i}")).to.eql("false");
        });
    });
});


describe('Readme sign', function () {
    const testopt = ["readme", "sign"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('sign(5i)', function () {
        it('expected 1i', function () {
            expect(invokeExecutionOn(jsmain, "5i")).to.eql("1i");
        });
    });
    describe('sign(-5i)', function () {
        it('expected -1i', function () {
            expect(invokeExecutionOn(jsmain, "-5i")).to.eql("-1i");
        });
    });
    describe('sign(0i)', function () {
        it('expected 0i', function () {
            expect(invokeExecutionOn(jsmain, "0i")).to.eql("0i");
        });
    });
});

describe('Readme nominal generic', function () {
    const testopt = ["readme", "nominal_inv_generic"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('GenericGreeting', function () {
        it('expected ["hello world", "hello world"]', function () {
            expect(invokeExecutionOn(jsmain)).to.eql('["hello world", "hello world"]');
        });
    });
});

describe('Readme nominal named', function () {
    const testopt = ["readme", "nominal_inv_named"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('NamedGreeting', function () {
        it('expected "hello bob"', function () {
            expect(invokeExecutionOn(jsmain, '"bob"')).to.eql('"hello bob"');
        });
    });
    describe('NamedGreeting Err', function () {
        it('expected invariant failure', function () {
            expect(invokeExecutionOn(jsmain, '""')).to.contain("Failed invariant");
        });
    });
});

describe('Readme percentage', function () {
    const testopt = ["readme", "typedecl_percentage"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('Percentage 30%', function () {
        it('expected 30n_Percentage', function () {
            expect(invokeExecutionOn(jsmain, "30n")).to.eql("30n_Percentage");
        });
    });
    describe('Percentage 101 Err', function () {
        it('expected invariant failure', function () {
            expect(invokeExecutionOn(jsmain, "101n")).to.contain("Failed invariant");
        });
    });
});

describe('Readme temp', function () {
    const testopt = ["readme", "typedecl_temp"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('isFrezing 5i_Celsius', function () {
        it('expected false', function () {
            expect(invokeExecutionOn(jsmain, "5i_Celsius")).to.eql("false");
        });
    });
    describe('isFrezing -5i_Celsius', function () {
        it('expected true', function () {
            expect(invokeExecutionOn(jsmain, "-5i_Celsius")).to.eql("true");
        });
    });
});

describe('Ref Methods', function () {
    const testopt = ["readme", "refcall"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('ctrs', function () {
        it('expected [0n, 1n]', function () {
            expect(invokeExecutionOn(jsmain)).to.eql("[0n, 1n]");
        });
    });
});

describe('Binders & Flow (flowit)', function () {
    const testopt = ["readme", "flowit"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('flowit(none)', function () {
        it('expected 0', function () {
            expect(invokeExecutionOn(jsmain, "none")).to.eql("0n");
        });
    });
    describe('flowit(0n)', function () {
        it('expected 10n', function () {
            expect(invokeExecutionOn(jsmain, "0n")).to.eql("10n");
        });
    });
    describe('flowit(7n)', function () {
        it('expected 17n', function () {
            expect(invokeExecutionOn(jsmain, "7n")).to.eql("17n");
        });
    });
});

describe('Binders & Flow (restrict)', function () {
    const testopt = ["readme", "restrict"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('restrict(none)', function () {
        it('expected 0n', function () {
            expect(invokeExecutionOn(jsmain, "none")).to.eql("0n");
        });
    });
    describe('restrict(0n)', function () {
        it('expected 10n', function () {
            expect(invokeExecutionOn(jsmain, "0n")).to.eql("10n");
        });
    });
    describe('restrict(7n)', function () {
        it('expected 17n', function () {
            expect(invokeExecutionOn(jsmain, "7n")).to.eql("17n");
        });
    });
});

describe('Datatype (evaluate)', function () {
    const testopt = ["readme", "datatype_evaluate"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('evaluate (and)', function () {
        it('expected false', function () {
            expect(invokeExecutionOn(jsmain, "AndOp{2n, LConst{1n, true}, LConst{1n, false}}")).to.eql("false");
        });
    });
    describe('evaluate (or)', function () {
        it('expected true', function () {
            expect(invokeExecutionOn(jsmain, "OrOp{2n, LConst{1n, true}, LConst{1n, false}}")).to.eql("true");
        });
    });
});

describe('Union (print)', function () {
    const testopt = ["readme", "union_print"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('print (bool)', function () {
        it('expected "b"', function () {
            expect(invokeExecutionOn(jsmain, "true")).to.eql('"b"');
        });
    });
    describe('print (none)', function () {
        it('expected "n"', function () {
            expect(invokeExecutionOn(jsmain, "none")).to.eql('"n"');
        });
    });
    describe('print (int)', function () {
        it('expected "i"', function () {
            expect(invokeExecutionOn(jsmain, "7i")).to.eql('"i"');
        });
    });
});

describe('Validator (zipcode)', function () {
    const testopt = ["readme", "zipcode"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('accepts (98052)', function () {
        it('expected true', function () {
            expect(invokeExecutionOn(jsmain, '"98052"')).to.eql("true");
        });
    });
    describe('accepts (1234)', function () {
        it('expected false', function () {
            expect(invokeExecutionOn(jsmain, '"1234"')).to.eql("false");
        });
    });
});


describe('StringOf (csspt)', function () {
    const testopt = ["readme", "csspt"];
    const { srcfile, dstdir, jsmain } = generatePaths(testopt);

    before(function () { codegen(srcfile, dstdir); });
    after(function () { cleanTest(dstdir); });

    describe('is3pt (3pt)', function () {
        it('expected true', function () {
            expect(invokeExecutionOn(jsmain, '"3pt"CSSpt')).to.eql("true");
        });
    });
    describe('is3pt (4pt)', function () {
        it('expected false', function () {
            expect(invokeExecutionOn(jsmain, '"4pt"CSSpt')).to.eql("false");
        });
    });
});
