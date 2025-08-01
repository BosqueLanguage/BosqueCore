import * as fs from "fs";
import * as path from "path";

import { runMainCode } from "../cppoutput/cppemit_nf.js"

const gc_test_path = "bin/cppruntime/gc/test/";

function insertGCCalls(bsqcode: string): string {
    let disableAutomaticCollections = bsqcode.replace("%*DISABLE_COLLECTIONS*%", "gtl_info.disable_automatic_collections = true;");
    let collections = disableAutomaticCollections.replace("%*COLLECT*%", "collect();");
    let assertClear = collections.replace("%*ASSERT_CLEAR*%", "assert(gtl_info.total_live_bytes == 0);");

    return assertClear;
}

function runMainCodeGC(testname: string, expected_output: string) {
    const test_contents = fs.readFileSync(path.join(gc_test_path, testname)).toString();

    const formattedTest = insertGCCalls(test_contents);
    runMainCode(formattedTest, expected_output);
}

export { runMainCodeGC };