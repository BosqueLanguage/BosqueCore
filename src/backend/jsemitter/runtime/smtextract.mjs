import { spawnSync } from "child_process";
import fs from "fs";
import path from "path";

function runSMTExtractor(smtfile, targettype, typeinfo, flag) {
  const result = spawnSync("/home/karidus/work/BSQON/build/output/smtextract", [
    smtfile,
    targettype,
    typeinfo,
    flag,
  ]);

  if (result.error) {
    console.error("Error running smtextract:", result.error);
    throw result.error;
  }

  if (result.stderr && result.stderr.length > 0) {
    console.error("stderr:", result.stderr.toString());
  }

  console.log(`Process exited with code ${result.status}`);

  return result.stdout.toString(); // Return full stdout text
}

function parseExtractorOutput(output) {
  const lines = output.split("\n");
  const result = { value: "", types: [] };

  for (const line of lines) {
    if (line.startsWith("Value:")) {
      result.value = line.replace("Value: ", "").trim();
    } else if (line.startsWith("Type:")) {
      result.types.push(line.replace("Type: ", "").trim());
    }
  }

  return result;
}

function scanDir(dir) {
  const entries = fs.readdirSync(dir, { withFileTypes: true });
  let results = [];

  for (const entry of entries) {
    const fullPath = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      results = results.concat(scanDir(fullPath));
    } else {
      results.push(fullPath);
    }
  }

  return results;
}

function scanDirectoryForMockMeta(base_dir) {
  const mock_meta = {
    smtfile: "",
    targettype: "",
    typeinfo: "",
    flag: "-m",
  };

  const files = scanDir(base_dir);

  for (const file of files) {
    if (file.includes("formula.smt2")) {
      mock_meta.smtfile = file;
    } else if (file.includes("targettype.json")) {
      mock_meta.targettype = file;
    } else if (file.includes("typeinfo.json")) {
      mock_meta.typeinfo = file;
    }
  }

  return mock_meta;
}

export function _$extractMock() {
  const files = scanDirectoryForMockMeta(".");

  try {
    const output = runSMTExtractor(
      files.smtfile,
      files.targettype,
      files.typeinfo,
      files.flag
    );

    return parseExtractorOutput(output);
  } catch (err) {
    console.error("Error Running SMTExtractor:", err);
    return undefined;
  }
}


