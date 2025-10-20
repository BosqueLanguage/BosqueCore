import { spawn } from "child_process";
import fs from "fs";
import path from "path";

function runSMTExtractor(smtfile, targettype, typeinfo, flag) {
  return new Promise((resolve, reject) => {
    const child = spawn("/home/karidus/work/BSQON/build/output/smtextract", [
      smtfile,
      targettype,
      typeinfo,
      flag,
    ]);

    let mock_res = "";

    child.stdout.on("data", (data) => {
      mock_res += data.toString();
    });

    child.stderr.on("data", (data) => {
      console.error(`stderr: ${data}`);
    });

    child.on("close", (code) => {
      console.log(`Process exited with code ${code}`);
      resolve(mock_res); // Return the full output when done
    });

    child.on("error", (err) => {
      reject(err); // In case spawn itself fails
    });
  });
}

function parseExtractorOutput(output) {
  const lines = output.split("\n");
  const result = { value: "", bsq_t: "" };

  const types = [];

  for (const line of lines) {
    if (line.startsWith("Value:")) {
      result.value = line.replace("Value: ", "").trim();
    }

    if (line.startsWith("Type:")) {
       types.push(line.replace("Type: ", "").trim());
    }
  }

	result.types = types;

  return result;
}

function scanDir(dir) {
  const entries = fs.readdirSync(dir, { withFileTypes: true });
  let results = [];

  for (const entry of entries) {
    const fullPath = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      results = results.concat(scanDir(fullPath)); // recursive call
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

export async function _$extractMock() {
  const files = scanDirectoryForMockMeta(".");
  try {
    const output = await runSMTExtractor(
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
