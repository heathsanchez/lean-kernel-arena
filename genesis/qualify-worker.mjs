import {readFileSync,statSync} from "node:fs";
import {createHash} from "node:crypto";
import {checkExport,productionConfig} from "./production.mjs";
import {runtimeIdentity} from "./runtime-identity.mjs";

const [path,bytesText,sha256]=process.argv.slice(2);
const started=Date.now();let runtime_sha256=null;
try {
  runtime_sha256=runtimeIdentity().sha256;
  const config=productionConfig(),expectedBytes=Number(bytesText);
  const size=statSync(path).size;
  if(size>config.inputBytes) throw new Error("input-cap");
  if(size!==expectedBytes) throw new Error("byte-count-mismatch");
  const data=readFileSync(path);
  const actual=createHash("sha256").update(data).digest("hex");
  if(actual!==sha256) throw new Error("sha256-mismatch");
  const result=checkExport(data.toString("utf8"),config);
  console.log(JSON.stringify({status:result.status,reason:result.reason??null,
    frontier:result.frontier_declaration??null,steps:result.steps??null,
    execution_order:result.execution_order??"retained-first",
    max_expression_depth:result.max_expression_depth??null,
    fallback_mode:result.fallback_mode??null,
    first_attempt_reason:result.first_attempt_reason??null,
    first_attempt_steps:result.first_attempt_steps??null,
    elapsed:Date.now()-started,crash:null,timeout:false,runtime_sha256}));
} catch(error) {
  console.log(JSON.stringify({status:null,reason:null,frontier:null,steps:null,
    elapsed:Date.now()-started,crash:String(error?.message??error),timeout:false,runtime_sha256}));
  process.exitCode=1;
}
