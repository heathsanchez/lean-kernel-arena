import {readFileSync} from "node:fs";
import {checkExport} from "./kernel.mjs";

const CAPABILITIES=[
  "sort",
  "binders",
  "application",
  "reduction",
  "declarations",
  "universes",
  "theorems",
  "proof-irrelevance",
  "function-eta",
  "inductive-envelope",
  "single-inductives",
  "reflexive-inductives",
  "inductive-reduction",
  "rule-k",
  "unit-eta",
  "prop-inductives",
  "nat-literals",
  "string-literals",
  "quotients",
  "projections",
  "structure-eta",
  "rigid-conversion",
  "opaque-declarations"
];
const BUDGET=1_000_000;

if(process.argv.length!==3){
  console.error("usage: node main.mjs <export.ndjson>");
  process.exit(3);
}

let input;
try {
  input=readFileSync(process.argv[2],"utf8");
} catch (err) {
  console.error(String(err?.message??err));
  process.exit(3);
}

try {
  const r=checkExport(input,CAPABILITIES,BUDGET);
  process.exit(r.status==="ACCEPT"?0:r.status==="REJECT"?1:2);
} catch (err) {
  console.error(String(err?.stack??err));
  process.exit(3);
}
