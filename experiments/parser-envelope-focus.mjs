import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {dirname} from "node:path";

const K=await import("file:///tmp/mathgraph-parser-envelope/kernel.mjs");
const CAPS=[
  "sort","binders","application","reduction","declarations","universes",
  "theorems","proof-irrelevance","function-eta","inductive-envelope",
  "single-inductives","reflexive-inductives","inductive-reduction","rule-k",
  "unit-eta","prop-inductives","nat-literals","string-literals","quotients",
  "projections","structure-eta","rigid-conversion","opaque-declarations"
];
const targets=["init-prelude","perf/grind-ring-5"];
const rows=[];
for(const name of targets){
  const input=readFileSync("_build/tests/"+name+".ndjson","utf8");
  const attempts=[];
  for(const budget of [1_000_000,4_000_000]){
    const t=Date.now();
    const r=K.checkExport(input,CAPS,budget);
    attempts.push({budget,status:r.status,reason:r.reason,steps:r.steps??null,
      constructed:r.constructed??null,parse_records:r.parse_records??null,
      elapsed_ms:Date.now()-t,frontier_declaration:r.frontier_declaration??null});
    if(r.status!=="UNKNOWN") break;
    if(!["budget-exhausted","host-stack-limit"].includes(r.reason)) break;
  }
  rows.push({name,input_bytes:input.length,attempts});
}
const summary={
  experiment:"parser-envelope-focus",
  byte_limit:16_000_000,record_limit:300_000,rows,
  claim_boundary:"Only the existing parser resource ceilings are raised. Export grammar, reference resolution, validation, semantic budget, equality, reduction, and verdict rules are unchanged."
};
const out="genesis/evidence/parser-envelope-focus.json";
mkdirSync(dirname(out),{recursive:true});
writeFileSync(out,JSON.stringify(summary,null,2)+"\n");
console.log("PARSER_ENVELOPE_FOCUS "+JSON.stringify(summary));
