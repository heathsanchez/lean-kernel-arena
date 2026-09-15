import {readFileSync,writeFileSync,mkdirSync} from "node:fs";

const K=await import("file:///tmp/mathgraph-zero-nested/kernel.mjs");
const CAPS=[
  "sort","binders","application","reduction","declarations","universes",
  "theorems","proof-irrelevance","function-eta","inductive-envelope",
  "single-inductives","reflexive-inductives","inductive-reduction","rule-k",
  "unit-eta","prop-inductives","nat-literals","string-literals","quotients",
  "projections","structure-eta","rigid-conversion","opaque-declarations"
];
const CASES=[
  ["init-prelude","frontier"],
  ["perf/grind-ring-5","frontier"],
  ["nested-unused-param","reject"],
  ["nested-nonuniform-param","reject"]
];
const rows=[];
for(const [name,want] of CASES){
  const input=readFileSync("_build/tests/"+name+".ndjson","utf8");
  const t0=Date.now();
  const r=K.checkExport(input,CAPS,1_000_000);
  const got=r.status==="UNKNOWN"&&r.reason==="inductive-semantics-frontier"?"frontier":
    r.status==="REJECT"?"reject":r.status.toLowerCase();
  const row={name,want,got,status:r.status,reason:r.reason,input_bytes:input.length,
    parse_records:r.parse_records??null,frontier_inductive:r.frontier_inductive??null,
    steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:Date.now()-t0,
    pass:got===want};
  rows.push(row);
  console.log("ROW "+JSON.stringify(row));
}
const clean=rows.every(r=>r.pass);
const out={
  experiment:"zero-param-nested-parser-frontier",
  clean,rows,
  claim_boundary:"Experimental parser-envelope correction only. Larger resource ceilings and the false recursor/minor-count representation invariants are relaxed only for one zero-parameter, zero-index nested source type whose recursor count, motive count, and unique-rule minor count agree with 1 + numNested. No nested semantic declaration is installed."
};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/zero-param-nested-parser-frontier.json",JSON.stringify(out,null,2)+"\n");
console.log("ZERO_PARAM_NESTED_PARSER_FRONTIER "+JSON.stringify(out));
if(!clean)process.exit(1);
