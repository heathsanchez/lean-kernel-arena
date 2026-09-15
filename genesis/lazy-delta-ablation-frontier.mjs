import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel-no-lazy-delta.mjs";
const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const TARGETS=[
 ["perf/shared-subterm","ACCEPT"],
 ["perf/church-numerals","ACCEPT"],
 ["perf/args-before-unfold","ACCEPT"],
 ["perf/folded-constant-first","ACCEPT"],
 ["perf/discarded-argument-match","ACCEPT"],
 ["undecidability/alg-conv-trans-acc-left","ACCEPT"],
 ["undecidability/alg-conv-trans-acc","REJECT"]
];
const rows=[];
for(const [name,want] of TARGETS){
 const t0=Date.now();
 const r=K.checkExport(readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8"),CAPS,1_000_000);
 const row={name,want,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:Date.now()-t0};
 rows.push(row);console.log("ROW "+JSON.stringify(row));
}
const out={experiment:"lazy-delta-ablation-frontier",rows,sharedClosed:rows[0].status==="ACCEPT",protectedClean:rows.slice(1).every(r=>r.status===r.want)};
mkdirSync("genesis/evidence",{recursive:true});writeFileSync("genesis/evidence/lazy-delta-ablation-frontier.json",JSON.stringify(out,null,2)+"\n");
console.log("LAZY_DELTA_ABLATION_FRONTIER "+JSON.stringify(out));
