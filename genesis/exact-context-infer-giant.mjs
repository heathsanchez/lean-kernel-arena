import {readFileSync} from "node:fs";
import * as K from "./kernel.mjs";
import "./compiled-representation-reuse-layer.mjs";
import "./verified-ctoridx-consequence-layer.mjs";
import "./native-nat-reduction-layer.mjs";
import "./nat-offset-defeq-layer.mjs";
import "./exact-binder-transport-layer.mjs";
import "./exact-context-infer-layer.mjs";

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems",
"proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives",
"inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals",
"quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];

const CASES=[
 ["init-prelude",1_000_000],
 ["perf/grind-ring-5",1_000_000],
 ["perf/shared-subterm",1_000_000],
 ["undecidability/subject-reduction-redex",1_000_000],
 ["undecidability/subject-reduction-reduct",1_000_000],
 ["init-prelude",4_000_000],
 ["perf/grind-ring-5",4_000_000]
];

for(const [name,budget] of CASES){
  const seen=[],p=K.Kernel.prototype,run0=p.run;
  p.run=function(...xs){seen.push(this);return run0.apply(this,xs);};
  const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
  const t0=Date.now();let r;
  try{r=K.checkExport(input,CAPS,budget);}finally{p.run=run0;}
  const s=k=>seen.reduce((n,x)=>n+(x.__exactInferStats?.[k]??0),0);
  const b=k=>seen.reduce((n,x)=>n+(x.__binderStats?.[k]??0),0);
  const q=k=>seen.reduce((n,x)=>n+(x[k]??0),0);
  console.log("EXACT_CONTEXT_INFER_GIANT "+JSON.stringify({
    name,budget,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
    parse_records:r.parse_records??null,frontier:r.frontier_declaration??null,
    inferQueries:s("queries"),inferHits:s("hits"),inferMisses:s("misses"),inferStores:s("stores"),inferKeyEntries:s("keyEntries"),
    shiftHits:b("shiftHits"),substHits:b("substHits"),nodeHits:q("__compiledNodeHits"),spineHits:q("__compiledSpineHits"),
    theoremMajorUnfolds:q("__theoremMajorUnfolds"),theoremDeltaUnfolds:q("__theoremDeltaUnfolds"),
    nativeNatHits:q("__nativeNatHits"),ctorIdxHits:q("__ctorIdxHits"),elapsed_ms:Date.now()-t0
  }));
}
