import {readFileSync} from "node:fs";
import * as K from "./kernel.mjs";
import "./exact-whnf-cache-layer.mjs";

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems",
"proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives",
"inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals",
"quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];

const TARGETS=["init-prelude","perf/grind-ring-5"];
const p=K.Kernel.prototype,oldRun=p.run;
for(const name of TARGETS){
  const seen=[];
  p.run=function(...xs){seen.push(this);return oldRun.apply(this,xs);};
  const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
  const t0=Date.now();let r;
  try{r=K.checkExport(input,CAPS,1_000_000);}finally{p.run=oldRun;}
  const hits=seen.reduce((n,k)=>n+(k.__whnfExactHits??0),0);
  const stores=seen.reduce((n,k)=>n+(k.__whnfExactStores??0),0);
  console.log("GIANT_EXACT_WHNF "+JSON.stringify({name,status:r.status,reason:r.reason,
    steps:r.steps??null,constructed:r.constructed??null,frontier:r.frontier_declaration??null,
    hits,stores,elapsed_ms:Date.now()-t0}));
}
