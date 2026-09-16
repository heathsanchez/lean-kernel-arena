import {readFileSync} from "node:fs";
import * as K from "./kernel.mjs";
import "./compiled-representation-reuse-layer.mjs";
import "./verified-ctoridx-consequence-layer.mjs";
import "./native-nat-reduction-layer.mjs";
import "./nat-offset-defeq-layer.mjs";
import "./exact-binder-transport-layer.mjs";
import "./compiled-semantic-consequence-layer.mjs";
import "./compiled-le-nat-dictionary-layer.mjs";
import "./lazy-congruence-conversion-layer.mjs";

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems",
"proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives",
"inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals",
"quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];

for(const [name,budget] of [
 ["init-prelude",1_000_000],["perf/grind-ring-5",1_000_000],["perf/shared-subterm",1_000_000],
 ["init-prelude",4_000_000],["perf/grind-ring-5",4_000_000]
]){
 const seen=[],p=K.Kernel.prototype,run0=p.run;
 p.run=function(...xs){seen.push(this);return run0.apply(this,xs);};
 const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
 const t0=Date.now();let r;
 try{r=K.checkExport(input,CAPS,budget);}finally{p.run=run0;}
 const q={attempts:0,headSame:0,app:0,pi:0,lam:0,proj:0,fallbacks:0,whnfSame:0};
 for(const k of seen)for(const [n,v] of Object.entries(k.__lazyConvStats??{}))q[n]+=v;
 console.log("LAZY_CONGRUENCE_SEPARATOR "+JSON.stringify({
  name,budget,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
  parse_records:r.parse_records??null,frontier:r.frontier_declaration??null,lazy:q,
  leNatHits:seen.reduce((n,k)=>n+(k.__compiledLENatHits??0),0),
  nodeHits:seen.reduce((n,k)=>n+(k.__compiledNodeHits??0),0),
  spineHits:seen.reduce((n,k)=>n+(k.__compiledSpineHits??0),0),
  elapsed_ms:Date.now()-t0
 }));
}
