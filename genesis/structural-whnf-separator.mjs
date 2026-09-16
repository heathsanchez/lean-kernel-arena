import {readFileSync} from "node:fs";
import * as K from "./kernel.mjs";
import "./compiled-representation-reuse-layer.mjs";
import "./verified-ctoridx-consequence-layer.mjs";
import "./native-nat-reduction-layer.mjs";
import "./nat-offset-defeq-layer.mjs";
import "./exact-binder-transport-layer.mjs";
import "./compiled-semantic-consequence-layer.mjs";
import "./structural-whnf-consequence-layer.mjs";

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
 const s={hits:0,stores:0,skipped:0,keyBytes:0,maxKeyBytes:0};
 for(const k of seen){const q=k.__structWhnfStats??{};for(const n of ["hits","stores","skipped","keyBytes"])s[n]+=q[n]??0;s.maxKeyBytes=Math.max(s.maxKeyBytes,q.maxKeyBytes??0);}
 console.log("STRUCTURAL_WHNF_SEPARATOR "+JSON.stringify({
  name,budget,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
  parse_records:r.parse_records??null,frontier:r.frontier_declaration??null,structWhnf:s,
  semWhnfHits:seen.reduce((n,k)=>n+(k.__semStats?.whnfHits??0),0),
  semWhnfStores:seen.reduce((n,k)=>n+(k.__semStats?.whnfStores??0),0),
  nodeHits:seen.reduce((n,k)=>n+(k.__compiledNodeHits??0),0),
  spineHits:seen.reduce((n,k)=>n+(k.__compiledSpineHits??0),0),
  elapsed_ms:Date.now()-t0
 }));
}
