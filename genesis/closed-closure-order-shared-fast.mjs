import {readFileSync} from "node:fs";
import * as K from "./kernel-closure-order.mjs";

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems",
"proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives",
"inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals",
"quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];

const input=readFileSync(new URL("../_build/tests/perf/shared-subterm.ndjson",import.meta.url),"utf8");
const p=K.Kernel.prototype,seen=[],old=p.run;
p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
const t0=Date.now();let r;
try{r=K.checkExport(input,CAPS,1_000_000);}finally{p.run=old;}
const events=[],stats={attempts:0,successes:0,aborts:0,ops:0,ctorPairs:0,whnfHits:0,recs:0,beta:0,eqHits:0,eqStores:0};
for(const k of seen){
  const s=k.__closedClosureStats??{};
  for(const q of Object.keys(stats))stats[q]+=s[q]??0;
  events.push(...(s.events??[]));
}
console.log("CLOSED_CLOSURE_ORDER_SHARED "+JSON.stringify({
  status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
  elapsed_ms:Date.now()-t0,stats,events
}));
if(r.status!=="ACCEPT")process.exit(1);
