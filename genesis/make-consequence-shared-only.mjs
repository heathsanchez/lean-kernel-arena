import {readFileSync} from "node:fs";
import * as K from "./kernel.mjs";
await import("./head-beta-spine-layer.mjs");
await import("./recursor-prefix-cache-layer.mjs");
await import("./compiled-dynamic-slot-layer.mjs");
await import("./recursor-core-first-layer.mjs");
await import("./make-consequence-cache-layer.mjs");

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems",
"proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives",
"inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals",
"quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const input=readFileSync(new URL("../_build/tests/perf/shared-subterm.ndjson",import.meta.url),"utf8");
const p=K.Kernel.prototype;
for(const budget of [1_000_000,2_000_000]){
 const seen=[],old=p.run;p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
 const t0=Date.now();let r;try{r=K.checkExport(input,CAPS,budget);}finally{p.run=old;}
 const core={splits:0,hits:0,stores:0,iterations:0,manualBeta:0,blocked:0};
 const make={hits:0,stores:0};const slot={queries:0,hits:0,prefixReused:0};
 for(const k of seen){
  for(const q of Object.keys(core))core[q]+=k.__recCoreStats?.[q]??0;
  for(const q of Object.keys(make))make[q]+=k.__makeConsequenceStats?.[q]??0;
  for(const q of Object.keys(slot))slot[q]+=k.__slotStats?.[q]??0;
 }
 console.log("MAKE_SHARED_ONLY "+JSON.stringify({budget,status:r.status,reason:r.reason,steps:r.steps??null,
   constructed:r.constructed??null,elapsed_ms:Date.now()-t0,core,make,slot}));
 if(r.status==="ACCEPT")process.exit(0);
}
process.exit(1);
