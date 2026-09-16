import {readFileSync} from "node:fs";
import * as K from "./kernel.mjs";
await import("./head-beta-spine-layer.mjs");
await import("./recursor-prefix-cache-layer.mjs");
await import("./compiled-dynamic-slot-layer.mjs"); // supplies exact support metadata
await import("./support-pruned-substitution-layer.mjs");
await import("./recursor-core-first-layer.mjs");

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems",
"proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives",
"inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals",
"quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const input=readFileSync(new URL("../_build/tests/perf/shared-subterm.ndjson",import.meta.url),"utf8");
const p=K.Kernel.prototype;
for(const budget of [1_000_000,2_000_000]){
 const seen=[],old=p.run;p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
 const t0=Date.now();let r;try{r=K.checkExport(input,CAPS,budget);}finally{p.run=old;}
 const sub={pruned:0,cacheHits:0,visits:0,builds:0},core={splits:0,hits:0,stores:0,iterations:0,manualBeta:0,blocked:0};
 for(const k of seen){
  for(const q of Object.keys(sub))sub[q]+=k.__supportSubStats?.[q]??0;
  for(const q of Object.keys(core))core[q]+=k.__recCoreStats?.[q]??0;
 }
 console.log("SUPPORT_PRUNED_SHARED "+JSON.stringify({budget,status:r.status,reason:r.reason,steps:r.steps??null,
   constructed:r.constructed??null,elapsed_ms:Date.now()-t0,sub,core}));
 if(r.status==="ACCEPT")process.exit(0);
}
process.exit(1);
