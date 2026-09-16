import {readFileSync} from "node:fs";
import * as K from "./kernel.mjs";
await import("./closed-closure-conversion-layer.mjs");
const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const input=readFileSync(new URL("../_build/tests/perf/shared-subterm.ndjson",import.meta.url),"utf8");
const p=K.Kernel.prototype,seen=[],old=p.run;p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
const t0=Date.now();let r;try{r=K.checkExport(input,CAPS,1_000_000);}finally{p.run=old;}
const st={attempts:0,successes:0,aborts:0,ops:0,ctorPairs:0,whnfHits:0,recs:0,beta:0,abortOps:0,abortBeta:0,abortDefs:0,abortRecs:0,abortVars:0,abortApps:0,abortWhnfHits:0,abortWhnfStores:0};
let lastAbort=null;
for(const k of seen){for(const q of Object.keys(st))st[q]+=k.__closedClosureStats?.[q]??0;if(k.__closedClosureStats?.lastAbort)lastAbort=k.__closedClosureStats.lastAbort;}
console.log("CLOSED_CLOSURE_SHARED_FAST "+JSON.stringify({status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:Date.now()-t0,stats:st,lastAbort}));
if(r.status!=="ACCEPT")process.exit(1);
