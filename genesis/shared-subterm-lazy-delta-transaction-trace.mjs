import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";
const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const p=K.Kernel.prototype,oldRun=p.run;const seen=[];
p.run=function(...xs){seen.push(this);return oldRun.apply(this,xs);};
const input=readFileSync(new URL("../_build/tests/perf/shared-subterm.ndjson",import.meta.url),"utf8");
const result=K.checkExport(input,CAPS,1_000_000);p.run=oldRun;
const kernels=seen.map(k=>({steps:k.steps,localDefs:k.localDefs===true,starts:k.__lazyDeltaTopStarts??0,
 successes:k.__lazyDeltaTopSuccesses??0,failures:k.__lazyDeltaTopFailures??0,
 lastSuccess:k.__lazyDeltaLastSuccess??null,lastFailure:k.__lazyDeltaLastFailure??null,lastPair:k.__lazyDeltaLastPair??null}));
const out={experiment:"shared-subterm-lazy-delta-transaction-trace",result,kernels};
mkdirSync("genesis/evidence",{recursive:true});writeFileSync("genesis/evidence/shared-subterm-lazy-delta-transaction-trace.json",JSON.stringify(out,null,2)+"\n");
console.log("SHARED_SUBTERM_LAZY_DELTA_TRANSACTION_TRACE "+JSON.stringify(out));
