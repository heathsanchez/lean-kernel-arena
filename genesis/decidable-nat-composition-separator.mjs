import {readFileSync} from "node:fs";
import * as K from "./kernel.mjs";
import "./compiled-representation-reuse-layer.mjs";
import "./verified-ctoridx-consequence-layer.mjs";
import "./native-nat-reduction-layer.mjs";
import "./nat-offset-defeq-layer.mjs";
import "./exact-binder-transport-layer.mjs";
import "./compiled-le-nat-dictionary-layer.mjs";
import "./compiled-nat-class-reduction-layer.mjs";
import "./compiled-constant-decidable-nat-layer.mjs";
import "./compiled-nat-pow-layer.mjs";
import "./compiled-decidable-nat-composition-layer.mjs";
import "./compiled-nat-isvalidchar-consequence-layer.mjs";
import "./compiled-semantic-consequence-layer.mjs";

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
function run(name,path,want,budget=1_000_000){
 const input=readFileSync(new URL(path,import.meta.url),"utf8"),seen=[],p=K.Kernel.prototype,old=p.run;
 p.run=function(...xs){seen.push(this);return old.apply(this,xs);};let r;const t0=Date.now();
 try{r=K.checkExport(input,CAPS,budget);}finally{p.run=old;}
 const row={name,want,budget,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,frontier:r.frontier_declaration??null,
  decisionCompositionHits:seen.reduce((n,k)=>n+(k.__decisionCompositionHits??0),0),elapsed_ms:Date.now()-t0};
 console.log("DECIDABLE_NAT_COMPOSITION "+JSON.stringify(row));
 if(want&&r.status!==want)process.exitCode=1;
 return row;
}
run("shared-subterm","../_build/tests/perf/shared-subterm.ndjson","ACCEPT",1_000_000);
run("init-prelude","../_build/tests/init-prelude.ndjson",null,2_000_000);
run("grind-ring-5","../_build/tests/perf/grind-ring-5.ndjson",null,2_000_000);
