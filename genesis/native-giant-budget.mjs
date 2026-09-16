import {readFileSync} from "node:fs";
import * as K from "./kernel.mjs";
import "./verified-ctoridx-consequence-layer.mjs";
import "./native-nat-reduction-layer.mjs";
import "./nat-offset-defeq-layer.mjs";
const CAPS=["sort","binders","application","reduction","declarations","universes","theorems",
"proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives",
"inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals",
"quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
for(const name of ["init-prelude","perf/grind-ring-5"]){
 const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
 for(const budget of [1500000,2500000,4000000]){
   const t0=Date.now(),r=K.checkExport(input,CAPS,budget);
   console.log("NATIVE_GIANT_BUDGET "+JSON.stringify({name,budget,status:r.status,reason:r.reason,steps:r.steps??null,
     constructed:r.constructed??null,frontier:r.frontier_declaration??null,elapsed_ms:Date.now()-t0}));
   if(r.status!=="UNKNOWN")break;
 }
}