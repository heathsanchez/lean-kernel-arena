import {readFileSync} from "node:fs";
import * as K from "./kernel.mjs";
import "./native-nat-reduction-layer.mjs";
const CAPS=["sort","binders","application","reduction","declarations","universes","theorems",
"proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives",
"inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals",
"quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
for(const name of ["init-prelude","perf/grind-ring-5","perf/shared-subterm"]){
  const seen=[],p=K.Kernel.prototype,run0=p.run;
  p.run=function(...xs){seen.push(this);return run0.apply(this,xs);};
  const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
  const t0=Date.now();let r;
  try{r=K.checkExport(input,CAPS,1_000_000);}finally{p.run=run0;}
  console.log("NATIVE_NAT_SEPARATOR "+JSON.stringify({
    name,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
    parse_records:r.parse_records??null,frontier:r.frontier_declaration??null,
    nativeNatHits:seen.reduce((n,x)=>n+(x.__nativeNatHits??0),0),elapsed_ms:Date.now()-t0
  }));
}
