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
import "./projection-closure-consequence-layer.mjs";

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const p=K.Kernel.prototype,result0=p.result;
p.result=function(...xs){const r=result0.apply(this,xs);r.__projectionClosure=this.__projectionClosure??null;return r;};

for(const name of ["init-prelude","perf/grind-ring-5","perf/shared-subterm"]){
  const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
  const r=K.checkExport(input,CAPS,1_000_000);
  console.log("PROJECTION_CLOSURE_SEPARATOR "+JSON.stringify({name,status:r.status,reason:r.reason,
    steps:r.steps??null,frontier:r.frontier_declaration??null,stats:r.__projectionClosure}));
}
