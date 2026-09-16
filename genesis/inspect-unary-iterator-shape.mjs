import {readFileSync} from "node:fs";
import * as K from "./kernel.mjs";

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems",
"proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives",
"inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals",
"quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];

const input=readFileSync(new URL("../_build/tests/perf/shared-subterm.ndjson",import.meta.url),"utf8");
const p=K.Kernel.prototype,seen=[],old=p.run;
p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
try{K.checkExport(input,CAPS,100000);}finally{p.run=old;}

function rawSpine(e){const args=[];let h=e;while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}args.reverse();return{h,args};}
for(const k of seen){
  for(const [name,d] of k.env??[]){
    if(d?.kind!=="def"||!String(name).includes("add"))continue;
    let e=d.value,outer=[];
    while(Array.isArray(e)&&e[0]==="lam"){outer.push(e[1]);e=e[2];}
    const s=rawSpine(e),rd=Array.isArray(s.h)&&s.h[0]==="const"?k.env.get(s.h[1]):null;
    console.log("ITERATOR_SHAPE "+JSON.stringify({
      name,defLevels:d.levelParams??[],outerBinders:outer.length,
      bodyHead:s.h,bodyArgs:s.args,recMeta:rd?{
        name:rd.name,kind:rd.kind,levelParams:rd.levelParams??[],numParams:rd.numParams,
        numIndices:rd.numIndices,numMinors:rd.numMinors,induct:rd.induct
      }:null
    }));
  }
}
