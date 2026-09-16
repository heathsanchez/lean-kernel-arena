import {readFileSync} from "node:fs";
import * as K from "./kernel.mjs";
import "./native-nat-reduction-layer.mjs";
import "./nat-offset-defeq-layer.mjs";
const CAPS=["sort","binders","application","reduction","declarations","universes","theorems",
"proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives",
"inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals",
"quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
function head(e){let h=e,args=0;while(Array.isArray(h)&&h[0]==="app"){args++;h=h[1];}
  return Array.isArray(h)?{tag:h[0],name:h[0]==="const"?h[1]:null,args}:{tag:typeof h,args};}
for(const name of ["init-prelude","perf/grind-ring-5","perf/shared-subterm"]){
  const seen=[],p=K.Kernel.prototype,run0=p.run,eq0=p.equal;
  p.run=function(...xs){seen.push(this);return run0.apply(this,xs);};
  p.equal=function(a,b,ctx=[]){
    try{return eq0.call(this,a,b,ctx);}
    catch(e){
      if(e?.message==="rigid-head-mismatch"&&!this.__nativeReject){
        this.__nativeReject={step:this.steps,ctxDepth:ctx.length,aHead:head(a),bHead:head(b),
          aBytes:JSON.stringify(a).length,bBytes:JSON.stringify(b).length,
          a:JSON.stringify(a).slice(0,7000),b:JSON.stringify(b).slice(0,7000)};
      }
      throw e;
    }
  };
  const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
  const t0=Date.now();let r;
  try{r=K.checkExport(input,CAPS,1_000_000);}finally{p.run=run0;p.equal=eq0;}
  console.log("NATIVE_NAT_SEPARATOR "+JSON.stringify({
    name,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
    parse_records:r.parse_records??null,frontier:r.frontier_declaration??null,
    nativeNatHits:seen.reduce((n,x)=>n+(x.__nativeNatHits??0),0),
    reject:seen.find(x=>x.__nativeReject)?.__nativeReject??null,elapsed_ms:Date.now()-t0
  }));
}
