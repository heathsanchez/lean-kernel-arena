import {readFileSync} from "node:fs";
import * as K from "./kernel.mjs";
import "./compiled-representation-reuse-layer.mjs";
import "./verified-ctoridx-consequence-layer.mjs";
import "./native-nat-reduction-layer.mjs";
import "./nat-offset-defeq-layer.mjs";
import "./exact-binder-transport-layer.mjs";
import "./compiled-le-nat-dictionary-layer.mjs";
import "./whnf-congruence-before-normal-layer.mjs";
import "./compiled-semantic-consequence-layer.mjs";

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems",
"proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives",
"inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals",
"quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];

function head(e){let h=e,n=0;while(Array.isArray(h)&&h[0]==="app"){n++;h=h[1];}
 return Array.isArray(h)?{tag:h[0],name:h[0]==="const"?h[1]:null,args:n}:{tag:typeof h,args:n};}
function firstDiff(a,b,path="$",depth=0){
 if(a===b)return null;if(depth>1000)return {path,kind:"depth"};
 if(Array.isArray(a)!==Array.isArray(b))return {path,kind:"array"};
 if(!Array.isArray(a))return {path,kind:"scalar",a,b};
 if(a.length!==b.length)return {path:path+".length",kind:"length",a:a.length,b:b.length};
 for(let i=0;i<a.length;i++){const d=firstDiff(a[i],b[i],path+"["+i+"]",depth+1);if(d)return d;}
 return null;
}

const p=K.Kernel.prototype,eq0=p.equal,run0=p.run;
p.run=function(...xs){this.__eqLtReject=[];return run0.apply(this,xs);};
p.equal=function(a,b,ctx=[]){
 try{return eq0.call(this,a,b,ctx);}
 catch(e){
   if(e?.status==="REJECT"&&typeof this.currentDeclaration==="string"&&this.currentDeclaration.includes("eq_or_lt_of_le")){
     const ab=JSON.stringify(a),bb=JSON.stringify(b);
     this.__eqLtReject??=[];
     this.__eqLtReject.push({reason:e.message,step:this.steps,ctxDepth:ctx.length,
       aHead:head(a),bHead:head(b),aBytes:ab.length,bBytes:bb.length,
       firstDiff:firstDiff(a,b),aPrefix:ab.slice(0,5000),bPrefix:bb.slice(0,5000)});
   }
   throw e;
 }
};
const result0=p.result;
p.result=function(...xs){const r=result0.apply(this,xs);r.__eqLtReject=(this.__eqLtReject??[]).slice(-12);return r;};

for(const name of ["init-prelude","perf/grind-ring-5"]){
 const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
 const t0=Date.now(),r=K.checkExport(input,CAPS,500_000);
 console.log("EQ_OR_LT_REJECT_PROFILE "+JSON.stringify({name,status:r.status,reason:r.reason,steps:r.steps??null,
  frontier:r.frontier_declaration??null,rows:r.__eqLtReject,elapsed_ms:Date.now()-t0}));
}
