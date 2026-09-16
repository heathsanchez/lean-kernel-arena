import {readFileSync} from "node:fs";
import * as K from "./kernel.mjs";
import "./compiled-representation-reuse-layer.mjs";
import "./verified-ctoridx-consequence-layer.mjs";
import "./native-nat-reduction-layer.mjs";
import "./nat-offset-defeq-layer.mjs";
import "./exact-binder-transport-layer.mjs";
import "./compiled-le-nat-dictionary-layer.mjs";
import "./compiled-nat-class-reduction-layer.mjs";
import "./compiled-nat-isvalidchar-consequence-layer.mjs";
import "./compiled-semantic-consequence-layer.mjs";

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems",
"proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives",
"inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals",
"quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];

function head(e){let h=e,n=0;while(Array.isArray(h)&&h[0]==="app"){n++;h=h[1];}
 return Array.isArray(h)?{tag:h[0],name:h[0]==="const"?h[1]:null,args:n}:{tag:typeof h,args:n};}
function sk(e,d=6){
 if(!Array.isArray(e))return e;if(d<=0)return ["…",e[0]];
 if(e[0]==="const")return ["const",e[1],e[2]??[]];
 if(e[0]==="var")return ["v",e[1]];
 if(e[0]==="sort")return ["sort",e[1]];
 if(e[0]==="nat")return ["nat",e[1]];
 if(e[0]==="proj")return ["proj",e[1],e[2],sk(e[3],d-1)];
 return [e[0],...e.slice(1).map(x=>sk(x,d-1))];
}
function prettyName(s){
 try{
   let x=JSON.parse(s),parts=[];
   while(Array.isArray(x)&&x.length===3){parts.push(String(x[2]));x=JSON.parse(x[0]);}
   return parts.reverse().join(".");
 }catch{return String(s);}
}
function parentDecl(s){
 const p=prettyName(s);
 return p.endsWith("isValidChar_UInt32")&&!p.includes("match_");
}

const p=K.Kernel.prototype,eq0=p.equal,run0=p.run;
p.run=function(...xs){this.__parentSlow=[];return run0.apply(this,xs);};
p.equal=function(a,b,ctx=[]){
 if(!parentDecl(this.currentDeclaration))return eq0.call(this,a,b,ctx);
 const start=this.steps;
 try{
   const out=eq0.call(this,a,b,ctx),cost=this.steps-start;
   if(cost>=5000){
     const ab=JSON.stringify(a),bb=JSON.stringify(b);
     this.__parentSlow.push({cost,result:"ok",step:start,ctxDepth:ctx.length,aHead:head(a),bHead:head(b),
       aBytes:ab.length,bBytes:bb.length,aSk:sk(a),bSk:sk(b),aPrefix:ab.slice(0,2500),bPrefix:bb.slice(0,2500)});
     this.__parentSlow.sort((x,y)=>y.cost-x.cost);this.__parentSlow.length=Math.min(12,this.__parentSlow.length);
   }
   return out;
 }catch(e){
   const cost=this.steps-start;
   if(cost>=5000){
     const ab=JSON.stringify(a),bb=JSON.stringify(b);
     this.__parentSlow.push({cost,result:e?.message??String(e),step:start,ctxDepth:ctx.length,aHead:head(a),bHead:head(b),
       aBytes:ab.length,bBytes:bb.length,aSk:sk(a),bSk:sk(b),aPrefix:ab.slice(0,2500),bPrefix:bb.slice(0,2500)});
     this.__parentSlow.sort((x,y)=>y.cost-x.cost);this.__parentSlow.length=Math.min(12,this.__parentSlow.length);
   }
   throw e;
 }
};
const result0=p.result;
p.result=function(...xs){const r=result0.apply(this,xs);r.__parentSlow=this.__parentSlow??[];return r;};

for(const name of ["init-prelude","perf/grind-ring-5"]){
 const input=readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");
 const t0=Date.now(),r=K.checkExport(input,CAPS,1_000_000);
 console.log("ISVALIDCHAR_UINT32_PARENT_PROFILE "+JSON.stringify({name,status:r.status,reason:r.reason,steps:r.steps??null,
   frontier:r.frontier_declaration??null,rows:r.__parentSlow,elapsed_ms:Date.now()-t0}));
}
