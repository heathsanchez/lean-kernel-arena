import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const p=K.Kernel.prototype, oldRun=p.run, oldEqual=p.equal, oldNormal=p.normal;
const seen=[];
function shape(e,k=null){
  if(!Array.isArray(e))return {scalar:typeof e};
  let h=e,n=0;
  while(Array.isArray(h)&&h[0]==="app"){n++;h=h[1];}
  const head=Array.isArray(h)?(h[0]==="const"?["const",h[1]]:h.slice(0,2)):typeof h;
  const kind=Array.isArray(h)&&h[0]==="const"&&k ? (k.env.get(h[1])?.kind??null) : null;
  return {tag:e[0],head,args:n,kind};
}
p.run=function(...xs){seen.push(this);this.__frontierSamples=[];return oldRun.apply(this,xs);};
p.equal=function(a,b,ctx=[]){
  if(this.steps>=850000 && (this.__frontierSamples?.length??0)<40)
    this.__frontierSamples.push({op:"equal",steps:this.steps,decl:this.currentDeclaration,ctx:ctx.length,a:shape(a,this),b:shape(b,this)});
  this.__lastEqual={steps:this.steps,decl:this.currentDeclaration,ctx:ctx.length,a:shape(a,this),b:shape(b,this)};
  return oldEqual.call(this,a,b,ctx);
};
p.normal=function(e){
  if(this.steps>=850000 && (this.__frontierSamples?.length??0)<40)
    this.__frontierSamples.push({op:"normal",steps:this.steps,decl:this.currentDeclaration,e:shape(e,this)});
  this.__lastNormal={steps:this.steps,decl:this.currentDeclaration,e:shape(e,this)};
  return oldNormal.call(this,e);
};
const input=readFileSync(new URL("../_build/tests/perf/shared-subterm.ndjson",import.meta.url),"utf8");
const result=K.checkExport(input,CAPS,1_000_000);
p.run=oldRun;p.equal=oldEqual;p.normal=oldNormal;
const kernels=seen.map(k=>({steps:k.steps,decl:k.currentDeclaration,lastEqual:k.__lastEqual,lastNormal:k.__lastNormal,samples:k.__frontierSamples}));
const out={experiment:"shared-subterm-budget-frontier",result,kernels};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/shared-subterm-budget-frontier.json",JSON.stringify(out,null,2)+"\n");
console.log("SHARED_SUBTERM_BUDGET_FRONTIER "+JSON.stringify(out));
