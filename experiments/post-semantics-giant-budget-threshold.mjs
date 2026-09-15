import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
const K=await import("file:///tmp/mathgraph-zero-nested/kernel.mjs");
const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];

function recognizedEnvelope(b){
 const source=(b.types??[]).length===1?b.types[0]:null;
 if(!source||source.numParams!==0||source.numIndices!==0||source.isUnsafe!==false||
    !Array.isArray(source.levelParams)||source.levelParams.length!==0||
    !Number.isSafeInteger(source.numNested)||source.numNested<=0)return false;
 const recs=b.recs??[],ids=recs.flatMap(r=>(r?.rules??[]).map(rr=>rr?.ctor));
 return recs.length===1+source.numNested&&new Set(ids).size===ids.length&&
   recs.every(r=>r&&r.numParams===0&&r.numIndices===0&&r.numMotives===recs.length&&r.numMinors===ids.length&&r.k===false&&r.isUnsafe===false);
}
function rewrite(input){
 const out=[];let rewritten=0;
 for(const line of input.split(/\r?\n/)){
  if(!line.trim())continue;const row=JSON.parse(line),b=row.inductive;
  if(!b||!recognizedEnvelope(b)){out.push(line);continue;}
  const source=b.types[0];
  out.push(JSON.stringify({axiom:{name:source.name,levelParams:source.levelParams??[],type:source.type,isUnsafe:false}}));
  for(const c of b.ctors??[])out.push(JSON.stringify({axiom:{name:c.name,levelParams:c.levelParams??[],type:c.type,isUnsafe:false}}));
  for(const r of b.recs??[])out.push(JSON.stringify({axiom:{name:r.name,levelParams:r.levelParams??[],type:r.type,isUnsafe:false}}));
  rewritten++;
 }
 return {text:out.join("\n")+"\n",rewritten};
}
const p=K.Kernel.prototype,retainedEqual=p.equal;
p.equal=function(a,b,ctx=[]){
 if((this.__projRecoveryDepth??0)>16)return retainedEqual.call(this,a,b,ctx);
 try{return retainedEqual.call(this,a,b,ctx);}
 catch(original){
  if(!(original instanceof K.Stop)||original.status!=="UNKNOWN"||original.message!=="conversion-frontier")throw original;
  const snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};let x,y;
  try{x=this.normal(a);y=this.normal(b);}catch(_){this.steps=snap.steps;this.budget=snap.budget;this.conversionFrontier=snap.frontier;throw original;}
  if(!Array.isArray(x)||!Array.isArray(y)||x[0]!=="proj"||y[0]!=="proj"||x[1]!==y[1]||x[2]!==y[2]){
   this.steps=snap.steps;this.budget=snap.budget;this.conversionFrontier=snap.frontier;throw original;
  }
  this.__projRecoveryDepth=(this.__projRecoveryDepth??0)+1;
  try{this.equal(x[3],y[3],ctx);this.__projRecoveryDepth--;return;}
  catch(e){this.__projRecoveryDepth--;if(!(e instanceof K.Stop||e instanceof RangeError))throw e;
   this.steps=snap.steps;this.budget=snap.budget;this.conversionFrontier=snap.frontier;throw original;}
 }
};
const inputs={};
for(const name of ["init-prelude","perf/grind-ring-5"])inputs[name]=rewrite(readFileSync("_build/tests/"+name+".ndjson","utf8")).text;
const rows=[];
for(const budget of [1000000,1500000,2000000,3000000,4000000]){
 for(const name of Object.keys(inputs)){
  const t0=Date.now(),r=K.checkExport(inputs[name],CAPS,budget);
  const row={budget,name,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
   frontier_declaration:r.frontier_declaration??null,elapsed_ms:Date.now()-t0};
  rows.push(row);console.log("ROW "+JSON.stringify(row));
 }
 if(rows.slice(-2).every(r=>r.status==="ACCEPT"))break;
}
const out={experiment:"post-semantics-giant-budget-threshold",rows};
mkdirSync("genesis/evidence",{recursive:true});writeFileSync("genesis/evidence/post-semantics-giant-budget-threshold.json",JSON.stringify(out,null,2)+"\n");
console.log("POST_SEMANTICS_GIANT_BUDGET_THRESHOLD "+JSON.stringify(out));
