import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
const K=await import("file:///tmp/mathgraph-zero-nested/kernel.mjs");
const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];

function recognizedEnvelope(b){
 const source=(b.types??[]).length===1?b.types[0]:null;
 if(!source||source.numParams!==0||source.numIndices!==0||source.isUnsafe!==false||
    !Array.isArray(source.levelParams)||source.levelParams.length!==0||
    !Number.isSafeInteger(source.numNested)||source.numNested<=0)return false;
 const recs=b.recs??[],ruleIds=recs.flatMap(r=>(r?.rules??[]).map(rr=>rr?.ctor));
 return recs.length===1+source.numNested&&new Set(ruleIds).size===ruleIds.length&&
   recs.every(r=>r&&r.numParams===0&&r.numIndices===0&&r.numMotives===recs.length&&r.numMinors===ruleIds.length&&r.k===false&&r.isUnsafe===false);
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
function firstDiff(a,b){
 const stack=[{a,b,path:"$"}];let common=0;
 while(stack.length){
  const q=stack.pop(),x=q.a,y=q.b;
  if(x===y){common++;continue;}
  if(!Array.isArray(x)||!Array.isArray(y))
    return {path:q.path,left:x,right:y,common};
  if(x.length!==y.length||x[0]!==y[0])
    return {path:q.path,leftTag:x[0],rightTag:y[0],leftLen:x.length,rightLen:y.length,common,
      left:JSON.stringify(x).slice(0,800),right:JSON.stringify(y).slice(0,800)};
  for(let i=x.length-1;i>=1;i--)stack.push({a:x[i],b:y[i],path:q.path+"["+i+"]"});
  common++;
 }
 return {equal:true,common};
}
function nodeCount(root){
 let n=0;const st=[root];while(st.length){const e=st.pop();n++;if(Array.isArray(e))for(let i=1;i<e.length;i++)if(Array.isArray(e[i]))st.push(e[i]);}return n;
}

const p=K.Kernel.prototype,run0=p.run,equal0=p.equal,kernels=[];
p.run=function(...args){kernels.push(this);return run0.apply(this,args);};
p.equal=function(a,b,ctx=[]){
 try{return equal0.call(this,a,b,ctx);}
 catch(e){
  if(e?.message==="conversion-frontier"&&!this.__fullConvCapture)
    this.__fullConvCapture={a,b,ctxDepth:ctx.length,atSteps:this.steps};
  throw e;
 }
};

const input=readFileSync("_build/tests/perf/grind-ring-5.ndjson","utf8"),rw=rewrite(input),t0=Date.now();
const r=K.checkExport(rw.text,CAPS,1_000_000);
const captures=[];
for(const [index,k] of kernels.entries()){
 const c=k.__fullConvCapture;if(!c)continue;
 const oldBudget=k.budget;k.budget=Math.max(oldBudget,k.steps+4_000_000);
 let x,y,diag;
 try{
  x=k.normal(c.a);y=k.normal(c.b);
  diag={index,localDefs:k.localDefs===true,atSteps:c.atSteps,ctxDepth:c.ctxDepth,
    leftBytes:JSON.stringify(x).length,rightBytes:JSON.stringify(y).length,
    leftNodes:nodeCount(x),rightNodes:nodeCount(y),diff:firstDiff(x,y)};
 }catch(e){diag={index,localDefs:k.localDefs===true,error:String(e?.stack??e).slice(0,1200)};}
 captures.push(diag);
}
const out={experiment:"grind-post-nested-conversion-diff",status:r.status,reason:r.reason,steps:r.steps??null,
 constructed:r.constructed??null,frontier_declaration:r.frontier_declaration??null,rewritten:rw.rewritten,
 elapsed_ms:Date.now()-t0,captures};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/grind-post-nested-conversion-diff.json",JSON.stringify(out,null,2)+"\n");
console.log("GRIND_POST_NESTED_CONVERSION_DIFF "+JSON.stringify(out));
if(!captures.length)process.exit(1);
