import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
const K=await import("file:///tmp/mathgraph-zero-nested/kernel.mjs");

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];

function recognizedEnvelope(b){
  const source=(b.types??[]).length===1?b.types[0]:null;
  if(!source||source.numParams!==0||source.numIndices!==0||source.isUnsafe!==false||
     !Array.isArray(source.levelParams)||source.levelParams.length!==0||
     !Number.isSafeInteger(source.numNested)||source.numNested<=0)return false;
  const recs=b.recs??[],ruleIds=recs.flatMap(r=>(r?.rules??[]).map(rr=>rr?.ctor));
  if(recs.length!==1+source.numNested||new Set(ruleIds).size!==ruleIds.length)return false;
  return recs.every(r=>r&&r.numParams===0&&r.numIndices===0&&r.numMotives===recs.length&&
    r.numMinors===ruleIds.length&&r.k===false&&r.isUnsafe===false);
}
function rewrite(input){
  const out=[];let rewritten=0;
  for(const line of input.split(/\r?\n/)){
    if(!line.trim())continue;
    const row=JSON.parse(line),b=row.inductive;
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
    const snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};
    let x,y;
    try{x=this.normal(a);y=this.normal(b);}
    catch(_){this.steps=snap.steps;this.budget=snap.budget;this.conversionFrontier=snap.frontier;throw original;}
    if(!Array.isArray(x)||!Array.isArray(y)||x[0]!=="proj"||y[0]!=="proj"||x[1]!==y[1]||x[2]!==y[2]){
      this.steps=snap.steps;this.budget=snap.budget;this.conversionFrontier=snap.frontier;throw original;
    }
    this.__projRecoveryDepth=(this.__projRecoveryDepth??0)+1;
    try{this.equal(x[3],y[3],ctx);this.__projRecoveryDepth--;return;}
    catch(e){
      this.__projRecoveryDepth--;
      if(!(e instanceof K.Stop||e instanceof RangeError))throw e;
      this.steps=snap.steps;this.budget=snap.budget;this.conversionFrontier=snap.frontier;throw original;
    }
  }
};

const methods=["shift","substitute","whnf","same","normal","equal","instantiateDeclaration","infer","getApp","make","appN"];
for(const name of methods){
  const orig=p[name];if(typeof orig!=="function")continue;
  p[name]=function(...args){
    this.__giantProf??={stack:[],ticks:{},calls:{}};
    const q=this.__giantProf;q.calls[name]=(q.calls[name]??0)+1;q.stack.push(name);
    try{return orig.apply(this,args);}finally{q.stack.pop();}
  };
}
const tick0=p.tick,run0=p.run;
p.tick=function(...args){
  this.__giantProf??={stack:[],ticks:{},calls:{}};
  const q=this.__giantProf,top=q.stack.at(-1)??"<none>";
  q.ticks[top]=(q.ticks[top]??0)+1;
  return tick0.apply(this,args);
};

const CASES=["init-prelude","perf/grind-ring-5"],rows=[];
for(const name of CASES){
  const seen=[],oldRun=p.run;
  p.run=function(...xs){seen.push(this);return oldRun.apply(this,xs);};
  const rw=rewrite(readFileSync("_build/tests/"+name+".ndjson","utf8")),t0=Date.now();
  let r;
  try{r=K.checkExport(rw.text,CAPS,1_000_000);}finally{p.run=oldRun;}
  const merged={ticks:{},calls:{}};
  for(const k of seen){
    const q=k.__giantProf??{ticks:{},calls:{}};
    for(const [n,v] of Object.entries(q.ticks))merged.ticks[n]=(merged.ticks[n]??0)+v;
    for(const [n,v] of Object.entries(q.calls))merged.calls[n]=(merged.calls[n]??0)+v;
  }
  const top=Object.keys(merged.ticks).map(op=>({op,ticks:merged.ticks[op],calls:merged.calls[op]??0,
    avg:merged.ticks[op]/Math.max(1,merged.calls[op]??1)})).sort((a,b)=>b.ticks-a.ticks);
  const row={name,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
    frontier_declaration:r.frontier_declaration??null,rewritten:rw.rewritten,elapsed_ms:Date.now()-t0,top:top.slice(0,16)};
  rows.push(row);console.log("ROW "+JSON.stringify(row));
}
const out={experiment:"post-semantics-giant-hotspot",rows};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/post-semantics-giant-hotspot.json",JSON.stringify(out,null,2)+"\n");
console.log("POST_SEMANTICS_GIANT_HOTSPOT "+JSON.stringify(out));
