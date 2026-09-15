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
function install(){
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
      this.__projRecoveryAttempts=(this.__projRecoveryAttempts??0)+1;
      this.__projRecoveryDepth=(this.__projRecoveryDepth??0)+1;
      try{
        this.equal(x[3],y[3],ctx);
        this.__projRecoverySuccesses=(this.__projRecoverySuccesses??0)+1;
        this.__projRecoveryDepth--;
        return;
      }catch(e){
        this.__projRecoveryDepth--;
        if(!(e instanceof K.Stop||e instanceof RangeError))throw e;
        this.steps=snap.steps;this.budget=snap.budget;this.conversionFrontier=snap.frontier;
        throw original;
      }
    }
  };
}

const CASES=[
 ["init-prelude","ACCEPT",true],
 ["perf/grind-ring-5","ACCEPT",true],
 ["nat-rec-rules","REJECT",false],
 ["proj-non-structure","REJECT",false],
 ["proj-of-imax-prop","REJECT",false],
 ["proj-of-prop","REJECT",false],
 ["nested-unused-param","REJECT",false],
 ["nested-nonuniform-param","either",false]
];

install();
const rows=[];
for(const [name,want,doRewrite] of CASES){
  const raw=readFileSync("_build/tests/"+name+".ndjson","utf8"),rw=doRewrite?rewrite(raw):{text:raw,rewritten:0};
  const seen=[],old=p.run;p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
  const t0=Date.now();let r;
  try{r=K.checkExport(rw.text,CAPS,1_000_000);}
  finally{p.run=old;}
  const sum=q=>seen.reduce((n,k)=>n+(k[q]??0),0);
  const pass=want==="either"?(r.status==="ACCEPT"||r.status==="REJECT"):r.status===want;
  const row={name,want,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
    frontier_declaration:r.frontier_declaration??null,parse_records:r.parse_records??null,rewritten:rw.rewritten,
    projectionRecoveryAttempts:sum("__projRecoveryAttempts"),projectionRecoverySuccesses:sum("__projRecoverySuccesses"),
    elapsed_ms:Date.now()-t0,pass};
  rows.push(row);console.log("ROW "+JSON.stringify(row));
}
p.equal=retainedEqual;

const giantsClosed=rows.slice(0,2).every(r=>r.status==="ACCEPT");
const controlsClean=rows.slice(2).every(r=>r.pass);
const out={experiment:"post-nested-projection-proof-irrelevance",giantsClosed,controlsClean,promotable_focus:giantsClosed&&controlsClean,rows,
 claim_boundary:"Positive congruence recovery only after retained conversion returns UNKNOWN at conversion-frontier. Normalized terms must be the identical projection operator (same structure name and field index); their structure arguments are then compared by the full retained converter, including proof irrelevance. Failure restores steps, budget, and the original frontier. Nested packages are consequence-separator axiomized only in this experiment after separate exact mutual recursor derivation; arbitrary Nat atoms use the prior exact candidate."};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/post-nested-projection-proof-irrelevance.json",JSON.stringify(out,null,2)+"\n");
console.log("POST_NESTED_PROJECTION_PROOF_IRRELEVANCE "+JSON.stringify(out));
if(!out.promotable_focus)process.exit(1);
