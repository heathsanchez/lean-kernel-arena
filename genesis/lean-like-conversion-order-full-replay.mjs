// Candidate-only full Arena replay for the narrow Lean-like conversion schedule.
// Production remains unchanged until this replay is green.
import {readFileSync,writeFileSync,mkdirSync,readdirSync} from "node:fs";
import {join,dirname} from "node:path";
import * as K from "./kernel.mjs";

const CAPS=[
  "sort","binders","application","reduction","declarations","universes",
  "theorems","proof-irrelevance","function-eta","inductive-envelope",
  "single-inductives","reflexive-inductives","inductive-reduction","rule-k",
  "unit-eta","prop-inductives","nat-literals","string-literals","quotients",
  "projections","structure-eta","rigid-conversion","opaque-declarations"
];
const BUDGET=1_000_000;
const ALLOWED_UNKNOWN=new Set(["init-prelude","perf/grind-ring-5","perf/shared-subterm"]);
const MUST_ACCEPT=new Set([
  "undecidability/alg-conv-trans-acc-left",
  "undecidability/alg-conv-trans-acc-right",
  "undecidability/subject-reduction-redex"
]);

const p=K.Kernel.prototype;
const retainedEqual=p.equal,retainedWhnf=p.whnf;
function snap(k){return {steps:k.steps,budget:k.budget,frontier:k.conversionFrontier};}
function restore(k,s){k.steps=s.steps;k.budget=s.budget;k.conversionFrontier=s.frontier;}
function fallbackable(e){return e instanceof K.Stop||e instanceof RangeError;}
function rawSpine(e){const args=[];let h=e;while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}args.reverse();return {head:h,args};}
function sameHead(k,a,b){return a===b||(Array.isArray(a)&&Array.isArray(b)&&k.same(a,b));}

p.whnf=function(e){
  const out=retainedWhnf.call(this,e);
  if(out!==e||!Array.isArray(e)||e[0]!=="app"||
     !this.caps.has("proof-irrelevance")||this._proofMajorRepresentative) return out;
  const [rh,rargs]=this.getApp(e);
  if(rh?.[0]!=="const")return out;
  const rd=this.env.get(rh[1]);
  if(rd?.kind!=="rec")return out;
  const ind=this.env.get(rd.induct);
  if(ind?.kind!=="inductive"||ind.isProp!==true)return out;
  const total=rd.numParams+1+rd.numMinors+rd.numIndices+1;
  if(rargs.length<total)return out;
  const major=rargs[total-1],[mh,margs]=this.getApp(major);
  if(mh?.[0]!=="const")return out;
  const md=this.env.get(mh[1]);
  if(md?.kind!=="thm"||!Array.isArray(md.value))return out;
  const s=snap(this);this._proofMajorRepresentative=true;
  try{
    let rep=this.instantiateDeclaration(mh,md.value);
    rep=this.appN(rep,margs);rep=retainedWhnf.call(this,rep);
    if(this.same(rep,major)){restore(this,s);return out;}
    const args=rargs.slice();args[total-1]=rep;
    const rebuilt=this.appN(rh,args),reduced=retainedWhnf.call(this,rebuilt);
    if(reduced!==rebuilt){this.__proofMajorHits=(this.__proofMajorHits??0)+1;return reduced;}
    restore(this,s);return out;
  }catch(err){
    if(!fallbackable(err))throw err;
    restore(this,s);return out;
  }finally{this._proofMajorRepresentative=false;}
};

p.equal=function(a,b,ctx=[]){
  if(this.same(a,b))return;
  if(this.localDefs)return retainedEqual.call(this,a,b,ctx);
  let pairs=null,app=false;
  if(Array.isArray(a)&&Array.isArray(b)&&a[0]===b[0]&&(a[0]==="pi"||a[0]==="lam")){
    pairs=[[a[1],b[1],ctx],[a[2],b[2],[...ctx,a[1]]]];
  }else{
    const sa=rawSpine(a),sb=rawSpine(b);
    if(sa.args.length>0&&sa.args.length===sb.args.length&&sameHead(this,sa.head,sb.head)){
      app=true;pairs=sa.args.map((x,i)=>[x,sb.args[i],ctx]);
    }
  }
  if(!pairs)return retainedEqual.call(this,a,b,ctx);
  const s=snap(this);
  try{
    for(const [x,y,c] of pairs)this.equal(x,y,c);
    this.__leanOrderHits=(this.__leanOrderHits??0)+1;
    if(app)this.__leanOrderAppHits=(this.__leanOrderAppHits??0)+1;
    else this.__leanOrderBinderHits=(this.__leanOrderBinderHits??0)+1;
    return;
  }catch(err){
    if(!fallbackable(err))throw err;
    restore(this,s);return retainedEqual.call(this,a,b,ctx);
  }
};

function walk(dir){
  const out=[];
  for(const ent of readdirSync(dir,{withFileTypes:true})){
    const q=join(dir,ent.name);
    if(ent.isDirectory())out.push(...walk(q));
    else if(ent.isFile()&&ent.name.endsWith(".stats.json"))out.push(q);
  }
  return out;
}
function correct(expected,status){
  if(expected==="accept")return status==="ACCEPT";
  if(expected==="reject")return status==="REJECT";
  if(expected==="either")return status==="ACCEPT"||status==="REJECT";
  return false;
}
const root=new URL("../_build/tests/",import.meta.url).pathname;
const rows=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
const t0=Date.now();
for(const statsPath of walk(root).sort()){
  const stats=JSON.parse(readFileSync(statsPath,"utf8"));
  const ndjson=statsPath.replace(/\.stats\.json$/,".ndjson");
  let input;try{input=readFileSync(ndjson,"utf8");}catch{continue;}
  const seen=[],oldRun=p.run;
  p.run=function(...args){seen.push(this);return oldRun.apply(this,args);};
  let r;try{r=K.checkExport(input,CAPS,BUDGET);}finally{p.run=oldRun;}
  counts[r.status]=(counts[r.status]??0)+1;
  rows.push({name:stats.name,expected:stats.outcome,status:r.status,reason:r.reason,
    steps:r.steps??null,constructed:r.constructed??null,correct:correct(stats.outcome,r.status),
    leanOrderHits:seen.reduce((n,k)=>n+(k.__leanOrderHits??0),0),
    proofMajorHits:seen.reduce((n,k)=>n+(k.__proofMajorHits??0),0)});
}
p.equal=retainedEqual;p.whnf=retainedWhnf;

const incorrect=rows.filter(r=>r.status!=="UNKNOWN"&&!r.correct);
const unexpectedUnknown=rows.filter(r=>r.status==="UNKNOWN"&&!ALLOWED_UNKNOWN.has(r.name));
const missingAllowed=[...ALLOWED_UNKNOWN].filter(n=>!rows.some(r=>r.name===n));
const targets=[...MUST_ACCEPT].map(name=>rows.find(r=>r.name===name)??{name,missing:true});
const targetClosed=targets.every(r=>r.status==="ACCEPT");
const allowedUnknownRows=rows.filter(r=>r.status==="UNKNOWN"&&ALLOWED_UNKNOWN.has(r.name));
const summary={
  experiment:"lean-like-conversion-order-full-candidate-replay",
  budget:BUDGET,total:rows.length,counts,elapsed_ms:Date.now()-t0,
  incorrect,unexpectedUnknown,missingAllowed,targets,allowedUnknownRows,
  totalLeanOrderHits:rows.reduce((n,r)=>n+r.leanOrderHits,0),
  totalProofMajorHits:rows.reduce((n,r)=>n+r.proofMajorHits,0),
  lawful:incorrect.length===0&&unexpectedUnknown.length===0&&targetClosed,
  promotable:incorrect.length===0&&unexpectedUnknown.length===0&&targetClosed,
  claim_boundary:"Candidate-only replay of the narrow Lean-like conversion order. The only permitted UNKNOWN rows are the three already-separated non-creative resource/semantics frontiers. Any wrong decided verdict or any new UNKNOWN fails qualification."
};
const out=new URL("./evidence/lean-like-conversion-order-full-replay.json",import.meta.url);
mkdirSync(dirname(out.pathname),{recursive:true});
writeFileSync(out,JSON.stringify({summary,rows},null,2)+"\n");
console.log("LEAN_LIKE_CONVERSION_ORDER_FULL "+JSON.stringify(summary));
if(!summary.lawful)process.exit(1);
