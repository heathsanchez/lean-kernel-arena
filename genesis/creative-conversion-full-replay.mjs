// Full protected replay for the focused creative-conversion winner.
//
// Candidate = pre-normal structural congruence + proof-major representative.
// This is experiment-only. Production is unchanged unless every protected
// non-target verdict is preserved and both creative ACCEPT witnesses close.
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
const TARGETS=new Set([
  "undecidability/alg-conv-trans-acc-left",
  "undecidability/subject-reduction-redex"
]);

const p=K.Kernel.prototype;
const retainedEqual=p.equal,retainedWhnf=p.whnf;

function snap(k){return {steps:k.steps,budget:k.budget,frontier:k.conversionFrontier};}
function restore(k,s){k.steps=s.steps;k.budget=s.budget;k.conversionFrontier=s.frontier;}
function fallbackable(e){return e instanceof K.Stop || e instanceof RangeError;}

function installCandidate(){
  p.equal=retainedEqual;p.whnf=retainedWhnf;

  p.whnf=function(e){
    const out=retainedWhnf.call(this,e);
    if(out!==e || !Array.isArray(e) || e[0]!=="app" ||
       !this.caps.has("proof-irrelevance") || this._proofMajorRepresentative)
      return out;

    const [rh,rargs]=this.getApp(e);
    if(rh?.[0]!=="const") return out;
    const rd=this.env.get(rh[1]);
    if(rd?.kind!=="rec") return out;
    const ind=this.env.get(rd.induct);
    if(ind?.kind!=="inductive" || ind.isProp!==true) return out;
    const total=rd.numParams+1+rd.numMinors+rd.numIndices+1;
    if(rargs.length<total) return out;

    const major=rargs[total-1];
    const [mh,margs]=this.getApp(major);
    if(mh?.[0]!=="const") return out;
    const md=this.env.get(mh[1]);
    if(md?.kind!=="thm" || !Array.isArray(md.value)) return out;

    const s=snap(this);
    this._proofMajorRepresentative=true;
    try{
      let rep=this.instantiateDeclaration(mh,md.value);
      rep=this.appN(rep,margs);
      rep=retainedWhnf.call(this,rep);
      if(this.same(rep,major)){restore(this,s);return out;}
      const args=rargs.slice();args[total-1]=rep;
      const rebuilt=this.appN(rh,args);
      const reduced=retainedWhnf.call(this,rebuilt);
      if(reduced!==rebuilt){
        this.__proofMajorHits=(this.__proofMajorHits??0)+1;
        return reduced;
      }
      restore(this,s);return out;
    }catch(err){
      if(!fallbackable(err)) throw err;
      restore(this,s);return out;
    }finally{
      this._proofMajorRepresentative=false;
    }
  };

  p.equal=function(a,b,ctx=[]){
    if(this.same(a,b)) return;
    if(this._preNormalCongruenceProbe) return retainedEqual.call(this,a,b,ctx);
    if(Array.isArray(a)&&Array.isArray(b)&&a[0]===b[0]&&
       (a[0]==="app"||a[0]==="pi"||a[0]==="lam")){
      const s=snap(this);
      this._preNormalCongruenceProbe=(this._preNormalCongruenceProbe??0)+1;
      try{
        if(a[0]==="app"){
          this._preNormalCongruenceProbe--;
          this.equal(a[1],b[1],ctx);
          this.equal(a[2],b[2],ctx);
          this._preNormalCongruenceProbe++;
        }else{
          this._preNormalCongruenceProbe--;
          this.equal(a[1],b[1],ctx);
          this.equal(a[2],b[2],[...ctx,a[1]]);
          this._preNormalCongruenceProbe++;
        }
        this.__preNormalHits=(this.__preNormalHits??0)+1;
        this._preNormalCongruenceProbe--;
        return;
      }catch(err){
        this._preNormalCongruenceProbe=Math.max(0,(this._preNormalCongruenceProbe??1)-1);
        if(!fallbackable(err)) throw err;
        restore(this,s);
        return retainedEqual.call(this,a,b,ctx);
      }
    }
    return retainedEqual.call(this,a,b,ctx);
  };
}
function uninstall(){p.equal=retainedEqual;p.whnf=retainedWhnf;}

function walk(dir){
  const out=[];
  for(const ent of readdirSync(dir,{withFileTypes:true})){
    const q=join(dir,ent.name);
    if(ent.isDirectory()) out.push(...walk(q));
    else if(ent.isFile()&&ent.name.endsWith(".stats.json")) out.push(q);
  }
  return out;
}
function correctness(expected,status){
  if(expected==="accept") return status==="ACCEPT";
  if(expected==="reject") return status==="REJECT";
  if(expected==="either") return status==="ACCEPT"||status==="REJECT";
  return status==="UNKNOWN";
}
function count(rows){
  const c={ACCEPT:0,REJECT:0,UNKNOWN:0};
  for(const r of rows)c[r.status]=(c[r.status]??0)+1;
  return c;
}
function evaluate(candidate){
  candidate?installCandidate():uninstall();
  const rows=[];
  const root=new URL("../_build/tests/",import.meta.url).pathname;
  for(const statsPath of walk(root).sort()){
    const stats=JSON.parse(readFileSync(statsPath,"utf8"));
    const ndjson=statsPath.replace(/\.stats\.json$/,".ndjson");
    let input;
    try{input=readFileSync(ndjson,"utf8");}catch{continue;}
    const seen=[];
    const oldRun=p.run;
    p.run=function(...args){seen.push(this);return oldRun.apply(this,args);};
    let r;
    try{r=K.checkExport(input,CAPS,BUDGET);}
    finally{p.run=oldRun;}
    rows.push({
      name:stats.name,expected:stats.outcome,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null,
      correct:correctness(stats.outcome,r.status),
      preNormalHits:seen.reduce((n,k)=>n+(k.__preNormalHits??0),0),
      proofMajorHits:seen.reduce((n,k)=>n+(k.__proofMajorHits??0),0)
    });
  }
  return rows;
}

const baseline=evaluate(false);
const candidate=evaluate(true);
uninstall();

const byName=new Map(candidate.map(r=>[r.name,r]));
const baselineByName=new Map(baseline.map(r=>[r.name,r]));
const targetRows=[...TARGETS].map(name=>({
  name,baseline:baselineByName.get(name)??null,candidate:byName.get(name)??null
}));

const baselineWrong=baseline.filter(r=>!r.correct&&!TARGETS.has(r.name));
const candidateWrong=candidate.filter(r=>!r.correct);
const protectedChanged=[];
for(const b of baseline){
  if(TARGETS.has(b.name)||b.status==="UNKNOWN") continue;
  const c=byName.get(b.name);
  if(c&&c.status!==b.status)
    protectedChanged.push({name:b.name,before:b.status,after:c.status,expected:b.expected});
}
const newlyResolved=candidate.filter(c=>{
  const b=baselineByName.get(c.name);
  return b?.status==="UNKNOWN"&&c.status!=="UNKNOWN"&&c.correct;
}).map(r=>({name:r.name,status:r.status,expected:r.expected}));

const targetClosed=targetRows.every(x=>x.candidate?.status==="ACCEPT");
const lawful=baselineWrong.length===0&&candidateWrong.length===0&&
  protectedChanged.length===0&&targetClosed;

const summary={
  experiment:"creative-conversion-full-protected-replay",
  budget:BUDGET,total:baseline.length,
  baselineCounts:count(baseline),candidateCounts:count(candidate),
  baselineWrong:baselineWrong.slice(0,20),
  candidateWrong:candidateWrong.slice(0,20),
  protectedChanged:protectedChanged.slice(0,20),
  targetRows,newlyResolved,
  totalPreNormalHits:candidate.reduce((n,r)=>n+r.preNormalHits,0),
  totalProofMajorHits:candidate.reduce((n,r)=>n+r.proofMajorHits,0),
  lawful,promotable:lawful,
  claim_boundary:"Candidate adds only pre-normal app/Pi/lambda congruence and proof-irrelevant replacement of a Prop recursor theorem-major by that theorem's already-checked body. All protected decided verdicts must remain byte-for-byte status-equivalent before promotion."
};
const out=new URL("./evidence/creative-conversion-full-replay.json",import.meta.url);
mkdirSync(dirname(out.pathname),{recursive:true});
writeFileSync(out,JSON.stringify({summary,baseline,candidate},null,2)+"\n");
console.log("CREATIVE_FULL_REPLAY "+JSON.stringify(summary));
if(!lawful) process.exit(1);
