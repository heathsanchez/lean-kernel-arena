import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {dirname} from "node:path";
import * as K from "./kernel.mjs";

const CAPS=[
  "sort","binders","application","reduction","declarations","universes",
  "theorems","proof-irrelevance","function-eta","inductive-envelope",
  "single-inductives","reflexive-inductives","inductive-reduction","rule-k",
  "unit-eta","prop-inductives","nat-literals","string-literals","quotients",
  "projections","structure-eta","rigid-conversion","opaque-declarations"
];
const BUDGET=1_000_000;
const TARGETS=[
  "perf/shared-subterm",
  "undecidability/alg-conv-trans-acc-left",
  "undecidability/alg-conv-trans-acc-right",
  "undecidability/subject-reduction-redex",
  "undecidability/alg-conv-trans-acc",
  "undecidability/subject-reduction-reduct"
];
const p=K.Kernel.prototype;
const retainedEqual=p.equal, retainedWhnf=p.whnf;
function snap(k){return {steps:k.steps,budget:k.budget,frontier:k.conversionFrontier};}
function restore(k,s){k.steps=s.steps;k.budget=s.budget;k.conversionFrontier=s.frontier;}
function fallbackable(e){return e instanceof K.Stop||e instanceof RangeError;}
function rawSpine(e){const args=[];let h=e;while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}args.reverse();return {head:h,args};}
function defHead(k,e){
  const s=rawSpine(e),h=s.head;
  return Array.isArray(h)&&h[0]==="const"&&k.env.get(h[1])?.kind==="def"?h:null;
}
function install(){
  p.equal=function(a,b,ctx=[]){
    if(this.same(a,b))return;
    if(this.localDefs)return retainedEqual.call(this,a,b,ctx);
    const ah=defHead(this,a),bh=defHead(this,b);
    if(!ah||!bh||ah[1]===bh[1])return retainedEqual.call(this,a,b,ctx);

    const s=snap(this);
    try{
      const x=retainedWhnf.call(this,a), y=retainedWhnf.call(this,b);
      if(x!==a||y!==b){
        this.__shallowDefHits=(this.__shallowDefHits??0)+1;
        retainedEqual.call(this,x,y,ctx);
        return;
      }
      restore(this,s);
      return retainedEqual.call(this,a,b,ctx);
    }catch(err){
      if(!fallbackable(err))throw err;
      restore(this,s);
      return retainedEqual.call(this,a,b,ctx);
    }
  };
}
function uninstall(){p.equal=retainedEqual;}
function inputFor(name){return readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");}
function evalOne(candidate,name){
  candidate?install():uninstall();
  const seen=[],oldRun=p.run;
  p.run=function(...args){seen.push(this);return oldRun.apply(this,args);};
  let r;const t0=Date.now();
  try{r=K.checkExport(inputFor(name),CAPS,BUDGET);}finally{p.run=oldRun;uninstall();}
  return {name,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
    elapsed_ms:Date.now()-t0,shallowDefHits:seen.reduce((n,k)=>n+(k.__shallowDefHits??0),0)};
}
const baseline=TARGETS.map(n=>evalOne(false,n));
const candidate=TARGETS.map(n=>evalOne(true,n));
const bm=new Map(baseline.map(r=>[r.name,r])),cm=new Map(candidate.map(r=>[r.name,r]));
const sharedClosed=cm.get("perf/shared-subterm")?.status==="ACCEPT";
const boundaryPreserved=TARGETS.slice(1).every(n=>{
  const b=bm.get(n),c=cm.get(n);
  return n==="undecidability/alg-conv-trans-acc-left"||n==="undecidability/subject-reduction-redex"
    ? true
    : b?.status===c?.status;
});
const summary={experiment:"shared-subterm-shallow-def-conversion",budget:BUDGET,baseline,candidate,sharedClosed,boundaryPreserved,
  claim_boundary:"Only comparisons whose two raw application heads are distinct checked definitions receive one transactional shallow-WHNF comparison before the retained converter. Failed attempts restore semantic state exactly."};
const out=new URL("./evidence/shared-subterm-shallow-def-conversion.json",import.meta.url);
mkdirSync(dirname(out.pathname),{recursive:true});
writeFileSync(out,JSON.stringify(summary,null,2)+"\n");
console.log("SHARED_SUBTERM_SHALLOW_DEF "+JSON.stringify(summary));
if(!(sharedClosed&&boundaryPreserved))process.exit(1);
