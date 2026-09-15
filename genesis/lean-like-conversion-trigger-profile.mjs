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
function sameHead(k,a,b){return a===b||(Array.isArray(a)&&Array.isArray(b)&&k.same(a,b));}
function headClass(k,h){
  if(!Array.isArray(h)) return typeof h;
  if(h[0]!=="const") return h[0];
  return "const:"+(k.env.get(h[1])?.kind??"unknown");
}
function bump(map,key){map.set(key,(map.get(key)??0)+1);}

function install(mode){
  p.equal=retainedEqual;p.whnf=retainedWhnf;
  p.whnf=function(e){
    const out=retainedWhnf.call(this,e);
    if(out!==e||!Array.isArray(e)||e[0]!=="app"||!this.caps.has("proof-irrelevance")||this._proofMajorRepresentative)return out;
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
    let kind=null,pairs=null,cls=null;
    if(Array.isArray(a)&&Array.isArray(b)&&a[0]===b[0]&&(a[0]==="pi"||a[0]==="lam")){
      kind="binder";pairs=[[a[1],b[1],ctx],[a[2],b[2],[...ctx,a[1]]]];
    }else if(mode!=="binder"){
      const sa=rawSpine(a),sb=rawSpine(b);
      if(sa.args.length>0&&sa.args.length===sb.args.length&&sameHead(this,sa.head,sb.head)){
        cls=headClass(this,sa.head);
        const allowed = mode==="all" ||
          (mode==="const" && cls.startsWith("const:")) ||
          (mode==="inductive" && cls==="const:inductive") ||
          (mode==="rec" && cls==="const:rec") ||
          (mode==="def" && cls==="const:def");
        if(allowed){kind="app";pairs=sa.args.map((x,i)=>[x,sb.args[i],ctx]);}
      }
    }
    if(!pairs)return retainedEqual.call(this,a,b,ctx);
    const s=snap(this);
    try{
      for(const [x,y,c] of pairs)this.equal(x,y,c);
      this.__probeSuccess??=new Map();bump(this.__probeSuccess,kind==="binder"?"binder":cls);
      return;
    }catch(err){
      if(!fallbackable(err))throw err;
      this.__probeFail??=new Map();bump(this.__probeFail,kind==="binder"?"binder":cls);
      restore(this,s);return retainedEqual.call(this,a,b,ctx);
    }
  };
}
function uninstall(){p.equal=retainedEqual;p.whnf=retainedWhnf;}
function inputFor(name){return readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8");}
function runMode(mode){
  install(mode);
  const rows=[];
  for(const name of TARGETS){
    const seen=[],oldRun=p.run;
    p.run=function(...args){seen.push(this);return oldRun.apply(this,args);};
    let r;try{r=K.checkExport(inputFor(name),CAPS,BUDGET);}finally{p.run=oldRun;}
    const merge=(field)=>{
      const out={};
      for(const k of seen)for(const [key,n] of (k[field]??new Map()))out[key]=(out[key]??0)+n;
      return out;
    };
    rows.push({name,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
      proofMajorHits:seen.reduce((n,k)=>n+(k.__proofMajorHits??0),0),
      probeSuccess:merge("__probeSuccess"),probeFail:merge("__probeFail")});
  }
  uninstall();
  return {mode,rows};
}
const modes=["binder","inductive","rec","def","const","all"];
const results=modes.map(runMode);
const wanted=new Set(TARGETS.slice(0,3)), forged=new Set(TARGETS.slice(3));
const viable=results.filter(v=>
  v.rows.filter(r=>wanted.has(r.name)).every(r=>r.status==="ACCEPT") &&
  v.rows.filter(r=>forged.has(r.name)).every(r=>r.status==="REJECT")
).map(v=>v.mode);
const summary={experiment:"lean-like-conversion-trigger-profile",budget:BUDGET,viable,results};
const out=new URL("./evidence/lean-like-conversion-trigger-profile.json",import.meta.url);
mkdirSync(dirname(out.pathname),{recursive:true});
writeFileSync(out,JSON.stringify(summary,null,2)+"\n");
console.log("LEAN_LIKE_TRIGGER_PROFILE "+JSON.stringify(summary));
if(!viable.length)process.exit(1);
