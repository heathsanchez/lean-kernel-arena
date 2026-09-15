import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const TARGETS=["undecidability/alg-conv-trans-acc-left","undecidability/alg-conv-trans-acc-right","undecidability/subject-reduction-redex","undecidability/alg-conv-trans-acc","undecidability/subject-reduction-reduct"];
const p=K.Kernel.prototype, retainedEqual=p.equal, retainedWhnf=p.whnf;
const snap=k=>({steps:k.steps,budget:k.budget,frontier:k.conversionFrontier});
function restore(k,s){k.steps=s.steps;k.budget=s.budget;k.conversionFrontier=s.frontier;}
const fallbackable=e=>e instanceof K.Stop||e instanceof RangeError;
function rawSpine(e){const args=[];let h=e;while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}args.reverse();return {head:h,args};}
function info(k,h){
 if(!Array.isArray(h))return {cls:typeof h,name:null};
 if(h[0]!=="const")return {cls:h[0],name:null};
 return {cls:"const:"+(k.env.get(h[1])?.kind??"unknown"),name:h[1]};
}
function install(){
 p.equal=retainedEqual;p.whnf=retainedWhnf;
 p.whnf=function(e){
  const out=retainedWhnf.call(this,e);
  if(out!==e||!Array.isArray(e)||e[0]!=="app"||!this.caps.has("proof-irrelevance")||this._proofMajorRepresentative)return out;
  const [rh,rargs]=this.getApp(e);if(rh?.[0]!=="const")return out;
  const rd=this.env.get(rh[1]),ind=rd?.kind==="rec"?this.env.get(rd.induct):null;
  if(rd?.kind!=="rec"||ind?.kind!=="inductive"||ind.isProp!==true)return out;
  const total=rd.numParams+1+rd.numMinors+rd.numIndices+1;if(rargs.length<total)return out;
  const major=rargs[total-1],[mh,margs]=this.getApp(major);if(mh?.[0]!=="const")return out;
  const md=this.env.get(mh[1]);if(md?.kind!=="thm"||!Array.isArray(md.value))return out;
  const s=snap(this);this._proofMajorRepresentative=true;
  try{
    let rep=this.appN(this.instantiateDeclaration(mh,md.value),margs);rep=retainedWhnf.call(this,rep);
    if(this.same(rep,major)){restore(this,s);return out;}
    const xs=rargs.slice();xs[total-1]=rep;const rebuilt=this.appN(rh,xs),reduced=retainedWhnf.call(this,rebuilt);
    if(reduced!==rebuilt){this.__proofMajorHits=(this.__proofMajorHits??0)+1;return reduced;}
    restore(this,s);return out;
  }catch(e){if(!fallbackable(e))throw e;restore(this,s);return out;}finally{this._proofMajorRepresentative=false;}
 };
 p.equal=function(a,b,ctx=[]){
  if(this.same(a,b))return;if(this.localDefs)return retainedEqual.call(this,a,b,ctx);
  let pairs=null,meta={cls:"binder",name:null,args:0};
  if(Array.isArray(a)&&Array.isArray(b)&&a[0]===b[0]&&(a[0]==="pi"||a[0]==="lam")){
    pairs=[[a[1],b[1],ctx],[a[2],b[2],[...ctx,a[1]]]];meta.args=2;
  }else{
    const sa=rawSpine(a),sb=rawSpine(b);
    if(sa.args.length&&sa.args.length===sb.args.length&&(sa.head===sb.head||this.same(sa.head,sb.head))){
      const x=info(this,sa.head);meta={...x,args:sa.args.length};
      if(x.cls==="var"||x.cls==="const:def")pairs=sa.args.map((v,i)=>[v,sb.args[i],ctx]);
    }
  }
  if(!pairs)return retainedEqual.call(this,a,b,ctx);
  const s=snap(this),start=this.steps;
  try{
    for(const [x,y,c] of pairs)this.equal(x,y,c);
    const delta=this.steps-start;
    this.__probeEvents??=[];
    if(this.__probeEvents.length<2000)this.__probeEvents.push({...meta,success:true,delta,ctx:ctx.length});
    this.__maxSuccess=Math.max(this.__maxSuccess??0,delta);
    return;
  }catch(e){
    if(!fallbackable(e))throw e;
    const delta=this.steps-start;
    this.__probeEvents??=[];
    if(this.__probeEvents.length<2000)this.__probeEvents.push({...meta,success:false,delta,ctx:ctx.length,reason:e.message});
    this.__maxFailure=Math.max(this.__maxFailure??0,delta);
    restore(this,s);return retainedEqual.call(this,a,b,ctx);
  }
 };
}
function uninstall(){p.equal=retainedEqual;p.whnf=retainedWhnf;}
install();const rows=[];
for(const name of TARGETS){
 const seen=[],old=p.run;p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
 let r;try{r=K.checkExport(readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8"),CAPS,1_000_000);}finally{p.run=old;}
 const events=seen.flatMap(k=>k.__probeEvents??[]);
 rows.push({name,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
   proofMajorHits:seen.reduce((n,k)=>n+(k.__proofMajorHits??0),0),
   maxSuccess:Math.max(0,...seen.map(k=>k.__maxSuccess??0)),maxFailure:Math.max(0,...seen.map(k=>k.__maxFailure??0)),
   successByHead:Object.fromEntries([...new Set(events.filter(e=>e.success).map(e=>e.name??e.cls))].map(q=>[q,events.filter(e=>e.success&&(e.name??e.cls)===q).map(e=>e.delta)])),
   failures:events.filter(e=>!e.success).slice(0,100)});
}
uninstall();
const maxRequired=Math.max(...rows.slice(0,3).map(r=>r.maxSuccess));
const summary={experiment:"creative-probe-cost-profile",maxRequired,rows};
mkdirSync("genesis/evidence",{recursive:true});writeFileSync("genesis/evidence/creative-probe-cost-profile.json",JSON.stringify(summary,null,2)+"\n");
console.log("CREATIVE_PROBE_COST_PROFILE "+JSON.stringify(summary));
