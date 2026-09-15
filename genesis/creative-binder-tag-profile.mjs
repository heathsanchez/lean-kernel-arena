import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import * as K from "./kernel.mjs";
const CAPS=["sort","binders","application","reduction","declarations","universes","theorems","proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives","inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals","quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const TARGETS=[
 "undecidability/alg-conv-trans-acc-left",
 "undecidability/alg-conv-trans-acc-right",
 "undecidability/subject-reduction-redex",
 "undecidability/alg-conv-trans-acc",
 "undecidability/subject-reduction-reduct"
];
const WANT=["ACCEPT","ACCEPT","ACCEPT","REJECT","REJECT"];
const p=K.Kernel.prototype, retainedEqual=p.equal, retainedWhnf=p.whnf;
const snap=k=>({steps:k.steps,budget:k.budget,frontier:k.conversionFrontier});
function restore(k,s){k.steps=s.steps;k.budget=s.budget;k.conversionFrontier=s.frontier;}
const fallbackable=e=>e instanceof K.Stop||e instanceof RangeError;
function spine(e){const args=[];let h=e;while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}args.reverse();return {head:h,args};}
function headClass(k,h){if(!Array.isArray(h))return typeof h;if(h[0]!=="const")return h[0];return "const:"+(k.env.get(h[1])?.kind??"unknown");}

function install(mode){
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
  let pairs=null,kind=null;
  if(Array.isArray(a)&&Array.isArray(b)&&a[0]===b[0]&&
     ((a[0]==="pi"&&mode.includes("pi"))||(a[0]==="lam"&&mode.includes("lam")))){
    kind=a[0];pairs=[[a[1],b[1],ctx],[a[2],b[2],[...ctx,a[1]]]];
  }else{
    const sa=spine(a),sb=spine(b);
    if(sa.args.length&&sa.args.length===sb.args.length&&(sa.head===sb.head||this.same(sa.head,sb.head))){
      const cls=headClass(this,sa.head);
      if(cls==="var"||cls==="const:def"){kind=cls;pairs=sa.args.map((x,i)=>[x,sb.args[i],ctx]);}
    }
  }
  if(!pairs)return retainedEqual.call(this,a,b,ctx);
  const s=snap(this);
  try{
    for(const [x,y,c] of pairs)this.equal(x,y,c);
    this.__hits??={};this.__hits[kind]=(this.__hits[kind]??0)+1;return;
  }catch(e){
    if(!fallbackable(e))throw e;restore(this,s);return retainedEqual.call(this,a,b,ctx);
  }
 };
}
function uninstall(){p.equal=retainedEqual;p.whnf=retainedWhnf;}
const modes=["pi","lam","pilam"],results=[];
for(const mode of modes){
 install(mode);const rows=[];
 for(let i=0;i<TARGETS.length;i++){
  const name=TARGETS[i],seen=[],old=p.run;p.run=function(...xs){seen.push(this);return old.apply(this,xs);};
  let r;try{r=K.checkExport(readFileSync(new URL("../_build/tests/"+name+".ndjson",import.meta.url),"utf8"),CAPS,1_000_000);}finally{p.run=old;}
  const hits={};for(const k of seen)for(const [q,n] of Object.entries(k.__hits??{}))hits[q]=(hits[q]??0)+n;
  rows.push({name,want:WANT[i],status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,hits,proofMajorHits:seen.reduce((n,k)=>n+(k.__proofMajorHits??0),0)});
 }
 results.push({mode,rows,clean:rows.every(r=>r.status===r.want)});
 uninstall();
}
const viable=results.filter(r=>r.clean).map(r=>r.mode);
const out={experiment:"creative-binder-tag-profile",viable,results};
mkdirSync("genesis/evidence",{recursive:true});
writeFileSync("genesis/evidence/creative-binder-tag-profile.json",JSON.stringify(out,null,2)+"\n");
console.log("CREATIVE_BINDER_TAG_PROFILE "+JSON.stringify(out));
if(!viable.length)process.exit(1);
