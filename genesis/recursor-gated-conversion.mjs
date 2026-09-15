import { Kernel, Stop } from "./kernel-base.mjs";

const PI_CAP=512, DEF_CAP=6500, VAR_CAP=15500;
const p=Kernel.prototype;
const retainedEqual=p.equal, retainedWhnf=p.whnf;

function snap(k){return {steps:k.steps,budget:k.budget,frontier:k.conversionFrontier};}
function restore(k,s){k.steps=s.steps;k.budget=s.budget;k.conversionFrontier=s.frontier;}
function fallbackable(e){return e instanceof Stop||e instanceof RangeError;}
function rawSpine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return {head:h,args};
}
function cls(k,h){
  if(!Array.isArray(h))return typeof h;
  if(h[0]!=="const")return h[0];
  return "const:"+(k.env.get(h[1])?.kind??"unknown");
}
function defSensitive(k,name,seen=new Set()){
  k.__recDefSensitive??=new Map();
  if(k.__recDefSensitive.has(name))return k.__recDefSensitive.get(name);
  if(seen.has(name))return false;
  seen.add(name);
  const d=k.env.get(name);
  if(d?.kind!=="def"||!Array.isArray(d.value)){
    k.__recDefSensitive.set(name,false);return false;
  }
  let found=false,work=[d.value],n=0;
  while(work.length&&n++<512&&!found){
    const e=work.pop();if(!Array.isArray(e))continue;
    if(e[0]==="const"){
      const q=k.env.get(e[1]);
      if(q?.kind==="rec"){found=true;break;}
      if(q?.kind==="def"&&defSensitive(k,e[1],new Set(seen))){found=true;break;}
    }
    for(let i=1;i<e.length;i++)if(Array.isArray(e[i]))work.push(e[i]);
  }
  k.__recDefSensitive.set(name,found);
  return found;
}
function sensitive(k,e){
  k.__recTermSensitive??=new WeakMap();
  if(Array.isArray(e)&&k.__recTermSensitive.has(e))return k.__recTermSensitive.get(e);
  let found=false,work=[e],n=0;
  while(work.length&&n++<512&&!found){
    const x=work.pop();if(!Array.isArray(x))continue;
    if(x[0]==="const"){
      const d=k.env.get(x[1]);
      if(d?.kind==="rec"||(d?.kind==="def"&&defSensitive(k,x[1]))){found=true;break;}
    }
    for(let i=1;i<x.length;i++)if(Array.isArray(x[i]))work.push(x[i]);
  }
  if(Array.isArray(e))k.__recTermSensitive.set(e,found);
  return found;
}

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

  const s=snap(this);
  this._proofMajorRepresentative=true;
  try{
    let rep=this.instantiateDeclaration(mh,md.value);
    rep=this.appN(rep,margs);
    rep=retainedWhnf.call(this,rep);
    if(this.same(rep,major)){restore(this,s);return out;}
    const args=rargs.slice();args[total-1]=rep;
    const rebuilt=this.appN(rh,args),reduced=retainedWhnf.call(this,rebuilt);
    if(reduced!==rebuilt)return reduced;
    restore(this,s);return out;
  }catch(err){
    if(!fallbackable(err))throw err;
    restore(this,s);return out;
  }finally{
    this._proofMajorRepresentative=false;
  }
};

p.equal=function(a,b,ctx=[]){
  if(this.same(a,b))return;
  if(this.localDefs)return retainedEqual.call(this,a,b,ctx);

  let pairs=null,cap=0;
  if(Array.isArray(a)&&Array.isArray(b)&&a[0]==="pi"&&b[0]==="pi"&&
     (sensitive(this,a)||sensitive(this,b))){
    cap=PI_CAP;
    pairs=[[a[1],b[1],ctx],[a[2],b[2],[...ctx,a[1]]]];
  }else{
    const sa=rawSpine(a),sb=rawSpine(b);
    if(sa.args.length>0&&sa.args.length===sb.args.length&&
       (sa.head===sb.head||this.same(sa.head,sb.head))){
      const k=cls(this,sa.head);
      if(k==="const:def"&&Array.isArray(sa.head)&&defSensitive(this,sa.head[1])){
        cap=DEF_CAP;
        pairs=sa.args.map((x,i)=>[x,sb.args[i],ctx]);
      }else if(k==="var"&&sa.args.some((x,i)=>sensitive(this,x)||sensitive(this,sb.args[i]))){
        cap=VAR_CAP;
        pairs=sa.args.map((x,i)=>[x,sb.args[i],ctx]);
      }
    }
  }
  if(!pairs)return retainedEqual.call(this,a,b,ctx);

  const s=snap(this);
  this.budget=Math.min(s.budget,s.steps+cap);
  try{
    for(const [x,y,c] of pairs)this.equal(x,y,c);
    this.budget=s.budget;
    return;
  }catch(err){
    this.budget=s.budget;
    if(!fallbackable(err))throw err;
    restore(this,s);
    return retainedEqual.call(this,a,b,ctx);
  }
};
