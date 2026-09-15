import {Kernel,Stop} from "./kernel-base.mjs";

const p=Kernel.prototype,retainedRun=p.run,retainedEqual=p.equal,retainedShift=p.shift;

class ShallowMiss extends Error {}
function rawSpine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return {head:h,args};
}
function rebuild(k,h,args){let out=h;for(const a of args)out=k.make("app",out,a);return out;}
function snap(k){return {steps:k.steps,budget:k.budget,frontier:k.conversionFrontier};}
function restore(k,s){k.steps=s.steps;k.budget=s.budget;k.conversionFrontier=s.frontier;}
function defSensitive(k,name,seen=new Set()){
  k.__shallowDefSensitive??=new Map();
  if(k.__shallowDefSensitive.has(name))return k.__shallowDefSensitive.get(name);
  if(seen.has(name))return false;
  seen.add(name);
  const d=k.env.get(name);
  if(d?.kind!=="def"||!Array.isArray(d.value)){k.__shallowDefSensitive.set(name,false);return false;}
  let found=false,work=[d.value],n=0;
  while(work.length&&n++<1024&&!found){
    const e=work.pop();if(!Array.isArray(e))continue;
    if(e[0]==="const"){
      const q=k.env.get(e[1]);
      if(q?.kind==="rec"){found=true;break;}
      if(q?.kind==="def"&&defSensitive(k,e[1],new Set(seen))){found=true;break;}
    }
    for(let i=1;i<e.length;i++)if(Array.isArray(e[i]))work.push(e[i]);
  }
  k.__shallowDefSensitive.set(name,found);return found;
}
function trigger(k,a,b){
  const sa=rawSpine(a),sb=rawSpine(b);
  if(sa.head?.[0]!=="const"||sb.head?.[0]!=="const"||sa.head[1]===sb.head[1])return false;
  const da=k.env.get(sa.head[1]),db=k.env.get(sb.head[1]);
  return da?.kind==="def"&&db?.kind==="def"&&defSensitive(k,sa.head[1])&&defSensitive(k,sb.head[1]);
}
function administrative(k,t){
  let cur=t;
  for(let n=0;n<32;n++){
    if(!Array.isArray(cur))return cur;
    if(cur[0]==="let"){
      k.tick();k.need("reduction");cur=k.substitute(cur[3],cur[2]);continue;
    }
    const s=rawSpine(cur);
    if(s.head?.[0]==="lam"&&s.args.length){
      k.tick();k.need("reduction");
      cur=rebuild(k,k.substitute(s.head[2],s.args[0]),s.args.slice(1));continue;
    }
    return cur;
  }
  return cur;
}
function rawIota(k,t){
  const s=rawSpine(t),rh=s.head,rargs=s.args;
  if(rh?.[0]!=="const")return null;
  const rd=k.env.get(rh[1]);if(rd?.kind!=="rec")return null;
  const total=rd.numParams+1+rd.numMinors+rd.numIndices+1;
  if(rargs.length<total)return null;
  const ms=rawSpine(rargs[total-1]),mh=ms.head,margs=ms.args;
  const md=mh?.[0]==="const"?k.env.get(mh[1]):null;
  if(md?.kind!=="ctor"||md.induct!==rd.induct||margs.length!==md.numParams+md.numFields)return null;
  for(let i=0;i<rd.numParams;i++)if(!k.same(margs[i],rargs[i]))return null;
  const rule=rd.rules.find(rr=>rr.ctor===md.name);if(!rule)return null;
  k.need("inductive-reduction");k.need("reduction");
  let rhs=k.instantiateDeclaration(rh,rule.rhs);
  rhs=k.appN(rhs,rargs.slice(0,rd.numParams+1+rd.numMinors).concat(margs.slice(md.numParams)));
  for(const extra of rargs.slice(total))rhs=k.make("app",rhs,extra);
  k.__shallowIotas=(k.__shallowIotas??0)+1;
  return administrative(k,rhs);
}
function reduceOnce(k,t,allowMajor=true){
  let cur=administrative(k,t),s=rawSpine(cur);
  if(s.head?.[0]==="const"){
    const d=k.env.get(s.head[1]);
    if(d?.kind==="def"){
      k.tick();k.need("declarations");k.need("reduction");
      let out=k.instantiateDeclaration(s.head,d.value);
      out=administrative(k,rebuild(k,out,s.args));
      k.__shallowDeltas=(k.__shallowDeltas??0)+1;
      return rawIota(k,out)??out;
    }
  }
  const io=rawIota(k,cur);if(io!==null)return io;
  if(allowMajor&&s.head?.[0]==="const"){
    const rd=k.env.get(s.head[1]);
    if(rd?.kind==="rec"){
      const total=rd.numParams+1+rd.numMinors+rd.numIndices+1;
      if(s.args.length>=total){
        const major=s.args[total-1],next=reduceOnce(k,major,false);
        if(next!==null&&next!==major){
          const xs=s.args.slice();xs[total-1]=next;
          k.__shallowMajorSteps=(k.__shallowMajorSteps??0)+1;
          return rebuild(k,s.head,xs);
        }
      }
    }
  }
  return cur===t?null:cur;
}
function compare(k,a,b,ctx,depth=0){
  if(depth>4096)throw new ShallowMiss("depth");
  let x=administrative(k,a),y=administrative(k,b);
  for(let n=0;n<20000;n++){
    if(k.same(x,y))return;
    const sx=rawSpine(x),sy=rawSpine(y);
    const sameHead=sx.args.length===sy.args.length&&
      (sx.head===sy.head||k.same(sx.head,sy.head));
    if(sameHead){
      const d=sx.head?.[0]==="const"?k.env.get(sx.head[1]):null;
      if(d?.kind==="rec"||d?.kind==="def"){
        const nx=reduceOnce(k,x,true),ny=reduceOnce(k,y,true);
        if(nx!==null&&nx!==x){x=nx;if(ny!==null&&ny!==y)y=ny;continue;}
        if(ny!==null&&ny!==y){y=ny;continue;}
      }
      for(let i=0;i<sx.args.length;i++)compare(k,sx.args[i],sy.args[i],ctx,depth+1);
      if(sx.args.length>0)return;
      if(Array.isArray(sx.head)&&Array.isArray(sy.head)&&k.same(sx.head,sy.head))return;
    }
    const nx=reduceOnce(k,x,true),ny=reduceOnce(k,y,true);
    if(nx!==null&&nx!==x){x=nx;if(ny!==null&&ny!==y)y=ny;continue;}
    if(ny!==null&&ny!==y){y=ny;continue;}
    throw new ShallowMiss("stuck");
  }
  throw new ShallowMiss("iterations");
}

p.run=function(...args){
  this.__shallowDefSensitive=new Map();this.__shallowTransactions=0;this.__shallowSuccesses=0;
  this.__shallowDeltas=0;this.__shallowIotas=0;this.__shallowMajorSteps=0;this.__shallowZeroShifts=0;
  return retainedRun.apply(this,args);
};
p.shift=function(e,amount,cut=0){
  if(amount===0){this.__shallowZeroShifts=(this.__shallowZeroShifts??0)+1;return e;}
  return retainedShift.call(this,e,amount,cut);
};
p.equal=function(a,b,ctx=[]){
  if(this.same(a,b))return;
  if(this.localDefs||this.__shallowActive||!trigger(this,a,b))return retainedEqual.call(this,a,b,ctx);
  const s=snap(this);this.__shallowTransactions=(this.__shallowTransactions??0)+1;
  this.__shallowActive=true;
  try{
    compare(this,a,b,ctx,0);
    this.__shallowSuccesses=(this.__shallowSuccesses??0)+1;
    this.__shallowActive=false;return;
  }catch(e){
    this.__shallowActive=false;
    if(!(e instanceof ShallowMiss||e instanceof Stop||e instanceof RangeError))throw e;
    restore(this,s);return retainedEqual.call(this,a,b,ctx);
  }
};
