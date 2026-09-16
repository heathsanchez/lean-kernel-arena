import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype,run0=p.run,whnf0=p.whnf;
const N=(pre,s)=>JSON.stringify([pre,"str",s]);
const NAT=N("[]","Nat");

function spine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return {h,args};
}
function natValue(e){
  if(!Array.isArray(e)||e[0]!=="nat")return null;
  try{return BigInt(e[1]);}catch{return null;}
}
function stripLams(e,n){
  let cur=e;
  for(let i=0;i<n;i++){
    if(!Array.isArray(cur)||cur[0]!=="lam")return null;
    cur=cur[2];
  }
  return cur;
}

p.run=function(...args){
  this.__ctorIdxCertified=new Map();
  this.__ctorIdxHits=0;
  return run0.apply(this,args);
};

function certify(k,d){
  k.__ctorIdxCertified??=new Map();
  if(k.__ctorIdxCertified.has(d.name))return k.__ctorIdxCertified.get(d.name);
  let result=null;
  try{
    if(d?.kind!=="def"||!Array.isArray(d.value)||!Array.isArray(d.type))throw 0;
    let ind=null;
    for(const x of k.env.values()){
      if(x?.kind==="inductive"&&N(x.name,"ctorIdx")===d.name){ind=x;break;}
    }
    if(!ind||ind.numParams!==0||ind.numIndices!==0||!Array.isArray(ind.ctors)||ind.ctors.length<2)throw 0;
    const I=["const",ind.name],Nat=["const",NAT];
    if(d.type[0]!=="pi"||JSON.stringify(d.type[1])!==JSON.stringify(I)||
       JSON.stringify(d.type[2])!==JSON.stringify(Nat))throw 0;
    if(d.value[0]!=="lam"||JSON.stringify(d.value[1])!==JSON.stringify(I))throw 0;
    const {h,args}=spine(d.value[2]);
    if(h?.[0]!=="const"||h[1]!==N(ind.name,"casesOn")||args.length!==2+ind.ctors.length)throw 0;
    const motive=args[0],major=args[1];
    if(motive?.[0]!=="lam"||JSON.stringify(motive[1])!==JSON.stringify(I)||
       JSON.stringify(motive[2])!==JSON.stringify(Nat)||
       major?.[0]!=="var"||major[1]!==0)throw 0;
    const ctorMap=new Map();
    for(let i=0;i<ind.ctors.length;i++){
      const cd=k.env.get(ind.ctors[i]);
      if(!cd||cd.kind!=="ctor"||cd.induct!==ind.name||cd.numParams!==0||
         !Number.isSafeInteger(cd.numFields)||cd.numFields<0)throw 0;
      const tail=stripLams(args[2+i],cd.numFields);
      const n=natValue(tail);
      if(n===null||n!==BigInt(i))throw 0;
      ctorMap.set(cd.name,i);
    }
    result={induct:ind.name,ctorMap};
  }catch{}
  k.__ctorIdxCertified.set(d.name,result);
  return result;
}

p.whnf=function(e){
  if(Array.isArray(e)&&e[0]==="app"){
    const {h,args}=spine(e);
    if(h?.[0]==="const"&&args.length===1){
      const d=this.env?.get(h[1]);
      if(d?.kind==="def"){
        const info=certify(this,d);
        if(info){
          const major=whnf0.call(this,args[0]),{h:mh}=spine(major);
          if(mh?.[0]==="const"&&info.ctorMap.has(mh[1])){
            this.__ctorIdxHits=(this.__ctorIdxHits??0)+1;
            return ["nat",info.ctorMap.get(mh[1])];
          }
        }
      }
    }
  }
  return whnf0.call(this,e);
};
