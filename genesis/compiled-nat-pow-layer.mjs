import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype,whnf0=p.whnf;
const N=(...xs)=>xs.reduce((pre,s)=>JSON.stringify([pre,"str",s]),"[]");

const NAT=N("Nat"), HPOW=N("HPow","hPow"), INST_HPOW=N("instHPow"),
  INST_POW_NAT=N("instPowNat"), INST_NAT_POW_NAT=N("instNatPowNat"),
  OFNAT=N("OfNat","ofNat"), INST_OFNAT_NAT=N("instOfNatNat");

function spine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return {h,args};
}
function isConst(e,name){return Array.isArray(e)&&e[0]==="const"&&e[1]===name;}
function natVal(e){
  if(!Array.isArray(e))return null;
  if(e[0]==="nat"){try{return BigInt(e[1]);}catch{return null;}}
  const {h,args}=spine(e);
  if(h?.[0]!=="const"||h[1]!==OFNAT||args.length!==3||!isConst(args[0],NAT))return null;
  let n;try{n=args[1]?.[0]==="nat"?BigInt(args[1][1]):null;}catch{n=null;}
  if(n===null)return null;
  const ip=spine(args[2]);
  if(ip.h?.[0]!=="const"||ip.h[1]!==INST_OFNAT_NAT||ip.args.length!==1)return null;
  let m;try{m=ip.args[0]?.[0]==="nat"?BigInt(ip.args[0][1]):null;}catch{m=null;}
  return m===n?n:null;
}
function isNatPowInstance(e){
  const s=spine(e);
  if(s.h?.[0]!=="const"||s.h[1]!==INST_HPOW||s.args.length!==3||
     !isConst(s.args[0],NAT)||!isConst(s.args[1],NAT))return false;
  const p=spine(s.args[2]);
  return p.h?.[0]==="const"&&p.h[1]===INST_POW_NAT&&p.args.length===2&&
    isConst(p.args[0],NAT)&&isConst(p.args[1],INST_NAT_POW_NAT);
}

p.whnf=function(e){
  if(Array.isArray(e)&&e[0]==="app"){
    const {h,args}=spine(e);
    if(h?.[0]==="const"&&h[1]===HPOW&&args.length===6&&
       isConst(args[0],NAT)&&isConst(args[1],NAT)&&isConst(args[2],NAT)&&
       isNatPowInstance(args[3])){
      const base=natVal(args[4]),exp=natVal(args[5]);
      if(base!==null&&exp!==null&&exp>=0n&&exp<=100000n){
        let out=1n,b=base,n=exp;
        while(n>0n){
          if(n&1n)out*=b;
          n>>=1n;if(n)b*=b;
          if(out>BigInt(Number.MAX_SAFE_INTEGER)||b>BigInt(Number.MAX_SAFE_INTEGER)*BigInt(Number.MAX_SAFE_INTEGER))break;
        }
        if(n===0n&&out<=BigInt(Number.MAX_SAFE_INTEGER)){
          this.need("nat-literals");this.need("reduction");this.need("declarations");
          this.__natPowHits=(this.__natPowHits??0)+1;
          return ["nat",Number(out)];
        }
      }
    }
  }
  return whnf0.call(this,e);
};

