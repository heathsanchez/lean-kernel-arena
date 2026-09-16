import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype,whnf0=p.whnf;
const N=(...xs)=>xs.reduce((pre,s)=>JSON.stringify([pre,"str",s]),"[]");

const NAT=N("Nat"), UINT32_SIZE=N("UInt32","size");
const DECIDE=N("Decidable","decide"), NAT_DECLT=N("Nat","decLt");
const LT_LT=N("LT","lt"), INST_LT_NAT=N("instLTNat");
const OFNAT=N("OfNat","ofNat"), INST_OFNAT_NAT=N("instOfNatNat");
const BTRUE=N("Bool","true"), BFALSE=N("Bool","false");

function spine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return {h,args};
}
function isConst(e,name){return Array.isArray(e)&&e[0]==="const"&&e[1]===name;}
function natVal(e){
  if(!Array.isArray(e))return null;
  if(e[0]==="nat"){try{return BigInt(e[1]);}catch{return null;}}
  if(isConst(e,UINT32_SIZE))return 4294967296n;
  const {h,args}=spine(e);
  if(h?.[0]!== "const"||h[1]!==OFNAT||args.length!==3||!isConst(args[0],NAT))return null;
  let n;try{n=args[1]?.[0]==="nat"?BigInt(args[1][1]):null;}catch{n=null;}
  if(n===null)return null;
  const ip=spine(args[2]);
  if(ip.h?.[0]!=="const"||ip.h[1]!==INST_OFNAT_NAT||ip.args.length!==1)return null;
  let m;try{m=ip.args[0]?.[0]==="nat"?BigInt(ip.args[0][1]):null;}catch{m=null;}
  return m===n?n:null;
}
function natLt(e){
  const {h,args}=spine(e);
  if(h?.[0]!=="const"||h[1]!==LT_LT||args.length!==4||
     !isConst(args[0],NAT)||!isConst(args[1],INST_LT_NAT))return null;
  const a=natVal(args[2]),b=natVal(args[3]);
  return a===null||b===null?null:[a,b];
}
function decLt(e){
  const {h,args}=spine(e);
  if(h?.[0]!=="const"||h[1]!==NAT_DECLT||args.length!==2)return null;
  const a=natVal(args[0]),b=natVal(args[1]);
  return a===null||b===null?null:[a,b];
}

p.whnf=function(e){
  if(isConst(e,UINT32_SIZE)){
    this.need("nat-literals");this.need("reduction");this.need("declarations");
    this.__constantDecisionHits=(this.__constantDecisionHits??0)+1;
    return ["nat",4294967296];
  }
  if(Array.isArray(e)&&e[0]==="app"){
    const {h,args}=spine(e);
    if(h?.[0]==="const"&&h[1]===DECIDE&&args.length===2){
      const pLt=natLt(args[0]),dLt=decLt(args[1]);
      if(pLt!==null&&dLt!==null&&pLt[0]===dLt[0]&&pLt[1]===dLt[1]){
        this.need("reduction");this.need("declarations");
        this.__constantDecisionHits=(this.__constantDecisionHits??0)+1;
        return ["const",pLt[0]<pLt[1]?BTRUE:BFALSE];
      }
    }
  }
  return whnf0.call(this,e);
};
