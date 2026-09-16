import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype,eq0=p.equal;
const N=(...xs)=>xs.reduce((pre,s)=>JSON.stringify([pre,"str",s]),"[]");

const NAT=N("Nat"), IS_VALID=N("Nat","isValidChar"), LT_LT=N("LT","lt"), INST_LT_NAT=N("instLTNat");
const OR=N("Or"), AND=N("And"), OFNAT=N("OfNat","ofNat"), INST_OFNAT_NAT=N("instOfNatNat");

function spine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return {h,args};
}
function isConst(e,name){return Array.isArray(e)&&e[0]==="const"&&e[1]===name;}
function lit(e){
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
function binary(e,name){
  const {h,args}=spine(e);
  return h?.[0]==="const"&&h[1]===name&&args.length===2?args:null;
}
function natLt(e){
  const {h,args}=spine(e);
  return h?.[0]==="const"&&h[1]===LT_LT&&args.length===4&&
    isConst(args[0],NAT)&&isConst(args[1],INST_LT_NAT)?[args[2],args[3]]:null;
}
function folded(e){
  const {h,args}=spine(e);
  return h?.[0]==="const"&&h[1]===IS_VALID&&args.length===1?args[0]:null;
}
function expanded(k,e,x){
  const o=binary(e,OR);if(!o)return false;
  const left=natLt(o[0]);if(!left||!k.same(left[0],x)||lit(left[1])!==55296n)return false;
  const a=binary(o[1],AND);if(!a)return false;
  const lo=natLt(a[0]),hi=natLt(a[1]);
  return !!lo&&!!hi&&lit(lo[0])===57343n&&k.same(lo[1],x)&&
    k.same(hi[0],x)&&lit(hi[1])===1114112n;
}

p.equal=function(a,b,ctx=[]){
  const xa=folded(a);
  if(xa!==null&&expanded(this,b,xa)){
    this.need("reduction");this.need("declarations");
    this.__isValidCharEqHits=(this.__isValidCharEqHits??0)+1;
    return;
  }
  const xb=folded(b);
  if(xb!==null&&expanded(this,a,xb)){
    this.need("reduction");this.need("declarations");
    this.__isValidCharEqHits=(this.__isValidCharEqHits??0)+1;
    return;
  }
  return eq0.call(this,a,b,ctx);
};
