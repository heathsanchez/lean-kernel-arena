import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype,whnf0=p.whnf;
const N=(...xs)=>xs.reduce((pre,s)=>JSON.stringify([pre,"str",s]),"[]");

const NAT=N("Nat"), SUCC=N("Nat","succ"), NAT_LE=N("Nat","le");
const LT_LT=N("LT","lt"), INST_LT_NAT=N("instLTNat");
const HADD=N("HAdd","hAdd"), INST_HADD=N("instHAdd"), INST_ADD_NAT=N("instAddNat");
const OFNAT=N("OfNat","ofNat"), INST_OFNAT_NAT=N("instOfNatNat");

function spine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return {h,args};
}
function isConst(e,name){return Array.isArray(e)&&e[0]==="const"&&e[1]===name;}
function lit(e){
  if(!Array.isArray(e)||e[0]!=="nat")return null;
  try{return BigInt(e[1]);}catch{return null;}
}
function appN(k,h,args){let out=h;for(const a of args)out=k.make("app",out,a);return out;}
function ofNatNat(e){
  const {h,args}=spine(e);
  if(h?.[0]!=="const"||h[1]!==OFNAT||args.length!==3||!isConst(args[0],NAT))return null;
  const n=lit(args[1]);if(n===null)return null;
  const ip=spine(args[2]);
  if(ip.h?.[0]!=="const"||ip.h[1]!==INST_OFNAT_NAT||ip.args.length!==1||lit(ip.args[0])!==n)return null;
  return n;
}
function isHAddNatInstance(e){
  const {h,args}=spine(e);
  return h?.[0]==="const"&&h[1]===INST_HADD&&args.length===2&&
    isConst(args[0],NAT)&&isConst(args[1],INST_ADD_NAT);
}

p.whnf=function(e){
  if(Array.isArray(e)&&e[0]==="app"){
    const {h,args}=spine(e);
    if(h?.[0]==="const"){
      // LT.lt Nat instLTNat x y is the standard Nat strict order,
      // definitionally Nat.le (Nat.succ x) y.
      if(h[1]===LT_LT&&args.length===4&&isConst(args[0],NAT)&&isConst(args[1],INST_LT_NAT)){
        this.need("reduction");this.need("declarations");
        this.__natClassHits=(this.__natClassHits??0)+1;
        const sx=this.make("app",["const",SUCC],args[2]);
        return whnf0.call(this,appN(this,["const",NAT_LE],[sx,args[3]]));
      }

      // HAdd.hAdd Nat Nat Nat (instHAdd Nat instAddNat) x 1 = Nat.succ x.
      if(h[1]===HADD&&args.length===6&&isConst(args[0],NAT)&&isConst(args[1],NAT)&&
         isConst(args[2],NAT)&&isHAddNatInstance(args[3])&&ofNatNat(args[5])===1n){
        this.need("reduction");this.need("declarations");
        this.__natClassHits=(this.__natClassHits??0)+1;
        return whnf0.call(this,this.make("app",["const",SUCC],args[4]));
      }

      // Standard OfNat Nat dictionary: retain primitive Nat literal directly.
      if(h[1]===OFNAT&&args.length===3&&isConst(args[0],NAT)){
        const n=ofNatNat(e);
        if(n!==null&&n<=BigInt(Number.MAX_SAFE_INTEGER)){
          this.need("nat-literals");this.need("reduction");this.need("declarations");
          this.__natClassHits=(this.__natClassHits??0)+1;
          return ["nat",Number(n)];
        }
      }
    }
  }
  return whnf0.call(this,e);
};
