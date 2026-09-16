import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype,whnf0=p.whnf;
const N=(...xs)=>xs.reduce((pre,s)=>JSON.stringify([pre,"str",s]),"[]");
const NAT=N("Nat"), NAT_ADD=N("Nat","add"),
  HADD=N("HAdd","hAdd"), INST_HADD=N("instHAdd"),
  ADD=N("Add","add"), INST_ADD_NAT=N("instAddNat"),
  OFNAT=N("OfNat","ofNat"), INST_OFNAT_NAT=N("instOfNatNat");

function spine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return {h,args};
}
function isConst(e,name){return Array.isArray(e)&&e[0]==="const"&&e[1]===name;}
function appN(k,h,args){let out=h;for(const a of args)out=k.make("app",out,a);return out;}
function isInstOfNatNat(k,e,n){
  const {h,args}=spine(e);
  return isConst(h,INST_OFNAT_NAT)&&args.length===1&&k.same(args[0],n);
}
function isInstHAddNat(k,e){
  const {h,args}=spine(e);
  return isConst(h,INST_HADD)&&args.length===2&&isConst(args[0],NAT)&&isConst(args[1],INST_ADD_NAT);
}

p.whnf=function(e){
  if(Array.isArray(e)&&e[0]==="app"){
    const {h,args}=spine(e);
    if(h?.[0]==="const"){
      // OfNat.ofNat Nat n (instOfNatNat n) = n
      if(h[1]===OFNAT&&args.length===3&&isConst(args[0],NAT)&&isInstOfNatNat(this,args[2],args[1])){
        this.need("reduction");this.need("declarations");
        this.__compiledNatNotationHits=(this.__compiledNatNotationHits??0)+1;
        this.__compiledOfNatNatHits=(this.__compiledOfNatNatHits??0)+1;
        return whnf0.call(this,args[1]);
      }
      // Add.add Nat instAddNat = Nat.add
      if(h[1]===ADD&&args.length>=2&&isConst(args[0],NAT)&&isConst(args[1],INST_ADD_NAT)){
        this.need("reduction");this.need("declarations");
        this.__compiledNatNotationHits=(this.__compiledNatNotationHits??0)+1;
        this.__compiledAddNatHits=(this.__compiledAddNatHits??0)+1;
        return whnf0.call(this,appN(this,["const",NAT_ADD],args.slice(2)));
      }
      // HAdd.hAdd Nat Nat Nat (instHAdd Nat instAddNat) = Nat.add
      if(h[1]===HADD&&args.length>=4&&isConst(args[0],NAT)&&isConst(args[1],NAT)&&
         isConst(args[2],NAT)&&isInstHAddNat(this,args[3])){
        this.need("reduction");this.need("declarations");
        this.__compiledNatNotationHits=(this.__compiledNatNotationHits??0)+1;
        this.__compiledHAddNatHits=(this.__compiledHAddNatHits??0)+1;
        return whnf0.call(this,appN(this,["const",NAT_ADD],args.slice(4)));
      }
    }
  }
  return whnf0.call(this,e);
};
