import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype,whnf0=p.whnf;
const N=(...xs)=>xs.reduce((pre,s)=>JSON.stringify([pre,"str",s]),"[]");
const LE_LE=N("LE","le"), NAT=N("Nat"), INST_LE_NAT=N("instLENat"), NAT_LE=N("Nat","le");

function spine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return {h,args};
}
function isConst(e,name){
  return Array.isArray(e)&&e[0]==="const"&&e[1]===name;
}
function appN(k,h,args){
  let out=h;
  for(const a of args)out=k.make("app",out,a);
  return out;
}

p.whnf=function(e){
  if(Array.isArray(e)&&e[0]==="app"){
    const {h,args}=spine(e);
    if(h?.[0]==="const"&&h[1]===LE_LE&&args.length>=2&&
       isConst(args[0],NAT)&&isConst(args[1],INST_LE_NAT)){
      // Exact dictionary-projection consequence:
      // LE.le Nat instLENat is definitionally Nat.le because
      // instLENat = LE.mk Nat Nat.le and LE.le projects field 0.
      this.need("reduction");this.need("declarations");
      this.__compiledLENatHits=(this.__compiledLENatHits??0)+1;
      const out=appN(this,["const",NAT_LE],args.slice(2));
      return whnf0.call(this,out);
    }
  }
  return whnf0.call(this,e);
};
