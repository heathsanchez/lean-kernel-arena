import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype,whnf0=p.whnf;
const N=(...xs)=>xs.reduce((pre,s)=>JSON.stringify([pre,"str",s]),"[]");
const ZERO=N("Nat","zero"), SUCC=N("Nat","succ"), ADD=N("Nat","add"), SUB=N("Nat","sub"),
  MUL=N("Nat","mul"), BEQ=N("Nat","beq"), BLE=N("Nat","ble"),
  BTRUE=N("Bool","true"), BFALSE=N("Bool","false");

function rawSpine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return {h,args};
}
function natVal(e){
  if(!Array.isArray(e))return null;
  if(e[0]==="nat"){
    try{return BigInt(e[1]);}catch{return null;}
  }
  if(e[0]==="const"&&e[1]===ZERO&&(e[2]??[]).length===0)return 0n;
  const {h,args}=rawSpine(e);
  if(h?.[0]==="const"&&h[1]===SUCC&&args.length===1){
    const v=natVal(args[0]); return v===null?null:v+1n;
  }
  return null;
}
function natExpr(v){
  return ["nat",v<=BigInt(Number.MAX_SAFE_INTEGER)?Number(v):v.toString()];
}

p.whnf=function(e){
  if(Array.isArray(e)&&e[0]==="app"){
    const {h,args}=rawSpine(e);
    if(h?.[0]==="const"){
      if(h[1]===SUCC&&args.length===1){
        const a=natVal(args[0]);
        if(a!==null){
          this.need("nat-literals"); this.need("reduction");
          this.__nativeNatHits=(this.__nativeNatHits??0)+1;
          return natExpr(a+1n);
        }
      }
      if(args.length===2 && [ADD,SUB,MUL,BEQ,BLE].includes(h[1])){
        const a=natVal(args[0]),b=natVal(args[1]);
        if(a!==null&&b!==null){
          this.need("nat-literals"); this.need("reduction");
          this.__nativeNatHits=(this.__nativeNatHits??0)+1;
          if(h[1]===ADD)return natExpr(a+b);
          if(h[1]===SUB)return natExpr(a>=b?a-b:0n);
          if(h[1]===MUL)return natExpr(a*b);
          if(h[1]===BEQ)return ["const",a===b?BTRUE:BFALSE];
          if(h[1]===BLE)return ["const",a<=b?BTRUE:BFALSE];
        }
      }
    }
  }
  return whnf0.call(this,e);
};
