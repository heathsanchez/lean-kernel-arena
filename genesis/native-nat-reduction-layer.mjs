import {Kernel} from "./kernel-base.mjs";
import {leanName} from "./name-codec.mjs";

const p=Kernel.prototype,whnf0=p.whnf;
const N=leanName;
const ZERO=N("Nat","zero"), SUCC=N("Nat","succ"), ADD=N("Nat","add"), SUB=N("Nat","sub"),
  MUL=N("Nat","mul"), DIV=N("Nat","div"), MOD=N("Nat","mod"), BEQ=N("Nat","beq"), BLE=N("Nat","ble"),
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

// Minimal compiled consequence for the demonstrated private-evaluator seam.
// Recognize only a raw multi-beta chain whose materialized body is exactly
// Nat.ble applied to already-compact naturals (or variables bound by that chain).
// This performs no speculative WHNF and introduces no synthetic kernel term;
// every non-match falls through to the historical evaluator unchanged.
function betaExposedBle(e){
  const captured=[];
  let body=e;
  while(Array.isArray(body)&&body[0]==="app"&&Array.isArray(body[1])&&body[1][0]==="lam"){
    captured.push(body[2]);
    body=body[1][2];
  }
  if(captured.length<2)return null;
  const {h,args}=rawSpine(body);
  if(h?.[0]!=="const"||h[1]!==BLE||args.length!==2)return null;
  const resolve=arg=>{
    if(Array.isArray(arg)&&arg[0]==="var"&&Number.isSafeInteger(arg[1])&&arg[1]>=0&&arg[1]<captured.length)
      return captured[captured.length-1-arg[1]];
    return arg;
  };
  const a=natVal(resolve(args[0])),b=natVal(resolve(args[1]));
  if(a===null||b===null)return null;
  return ["const",a<=b?BTRUE:BFALSE];
}

p.whnf=function(e){
  if(Array.isArray(e)&&e[0]==="app"){
    const compiledBle=betaExposedBle(e);
    if(compiledBle!==null){
      this.need("application"); this.need("reduction"); this.need("nat-literals");
      this.__nativeNatHits=(this.__nativeNatHits??0)+1;
      return compiledBle;
    }

    const {h,args}=rawSpine(e);
    if(h?.[0]==="const"){
      if(h[1]===SUCC&&args.length===1){
        const wa=whnf0.call(this,args[0]),a=natVal(wa);
        if(a!==null){
          this.need("nat-literals"); this.need("reduction");
          this.__nativeNatHits=(this.__nativeNatHits??0)+1;
          return natExpr(a+1n);
        }
      }
      if(args.length===2 && [ADD,SUB,MUL,DIV,MOD,BEQ,BLE].includes(h[1])){
        // Lean's reduce_bin_nat_op / reduce_bin_nat_pred first put both
        // operands in WHNF, then recognize Nat.zero or primitive Nat literals.
        const wa=whnf0.call(this,args[0]),wb=whnf0.call(this,args[1]);
        const a=natVal(wa),b=natVal(wb);
        if(a!==null&&b!==null){
          this.need("nat-literals"); this.need("reduction");
          this.__nativeNatHits=(this.__nativeNatHits??0)+1;
          if(h[1]===ADD)return natExpr(a+b);
          if(h[1]===SUB)return natExpr(a>=b?a-b:0n);
          if(h[1]===MUL)return natExpr(a*b);
          if(h[1]===DIV)return natExpr(b===0n?0n:a/b);
          if(h[1]===MOD)return natExpr(b===0n?a:a%b);
          if(h[1]===BEQ)return ["const",a===b?BTRUE:BFALSE];
          if(h[1]===BLE)return ["const",a<=b?BTRUE:BFALSE];
        }
      }
    }
  }
  return whnf0.call(this,e);
};
