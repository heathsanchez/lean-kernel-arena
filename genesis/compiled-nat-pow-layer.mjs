import {Kernel} from "./kernel-base.mjs";

const p=Kernel.prototype,whnf0=p.whnf;
const N=(...xs)=>xs.reduce((pre,s)=>JSON.stringify([pre,"str",s]),"[]");
const POW=N("Nat","pow"), ZERO=N("Nat","zero");
// Lean's kernel reduce_pow guard in type_checker.cpp bounds exponents at 1 << 24.
const EXPONENT_LIMIT=1n<<24n, OUTPUT_BIT_LIMIT=4096;

function spine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return {h,args};
}
function natVal(e){
  if(!Array.isArray(e))return null;
  if(e[0]==="nat"){
    const n=e[1];
    if(!((Number.isSafeInteger(n)&&n>=0)||(typeof n==="string"&&/^(0|[1-9][0-9]*)$/.test(n))))return null;
    try{return BigInt(n);}catch{return null;}
  }
  if(e[0]==="const"&&e[1]===ZERO&&(e[2]??[]).length===0)return 0n;
  return null;
}
function boundedPow(base,exponent){
  if(exponent===0n)return 1n;
  if(base===0n)return 0n;
  if(base===1n)return 1n;
  if(base.toString(2).length>OUTPUT_BIT_LIMIT)return null;
  let out=1n,b=base,n=exponent;
  while(n>0n){
    if(n&1n){
      out*=b;
      if(out.toString(2).length>OUTPUT_BIT_LIMIT)return null;
    }
    n>>=1n;
    if(n){
      b*=b;
      if(b.toString(2).length>OUTPUT_BIT_LIMIT)return null;
    }
  }
  return out;
}
function natExpr(value){
  return ["nat",value<=BigInt(Number.MAX_SAFE_INTEGER)?Number(value):value.toString()];
}

p.whnf=function(e){
  if(Array.isArray(e)&&e[0]==="app"){
    const {h,args}=spine(e);
    if(h?.[0]==="const"&&h[1]===POW&&(h[2]??[]).length===0&&args.length===2){
      const wb=whnf0.call(this,args[0]),we=whnf0.call(this,args[1]);
      const base=natVal(wb)??natVal(args[0]),exponent=natVal(we)??natVal(args[1]);
      if(base!==null&&exponent!==null&&exponent>=0n&&exponent<=EXPONENT_LIMIT){
        const out=boundedPow(base,exponent);
        if(out!==null){
          this.need("nat-literals");this.need("reduction");
          this.__natPowHits=(this.__natPowHits??0)+1;
          return natExpr(out);
        }
      }
    }
  }
  return whnf0.call(this,e);
};
