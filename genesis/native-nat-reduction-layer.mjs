import {Kernel} from "./kernel-base.mjs";
import {leanName} from "./name-codec.mjs";

const p=Kernel.prototype,whnf0=p.whnf,instantiate0=p.instantiateDeclaration;
const N=leanName;
const ZERO=N("Nat","zero"), SUCC=N("Nat","succ"), ADD=N("Nat","add"), SUB=N("Nat","sub"),
  MUL=N("Nat","mul"), DIV=N("Nat","div"), MOD=N("Nat","mod"), BEQ=N("Nat","beq"), BLE=N("Nat","ble"),
  BTRUE=N("Bool","true"), BFALSE=N("Bool","false");
const NATIVE_MARKER="__mathgraph_native_nat_primitive";

const PRIMITIVES=new Map([
  [SUCC,{arity:1,run:([a])=>natExpr(a+1n)}],
  [ADD,{arity:2,run:([a,b])=>natExpr(a+b)}],
  [SUB,{arity:2,run:([a,b])=>natExpr(a>=b?a-b:0n)}],
  [MUL,{arity:2,run:([a,b])=>natExpr(a*b)}],
  [DIV,{arity:2,run:([a,b])=>natExpr(b===0n?0n:a/b)}],
  [MOD,{arity:2,run:([a,b])=>natExpr(b===0n?a:a%b)}],
  [BEQ,{arity:2,run:([a,b])=>["const",a===b?BTRUE:BFALSE]}],
  [BLE,{arity:2,run:([a,b])=>["const",a<=b?BTRUE:BFALSE]}]
]);

function rawSpine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return {h,args};
}
function multiBetaCount(e){
  let n=0,cur=e;
  while(Array.isArray(cur)&&cur[0]==="app"&&Array.isArray(cur[1])&&cur[1][0]==="lam"){
    n++;cur=cur[1][2];
  }
  return n;
}
function primitiveName(h){
  if(!Array.isArray(h))return null;
  if(h[0]==="const")return h[1];
  if(h[0]===NATIVE_MARKER)return h[1];
  return null;
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
function tryPrimitive(kernel,head,args,operandWhnf){
  const name=primitiveName(head),spec=name===null?null:PRIMITIVES.get(name);
  if(!spec||args.length!==spec.arity)return null;
  const values=[];
  for(const arg of args){
    const v=natVal(operandWhnf(arg));
    if(v===null)return null;
    values.push(v);
  }
  kernel.need("nat-literals");
  kernel.need("reduction");
  kernel.__nativeNatHits=(kernel.__nativeNatHits??0)+1;
  return spec.run(values);
}

// The retained multi-beta machine is a private execution path. If it exposes a
// primitive only after compiling two or more raw beta redexes, preserve that
// head long enough for the same retained native rule above to see its operands.
// No marker is installed for ordinary WHNF, single beta, or full-stack paths.
// If operands are not reducible natural values, replay the exact historical
// unfolding path instead of inventing a partial result.
p.instantiateDeclaration=function(ref,term){
  if((this.__nativeNatBridgeDepth??0)>0 && !(this.__nativeNatBypass>0) &&
     Array.isArray(ref)&&ref[0]==="const"&&PRIMITIVES.has(ref[1]))
    return [NATIVE_MARKER,ref[1],ref[2]??[]];
  return instantiate0.call(this,ref,term);
};

p.whnf=function(e){
  if((this.__nativeNatBypass??0)>0)return whnf0.call(this,e);

  if(Array.isArray(e)&&e[0]==="app"){
    const {h,args}=rawSpine(e);
    const direct=tryPrimitive(this,h,args,arg=>whnf0.call(this,arg));
    if(direct!==null)return direct;
  }

  const bridge=this._fullStackSafe!==true && multiBetaCount(e)>=2;
  if(!bridge)return whnf0.call(this,e);

  this.__nativeNatBridgeDepth=(this.__nativeNatBridgeDepth??0)+1;
  let reduced;
  try{reduced=whnf0.call(this,e);}
  finally{this.__nativeNatBridgeDepth--;}

  if(Array.isArray(reduced)){
    const {h,args}=rawSpine(reduced);
    const bridged=tryPrimitive(this,h,args,arg=>this.whnf(arg));
    if(bridged!==null)return bridged;
    if(h?.[0]===NATIVE_MARKER){
      this.__nativeNatBypass=(this.__nativeNatBypass??0)+1;
      try{return whnf0.call(this,e);}
      finally{this.__nativeNatBypass--;}
    }
  }
  return reduced;
};
