import {Kernel} from "./kernel-base.mjs";
import {leanName} from "./name-codec.mjs";

// Lean v4.29.1 type_checker::is_def_eq_offset compatibility.
// Primitive Nat literals are definitionally compared with Nat.zero/Nat.succ
// without expanding the entire literal into a successor chain.
const p=Kernel.prototype,eq0=p.equal;
const N=leanName;
const ZERO=N("Nat","zero"),SUCC=N("Nat","succ");

function lit(e){
  if(!Array.isArray(e)||e[0]!=="nat")return null;
  try{return BigInt(e[1]);}catch{return null;}
}
function zero(e){
  const n=lit(e); if(n!==null)return n===0n;
  return Array.isArray(e)&&e[0]==="const"&&e[1]===ZERO&&(e[2]??[]).length===0;
}
function pred(e){
  const n=lit(e);
  if(n!==null)return n>0n?["nat",(n-1n)<=BigInt(Number.MAX_SAFE_INTEGER)?Number(n-1n):(n-1n).toString()]:null;
  if(!Array.isArray(e)||e[0]!=="app")return null;
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();
  return h?.[0]==="const"&&h[1]===SUCC&&args.length===1?args[0]:null;
}

p.equalNatOffset=function(a,b,ctx=[]){
  if(!this.caps.has("nat-literals"))return false;
  const na=lit(a),nb=lit(b);
  if(na!==null&&nb!==null){
    this.tick();
    if(na!==nb)this.reject("nat-literal-mismatch");
    this.__natOffsetHits=(this.__natOffsetHits??0)+1;
    return true;
  }
  if(zero(a)&&zero(b)){
    this.__natOffsetHits=(this.__natOffsetHits??0)+1;
    return true;
  }
  const pa=pred(a),pb=pred(b);
  if(pa!==null&&pb!==null){
    this.__natOffsetHits=(this.__natOffsetHits??0)+1;
    this.tick();
    this.equal(pa,pb,ctx);
    return true;
  }
  return false;
};

p.equal=function(a,b,ctx=[]){
  if(this.equalNatOffset(a,b,ctx))return;
  return eq0.call(this,a,b,ctx);
};
