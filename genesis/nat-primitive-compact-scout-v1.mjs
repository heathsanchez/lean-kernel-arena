import {leanName} from "./name-codec.mjs";

const N=leanName;
const ZERO=N("Nat","zero"),SUCC=N("Nat","succ");
const ADD=N("Nat","add"),SUB=N("Nat","sub"),MUL=N("Nat","mul");
const DIV=N("Nat","div"),MOD=N("Nat","mod"),BEQ=N("Nat","beq"),BLE=N("Nat","ble");
const BTRUE=N("Bool","true"),BFALSE=N("Bool","false");

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
function natExpr(v){
  return ["nat",v<=BigInt(Number.MAX_SAFE_INTEGER)?Number(v):v.toString()];
}

export function compactNatPrimitiveArity(head){
  if(!Array.isArray(head)||head[0]!=="const"||(head[2]??[]).length!==0)return null;
  const name=head[1];
  if(name===SUCC)return 1;
  if([ADD,SUB,MUL,DIV,MOD,BEQ,BLE].includes(name))return 2;
  return null;
}

export function tryCompactNatPrimitive(head,args){
  if(!Array.isArray(head)||head[0]!=="const"||(head[2]??[]).length!==0)return null;
  const name=head[1];

  if(name===SUCC&&args.length===1){
    const a=natVal(args[0]);
    return a===null?null:natExpr(a+1n);
  }

  if(args.length!==2||![ADD,SUB,MUL,DIV,MOD,BEQ,BLE].includes(name))return null;
  const a=natVal(args[0]),b=natVal(args[1]);
  if(a===null||b===null)return null;

  if(name===ADD)return natExpr(a+b);
  if(name===SUB)return natExpr(a>=b?a-b:0n);
  if(name===MUL)return natExpr(a*b);
  if(name===DIV)return natExpr(b===0n?0n:a/b);
  if(name===MOD)return natExpr(b===0n?a:a%b);
  if(name===BEQ)return ["const",a===b?BTRUE:BFALSE];
  if(name===BLE)return ["const",a<=b?BTRUE:BFALSE];
  return null;
}
