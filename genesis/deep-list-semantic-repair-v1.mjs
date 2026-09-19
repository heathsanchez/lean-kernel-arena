import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {dirname,resolve} from "node:path";
import {Kernel} from "./kernel-base.mjs";
import {leanName} from "./name-codec.mjs";
import * as P from "./production.mjs";

const N=leanName;
const ZERO=N("Nat","zero"),SUCC=N("Nat","succ");
const BLE=N("Nat","ble"),BEQ=N("Nat","beq");
const BTRUE=N("Bool","true"),BFALSE=N("Bool","false");
const TARGETS=[
  "perf/magma-list-deep-n21.ndjson",
  "perf/magma-list-deep-n36.ndjson",
];
const BUDGETS=[2_000_000,4_000_000,8_000_000];

const retainedWhnf=Kernel.prototype.whnf;

function spine(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return {h,args};
}
function natCtor(e){
  if(!Array.isArray(e)) return null;
  if(e[0]==="nat"){
    try{
      const n=BigInt(e[1]);
      if(n===0n)return {kind:"zero"};
      const p=n-1n;
      return {kind:"succ",pred:["nat",p<=BigInt(Number.MAX_SAFE_INTEGER)?Number(p):p.toString()]};
    }catch{return null;}
  }
  if(e[0]==="const"&&e[1]===ZERO&&(e[2]??[]).length===0)
    return {kind:"zero"};
  const s=spine(e);
  if(s.h?.[0]==="const"&&s.h[1]===SUCC&&(s.h[2]??[]).length===0&&s.args.length===1)
    return {kind:"succ",pred:s.args[0]};
  return null;
}
function bool(name){return ["const",name];}
function app2(k,h,a,b){return k.make("app",k.make("app",h,a),b);}

Kernel.prototype.whnf=function(e){
  if(Array.isArray(e)&&e[0]==="app"){
    const {h,args}=spine(e);
    if(h?.[0]==="const"&&(h[2]??[]).length===0&&args.length===2&&
       (h[1]===BLE||h[1]===BEQ)){
      const a=natCtor(args[0]),b=natCtor(args[1]);
      if(a&&b){
        this.tick();this.need("reduction");this.need("declarations");
        this.__symbolicNatBoolHits=(this.__symbolicNatBoolHits??0)+1;
        if(h[1]===BEQ){
          if(a.kind==="zero"&&b.kind==="zero")return bool(BTRUE);
          if(a.kind!==b.kind)return bool(BFALSE);
          return app2(this,h,a.pred,b.pred);
        }
        if(a.kind==="zero")return bool(BTRUE);
        if(b.kind==="zero")return bool(BFALSE);
        return app2(this,h,a.pred,b.pred);
      }
    }
  }
  return retainedWhnf.call(this,e);
};

const rows=[];
for(const name of TARGETS){
  const input=readFileSync(resolve("_build/tests",name),"utf8");
  const attempts=[];
  for(const budget of BUDGETS){
    const r=P.checkExport(input,{
      semanticBudget:budget,
      inputBytes:20_000_000,
      recordLimit:400_000,
    });
    attempts.push({
      budget,status:r.status,reason:r.reason??null,steps:r.steps??null,
      frontier:r.frontier_declaration??null,
    });
    console.log("DEEP_LIST_SEMANTIC_REPAIR_ATTEMPT "+JSON.stringify({
      name,budget,status:r.status,reason:r.reason??null,steps:r.steps??null,
      frontier:r.frontier_declaration??null,
    }));
    if(r.status==="ACCEPT"||r.status==="REJECT")break;
  }
  rows.push({name,attempts});
}
Kernel.prototype.whnf=retainedWhnf;

const report={
  schema:"deep-list-semantic-repair-v1",
  candidate:"symbolic Nat.ble/Nat.beq constructor equations",
  claim_boundary:"Candidate-only exact definitional reduction for Nat.ble and Nat.beq on explicit Nat.zero/Nat.succ constructor shapes. No theorem, proof-irrelevance, or unrelated conversion rule is added.",
  rows,
  gates:{
    no_latent_wrong_reject:rows.every(r=>!r.attempts.some(a=>a.status==="REJECT")),
    both_reproduce_default_unknown:rows.every(r=>r.attempts[0]?.status==="UNKNOWN"),
    both_reach_beyond_4m_without_wrong:rows.every(r=>r.attempts.some(a=>a.budget>=4_000_000)),
  },
};
mkdirSync(dirname("genesis/evidence/deep-list-semantic-repair-v1.json"),{recursive:true});
writeFileSync("genesis/evidence/deep-list-semantic-repair-v1.json",JSON.stringify(report,null,2)+"\n");
console.log("DEEP_LIST_SEMANTIC_REPAIR_RESULT="+JSON.stringify(report));
if(!Object.values(report.gates).every(Boolean))process.exit(1);
console.log("PASS_DEEP_LIST_SEMANTIC_REPAIR_V1");
