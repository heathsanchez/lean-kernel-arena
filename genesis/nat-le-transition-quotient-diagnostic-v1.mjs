import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {dirname,resolve} from "node:path";
import {Kernel,Stop,REJECT} from "./kernel-base.mjs";
import {leanName} from "./name-codec.mjs";
import * as P from "./production.mjs";

const N=leanName;
const ZERO=N("Nat","zero"),SUCC=N("Nat","succ");
const BLE=N("Nat","ble"),BEQ=N("Nat","beq");
const LAND=N("Nat","land"),SHIFTR=N("Nat","shiftRight");
const OFNAT=N("OfNat","ofNat"),INST_OF_NAT=N("instOfNatNat");
const NAT=N("Nat"),BTRUE=N("Bool","true"),BFALSE=N("Bool","false");\nconst PROFILE_DECL=N("Nat","succ_le_succ");\nconst LE_LE=N("LE","le"),INST_LE_NAT=N("instLENat");\nconst SAMPLE_LIMIT=100_000;
const TARGETS=[
  "perf/magma-list-deep-n21.ndjson",
  "perf/magma-list-deep-n36.ndjson",
];
const BUDGET=4_000_000;

const retainedWhnf=Kernel.prototype.whnf;
const retainedEqual=Kernel.prototype.equal;
const retainedRun=Kernel.prototype.run;
Error.stackTraceLimit=80;

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
function natVal(e){
  if(!Array.isArray(e))return null;
  if(e[0]==="nat"){try{return BigInt(e[1]);}catch{return null;}}
  if(e[0]==="const"&&e[1]===ZERO&&(e[2]??[]).length===0)return 0n;
  const c=natCtor(e);
  if(c?.kind==="succ"){
    const p=natVal(c.pred); return p===null?null:p+1n;
  }
  return null;
}
function natExpr(v){
  return ["nat",v<=BigInt(Number.MAX_SAFE_INTEGER)?Number(v):v.toString()];
}
function exactNatOfNat(e){
  const {h,args}=spine(e);
  if(h?.[0]!=="const"||h[1]!==OFNAT||args.length!==3)return null;
  if(!(args[0]?.[0]==="const"&&args[0][1]===NAT))return null;
  const inst=spine(args[2]);
  if(!(inst.h?.[0]==="const"&&inst.h[1]===INST_OF_NAT&&inst.args.length===1))return null;
  const numeral=natVal(args[1]),witness=natVal(inst.args[0]);
  if(numeral===null||witness===null||numeral!==witness)return null;
  return natExpr(numeral);
}

Kernel.prototype.whnf=function(e){
  if(Array.isArray(e)&&e[0]==="app"){
    const ofNat=exactNatOfNat(e);
    if(ofNat!==null){
      this.tick();this.need("reduction");this.need("declarations");
      this.__symbolicNatBoolHits=(this.__symbolicNatBoolHits??0)+1;
      return ofNat;
    }
    const {h,args}=spine(e);
    if(h?.[0]==="const"&&(h[2]??[]).length===0&&args.length===2&&
       (h[1]===LAND||h[1]===SHIFTR)){
      const wa=this.whnf(args[0]),wb=this.whnf(args[1]);
      const a=natVal(wa)??natVal(args[0]),b=natVal(wb)??natVal(args[1]);
      if(a!==null&&b!==null&&a>=0n&&b>=0n){
        this.tick();this.need("reduction");this.need("declarations");
        this.__symbolicNatBoolHits=(this.__symbolicNatBoolHits??0)+1;
        if(h[1]===LAND)return natExpr(a&b);
        if(b<=1000000n)return natExpr(a>>b);
      }
    }
    if(h?.[0]==="const"&&(h[2]??[]).length===0&&args.length===2&&
       (h[1]===BLE||h[1]===BEQ)){
      const wa=this.whnf(args[0]),wb=this.whnf(args[1]);
      const a=natCtor(wa),b=natCtor(wb);
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

Kernel.prototype.run=function(...args){
  this.__semanticRepairFirstRigid=null;
  this.__semanticRepairLastRigid=null;
  this.__semanticRepairHits=0;
  this.__leTransition={
    targetCalls:0,
    sampled:0,
    transitions:new Map(),
    outputHeads:new Map(),
  };
  return retainedRun.apply(this,args);
};

Kernel.prototype.equal=function(a,b,ctx=[]){
  try{
    return retainedEqual.call(this,a,b,ctx);
  }catch(e){
    if(e instanceof Stop && e.status===REJECT && e.message==="rigid-head-mismatch"){
      const row={
        step:this.steps,
        declaration:String(this.currentDeclaration),
        ctx_depth:ctx.length,
        left:JSON.stringify(a).slice(0,12000),
        right:JSON.stringify(b).slice(0,12000),
        stack:String(e.stack??"").split("\n").slice(0,80),
      };
      if(this.__semanticRepairFirstRigid===null)this.__semanticRepairFirstRigid=row;
      this.__semanticRepairLastRigid=row;
    }
    throw e;
  }
};

const semanticRepairWhnf=Kernel.prototype.whnf;\nlet globalCaseSampleCount=0;\n
function isConst(e,name){
  return Array.isArray(e)&&e[0]==="const"&&e[1]===name;
}
function targetLeTerm(e){
  if(!Array.isArray(e)||e[0]!=="app")return false;
  const {h,args}=spine(e);
  return h?.[0]==="const"&&h[1]===LE_LE&&
    args.length>=2&&
    isConst(args[0],NAT)&&
    isConst(args[1],INST_LE_NAT);
}
function shape(e,depth=0){
  if(depth>40)return ["DEPTH"];
  if(!Array.isArray(e))return typeof e==="string"?e:String(e);
  const tag=e[0];
  if(tag==="var")return ["var","_"];
  if(tag==="nat")return ["nat","_"];
  if(tag==="const")return ["const",e[1],Array.isArray(e[2])?e[2].map(()=>"_"):undefined].filter(x=>x!==undefined);
  return e.map((x,i)=>i===0?x:shape(x,depth+1));
}
function headSignature(e){
  if(!Array.isArray(e))return typeof e+":"+String(e);
  const s=spine(e);
  if(s.h?.[0]==="const")return "const:"+String(s.h[1]);
  return String(s.h?.[0]??"<none>");
}
Kernel.prototype.whnf=function(e){
  const inScope=String(this.currentDeclaration??"<none>")===PROFILE_DECL;
  const target=inScope&&targetLeTerm(e);
  const q=this.__leTransition;
  if(target&&q)q.targetCalls++;
  const out=semanticRepairWhnf.call(this,e);
  if(target&&q&&globalCaseSampleCount<SAMPLE_LIMIT){\n    globalCaseSampleCount++;\n    q.sampled++;
    const key=JSON.stringify([shape(e),shape(out)]);
    q.transitions.set(key,(q.transitions.get(key)??0)+1);
    const h=headSignature(out);
    q.outputHeads.set(h,(q.outputHeads.get(h)??0)+1);
  }
  return out;
};


const rows=[];
for(const name of TARGETS){\n  globalCaseSampleCount=0;\n  const input=readFileSync(resolve("_build/tests",name),"utf8");
  const seen=[];
  const captureRun=Kernel.prototype.run;
  Kernel.prototype.run=function(...xs){
    seen.push(this);
    return captureRun.apply(this,xs);
  };

  let r;
  try{
    r=P.checkExport(input,{
      semanticBudget:BUDGET,
      inputBytes:20_000_000,
      recordLimit:400_000,
    });
  }finally{
    Kernel.prototype.run=captureRun;
  }

  const merged={
    targetCalls:0,
    sampled:0,
    transitions:new Map(),
    outputHeads:new Map(),
  };
  for(const k of seen){
    const q=k.__leTransition;
    if(!q)continue;
    merged.targetCalls+=q.targetCalls;
    merged.sampled+=q.sampled;
    for(const [key,n] of q.transitions.entries())
      merged.transitions.set(key,(merged.transitions.get(key)??0)+n);
    for(const [key,n] of q.outputHeads.entries())
      merged.outputHeads.set(key,(merged.outputHeads.get(key)??0)+n);
  }
  const transitionRows=Array.from(merged.transitions.entries())
    .map(([transition,count])=>({count,transition:JSON.parse(transition)}))
    .sort((a,b)=>b.count-a.count||JSON.stringify(a.transition).localeCompare(JSON.stringify(b.transition)));
  const outputHeads=Array.from(merged.outputHeads.entries())
    .map(([head,count])=>({head,count}))
    .sort((a,b)=>b.count-a.count||a.head.localeCompare(b.head));
  const coveredTop8=transitionRows.slice(0,8).reduce((n,x)=>n+x.count,0);
  const coverage=merged.sampled?coveredTop8/merged.sampled:0;

  rows.push({
    name,
    status:r.status,
    reason:r.reason??null,
    steps:r.steps??null,
    frontier:r.frontier_declaration??null,
    target_calls:merged.targetCalls,
    sampled:merged.sampled,
    transition_class_count:transitionRows.length,
    top8_coverage:coverage,
    dominant_transition_count:transitionRows[0]?.count??0,
    dominant_output_head:outputHeads[0]?.head??null,
    output_heads:outputHeads.slice(0,12),
    top_transitions:transitionRows.slice(0,12),
  });
  console.log("NAT_LE_TRANSITION_QUOTIENT_ROW="+JSON.stringify(rows.at(-1)));
}

Kernel.prototype.whnf=retainedWhnf;
Kernel.prototype.equal=retainedEqual;
Kernel.prototype.run=retainedRun;

const quotientCandidate=rows.every(r=>
  r.sampled>0 &&
  r.top8_coverage>=0.99 &&
  r.transition_class_count<=8 &&
  r.dominant_transition_count>=10000
);
const directCandidate=
  rows.length===2 &&
  rows[0].dominant_output_head!==null &&
  rows[0].dominant_output_head===rows[1].dominant_output_head;
const classification=
  quotientCandidate&&directCandidate ? "quotient-and-direct-transition-candidate" :
  quotientCandidate ? "quotient-candidate-only" :
  "no-candidate";

const report={
  schema:"nat-le-transition-quotient-diagnostic-v1",
  precommit:{
    realitygraph_commit:"2c01cb013734253ade4129fa4728b64f6f33d164",
    source_episode_run:35422326680,
    source_episode_artifact:10578065010,
    source_episode_digest:"sha256:12dd7f614f93dfe79883bad21c862172039acbf0d291b7c619f033a31e2b508e",
    target_terms:"WHNF requests headed by LE.le with first arguments Nat and instLENat inside Nat.succ_le_succ",
    sample_limit_per_case:SAMPLE_LIMIT,
  },
  candidate:"measure exact input-shape -> output-shape quotient of LE.le Nat instLENat WHNF transitions",
  claim_boundary:"Diagnostic-only transition measurement. Variable and numeral identities are abstracted only for counting transition shapes; this abstraction is not used as semantic equality or as a rewrite key.",
  rows,
  classification,
  gates:{
    no_wrong_reject:rows.every(r=>r.status!=="REJECT"),
    both_unknown_at_4m:rows.every(r=>r.status==="UNKNOWN"&&r.steps===4000001),
    both_observe_target_transitions:rows.every(r=>r.target_calls>10000&&r.sampled>10000),
    sample_bound_respected:rows.every(r=>r.sampled<=SAMPLE_LIMIT),
    classification_total:["quotient-and-direct-transition-candidate","quotient-candidate-only","no-candidate"].includes(classification),
  },
};
mkdirSync(dirname("genesis/evidence/nat-le-transition-quotient-diagnostic-v1.json"),{recursive:true});
writeFileSync("genesis/evidence/nat-le-transition-quotient-diagnostic-v1.json",JSON.stringify(report,null,2)+"\n");
console.log("NAT_LE_TRANSITION_QUOTIENT_DIAGNOSTIC_RESULT="+JSON.stringify(report));
if(!Object.values(report.gates).every(Boolean))process.exit(1);
console.log("PASS_NAT_LE_TRANSITION_QUOTIENT_DIAGNOSTIC_V1");
console.log("CLASSIFICATION="+classification);
