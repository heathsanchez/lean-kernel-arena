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
const NAT=N("Nat"),BTRUE=N("Bool","true"),BFALSE=N("Bool","false");
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

const rows=[];
const ENV="LEAN_DIRECT_NAT_LE_TRANSITION_V1";

for(const name of TARGETS){
  const input=readFileSync(resolve("_build/tests",name),"utf8");
  const arms={};

  for(const arm of ["cold","candidate","restart","ablation"]){
    process.env[ENV]=(arm==="candidate"||arm==="restart")?"1":"0";
    const seen=[];
    const captureRun=Kernel.prototype.run;
    Kernel.prototype.run=function(...xs){
      seen.push(this);
      return captureRun.apply(this,xs);
    };

    let r;
    const started=Date.now();
    try{
      r=P.checkExport(input,{
        semanticBudget:BUDGET,
        inputBytes:20_000_000,
        recordLimit:400_000,
      });
    }finally{
      Kernel.prototype.run=captureRun;
    }

    const directHits=seen.reduce((n,k)=>n+(k.__semStats?.directNatLeHits??0),0);
    arms[arm]={
      status:r.status,
      reason:r.reason??null,
      steps:r.steps??null,
      frontier:r.frontier_declaration??null,
      first_attempt_reason:r.first_attempt_reason??null,
      first_attempt_steps:r.first_attempt_steps??null,
      fallback_attempt_reason:r.fallback_attempt_reason??null,
      fallback_attempt_steps:r.fallback_attempt_steps??null,
      elapsed_ms:Date.now()-started,
      direct_nat_le_hits:directHits,
    };
    console.log("DIRECT_NAT_LE_TRANSITION_ARM "+JSON.stringify({
      name,arm,...arms[arm]
    }));
  }
  rows.push({name,arms});
}
delete process.env[ENV];

Kernel.prototype.whnf=retainedWhnf;
Kernel.prototype.equal=retainedEqual;
Kernel.prototype.run=retainedRun;

const sum=(arm,key)=>rows.reduce((n,r)=>n+(r.arms[arm][key]??0),0);
const candidateImproves=rows.some(r=>
  (r.arms.candidate.steps??Number.MAX_SAFE_INTEGER)<(r.arms.cold.steps??Number.MAX_SAFE_INTEGER) ||
  r.arms.candidate.elapsed_ms<r.arms.cold.elapsed_ms
);
const report={
  schema:"direct-nat-le-transition-v1",
  precommit:{
    realitygraph_commit:"c8837b46f507dfc556c37ada5c5af3550784ac25",
    source_episode_run:35425168709,
    source_episode_artifact:10578117716,
    source_episode_digest:"sha256:3bd1bc23e71c242b40cb05c7c9b93fc4de56ca7a95588fefacd2fcc44af4f682",
    source_transition_run:35425078446,
    source_transition_artifact:10578288835,
    source_transition_digest:"sha256:55af8ffd71d8ee527b6169192a2bd18b6d0a344f9a7f4c70a8a85c00d059ffeb",
  },
  candidate:"LE.le.{0} Nat instLENat xs -> Nat.le xs under exact head/universe/instance guards",
  claim_boundary:"Candidate exact WHNF transition only. No arbitrary typeclass projection, non-Nat LE instance, theorem or unrelated conversion rule is added.",
  rows,
  comparison:{
    cold_steps:sum("cold","steps"),
    candidate_steps:sum("candidate","steps"),
    restart_steps:sum("restart","steps"),
    ablation_steps:sum("ablation","steps"),
    cold_elapsed_ms:sum("cold","elapsed_ms"),
    candidate_elapsed_ms:sum("candidate","elapsed_ms"),
    restart_elapsed_ms:sum("restart","elapsed_ms"),
    ablation_elapsed_ms:sum("ablation","elapsed_ms"),
    candidate_hits:sum("candidate","direct_nat_le_hits"),
    restart_hits:sum("restart","direct_nat_le_hits"),
  },
  gates:{
    semantic_statuses_match_cold:rows.every(r=>
      ["candidate","restart","ablation"].every(a=>r.arms[a].status===r.arms.cold.status)
    ),
    no_wrong_reject:rows.every(r=>Object.values(r.arms).every(a=>a.status!=="REJECT")),
    candidate_exercised:rows.every(r=>r.arms.candidate.direct_nat_le_hits>10000),
    restart_reproduces_candidate:rows.every(r=>
      r.arms.restart.status===r.arms.candidate.status &&
      r.arms.restart.reason===r.arms.candidate.reason &&
      r.arms.restart.direct_nat_le_hits>10000
    ),
    ablation_restores_cold:rows.every(r=>
      r.arms.ablation.status===r.arms.cold.status &&
      r.arms.ablation.reason===r.arms.cold.reason &&
      r.arms.ablation.direct_nat_le_hits===0
    ),
    candidate_improves_steps_or_wall_time:candidateImproves,
  },
};
mkdirSync(dirname("genesis/evidence/direct-nat-le-transition-v1.json"),{recursive:true});
writeFileSync("genesis/evidence/direct-nat-le-transition-v1.json",JSON.stringify(report,null,2)+"\n");
console.log("DIRECT_NAT_LE_TRANSITION_RESULT="+JSON.stringify(report));
if(!Object.values(report.gates).every(Boolean))process.exit(1);
console.log("PASS_DIRECT_NAT_LE_TRANSITION_V1");
