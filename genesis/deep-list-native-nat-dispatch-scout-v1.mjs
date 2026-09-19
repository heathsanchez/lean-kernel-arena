import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {dirname,resolve} from "node:path";
import {Kernel} from "./kernel-base.mjs";
import * as P from "./production.mjs";
import "./deep-list-symbolic-nat-layer-v1.mjs";

const TARGETS=[
  "perf/magma-list-deep-n21.ndjson",
  "perf/magma-list-deep-n36.ndjson",
];
const BUDGETS=[2_000_000,4_000_000];

const rows=[];
for(const name of TARGETS){
  const input=readFileSync(resolve("_build/tests",name),"utf8");
  const attempts=[];
  for(const budget of BUDGETS){
    const seen=[];
    const run0=Kernel.prototype.run;
    Kernel.prototype.run=function(...args){seen.push(this);return run0.apply(this,args);};
    let r;
    const t0=Date.now();
    try{
      r=P.checkExport(input,{
        semanticBudget:budget,
        inputBytes:20_000_000,
        recordLimit:400_000,
      });
    }finally{
      Kernel.prototype.run=run0;
    }
    const scopedHits=seen.reduce((n,k)=>n+(k.__scopedNativeNatHits??0),0);
    const operandHits=seen.reduce((n,k)=>n+(k.__scopedNativeOperandHits??0),0);
    const symbolicHits=seen.reduce((n,k)=>n+(k.__symbolicNatBoolHits??0),0);
    attempts.push({
      budget,
      status:r.status,
      reason:r.reason??null,
      steps:r.steps??null,
      frontier:r.frontier_declaration??null,
      scoped_native_nat_hits:scopedHits,
      symbolic_nat_bool_hits:symbolicHits,
      elapsed_ms:Date.now()-t0,
    });
    console.log("DEEP_LIST_NATIVE_NAT_DISPATCH_SCOUT "+JSON.stringify({name,...attempts.at(-1)}));
    if(r.status==="ACCEPT"||r.status==="REJECT")break;
  }
  rows.push({name,attempts});
}

const report={
  schema:"deep-list-native-nat-dispatch-scout-v1",
  claim_boundary:"Diagnostic execution-order scout. It reuses only the already-authorized compact Nat primitive equations and exposes them inside the scoped-beta evaluator before ordinary definition unfolding. It is not a production promotion and does not add Nat.decLt, Decidable, UInt32, Char, or declaration-name semantics.",
  rows,
  gates:{
    compact_native_dispatch_reached:rows.every(r=>r.attempts.some(a=>a.scoped_native_nat_hits>0)),
    native_operand_frames_reached:rows.every(r=>r.attempts.some(a=>a.scoped_native_operand_hits>0)),
    no_expected_accept_became_reject:rows.every(r=>!r.attempts.some(a=>a.status==="REJECT")),
    symbolic_repair_still_active:rows.every(r=>r.attempts.some(a=>a.symbolic_nat_bool_hits>0)),
  },
};
mkdirSync(dirname("genesis/evidence/deep-list-native-nat-dispatch-scout-v1.json"),{recursive:true});
writeFileSync("genesis/evidence/deep-list-native-nat-dispatch-scout-v1.json",JSON.stringify(report,null,2)+"\n");
console.log("DEEP_LIST_NATIVE_NAT_DISPATCH_SCOUT_RESULT="+JSON.stringify(report));
if(!Object.values(report.gates).every(Boolean))process.exit(1);
console.log("PASS_DEEP_LIST_NATIVE_NAT_DISPATCH_SCOUT_V1");
