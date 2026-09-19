import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {dirname,resolve} from "node:path";
import * as K from "./kernel.mjs";
import * as P from "./production.mjs";

const CAPS=[
  "sort","binders","application","reduction","declarations","universes",
  "theorems","proof-irrelevance","function-eta","inductive-envelope",
  "single-inductives","reflexive-inductives","inductive-reduction","rule-k",
  "unit-eta","prop-inductives","nat-literals","string-literals","quotients",
  "projections","structure-eta","rigid-conversion","opaque-declarations"
];
const TARGETS=[
  "perf/magma-list-deep-n21.ndjson",
  "perf/magma-list-deep-n36.ndjson",
];
const BUDGET=4_000_000;

function label(n){
  if(typeof n!=="string") return String(n);
  let cur=n,parts=[];
  for(let i=0;i<40;i++){
    let x;
    try{x=JSON.parse(cur);}catch{return parts.length?parts.reverse().join("."):n;}
    if(!Array.isArray(x)||x.length!==3||(x[1]!=="str"&&x[1]!=="num"))
      return parts.length?parts.reverse().join("."):n;
    parts.push(String(x[2])); cur=x[0];
    if(cur==="[]") return parts.reverse().join(".");
  }
  return parts.reverse().join(".");
}
function spine(e){
  const args=[]; let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse(); return {head:h,args};
}
function headSummary(k,e){
  if(!Array.isArray(e)) return {tag:typeof e,value:String(e)};
  const s=spine(e),h=s.head;
  let out={tag:e[0],spine_arity:s.args.length};
  if(Array.isArray(h)){
    out.head_tag=h[0];
    if(h[0]==="const"){
      out.head_name=label(h[1]);
      const d=k.env?.get?.(h[1]);
      out.head_decl_kind=d?.kind??null;
    }else if(h[0]==="var") out.head_var=h[1];
    else if(h[0]==="proj") out.head_proj={type:label(h[1]),index:h[2]};
  }
  return out;
}
function shallow(k,e,depth=0){
  if(depth>2||!Array.isArray(e)) return headSummary(k,e);
  const tag=e[0];
  if(tag==="app"){
    const s=spine(e);
    return {
      ...headSummary(k,e),
      args:s.args.slice(0,8).map(x=>shallow(k,x,depth+1))
    };
  }
  if(tag==="pi"||tag==="lam") return {
    tag,domain:shallow(k,e[1],depth+1),body:shallow(k,e[2],depth+1)
  };
  if(tag==="proj") return {
    tag,type:label(e[1]),index:e[2],struct:shallow(k,e[3],depth+1)
  };
  if(tag==="const") return {...headSummary(k,e),name:label(e[1])};
  if(tag==="var") return {tag,index:e[1]};
  return {tag};
}

const p=K.Kernel.prototype;
const retainedEqual=p.equal;
const retainedRun=p.run;
const traces=new WeakMap();

function state(k){
  let s=traces.get(k);
  if(!s){s={rigid:[],calls:0};traces.set(k,s);}
  return s;
}
p.equal=function(a,b,ctx=[]){
  const s=state(this); s.calls++;
  try{
    return retainedEqual.call(this,a,b,ctx);
  }catch(e){
    if(e instanceof K.Stop && e.status===K.REJECT && e.message==="rigid-head-mismatch"){
      if(s.rigid.length<80){
        const sa=spine(a),sb=spine(b);
        s.rigid.push({
          step:this.steps,
          declaration:label(this.currentDeclaration),
          ctx_depth:ctx.length,
          left:shallow(this,a),
          right:shallow(this,b),
          left_raw_tag:Array.isArray(a)?a[0]:typeof a,
          right_raw_tag:Array.isArray(b)?b[0]:typeof b,
          left_spine_arity:sa.args.length,
          right_spine_arity:sb.args.length,
          left_json:JSON.stringify(a).slice(0,6000),
          right_json:JSON.stringify(b).slice(0,6000),
          error_stack:String(e?.stack??"").split("\n").slice(0,24),
        });
      }
    }
    throw e;
  }
};

const rows=[];
for(const name of TARGETS){
  const kernels=[];
  p.run=function(...xs){kernels.push(this);return retainedRun.apply(this,xs);};
  const input=readFileSync(resolve("_build/tests",name),"utf8");
  let result;
  try{
    result=P.checkExport(input,{
      semanticBudget:BUDGET,
      inputBytes:20_000_000,
      recordLimit:400_000,
    });
  }finally{
    p.run=retainedRun;
  }

  const noRigidCaps=CAPS.filter(x=>x!=="rigid-conversion");
  const withoutRigid=K.checkExport(input,noRigidCaps,BUDGET);

  const merged=[];
  for(const k of kernels){
    for(const row of state(k).rigid) merged.push(row);
  }
  rows.push({
    name,
    retained:result,
    without_rigid_conversion:withoutRigid,
    rigid_trace:merged,
    deepest_rigid:merged[0]??null,
  });
  console.log("DEEP_LIST_RIGID_DIAGNOSTIC "+JSON.stringify({
    name,
    retained:{status:result.status,reason:result.reason,steps:result.steps??null},
    withoutRigid:{status:withoutRigid.status,reason:withoutRigid.reason,steps:withoutRigid.steps??null},
    deepest:merged[0]??null,
    outermost:merged.at(-1)??null,
    firstFrames:merged.slice(0,5),
    lastFrames:merged.slice(-5),
    rigidFrameCount:merged.length,
  }));
}
p.equal=retainedEqual;
p.run=retainedRun;

const report={
  schema:"deep-list-rigid-diagnostic-v1",
  claim_boundary:"Diagnostic only. No production semantics changed. The no-rigid arm removes only the definitive rigid mismatch rejection and is not a promotion candidate.",
  budget:BUDGET,
  rows,
  gates:{
    both_retained_reject:rows.every(r=>r.retained.status==="REJECT"&&r.retained.reason==="rigid-head-mismatch"),
    both_no_rigid_nonreject:rows.every(r=>r.without_rigid_conversion.status!=="REJECT"),
    both_capture_rigid_pair:rows.every(r=>r.deepest_rigid!==null),
  },
};
mkdirSync(dirname("genesis/evidence/deep-list-rigid-diagnostic-v1.json"),{recursive:true});
writeFileSync("genesis/evidence/deep-list-rigid-diagnostic-v1.json",JSON.stringify(report,null,2)+"\n");
console.log("DEEP_LIST_RIGID_DIAGNOSTIC_RESULT="+JSON.stringify({
  gates:report.gates,
  rows:rows.map(r=>({name:r.name,deepest:r.deepest_rigid}))
}));
if(!Object.values(report.gates).every(Boolean)) process.exit(1);
console.log("PASS_DEEP_LIST_RIGID_DIAGNOSTIC_V1");
