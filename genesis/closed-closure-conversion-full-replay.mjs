import {readFileSync,writeFileSync,mkdirSync,readdirSync} from "node:fs";
import {join} from "node:path";
import * as B from "./kernel.mjs";

const CAPS=[
  "sort","binders","application","reduction","declarations","universes",
  "theorems","proof-irrelevance","function-eta","inductive-envelope",
  "single-inductives","reflexive-inductives","inductive-reduction","rule-k",
  "unit-eta","prop-inductives","nat-literals","string-literals","quotients",
  "projections","structure-eta","rigid-conversion","opaque-declarations"
];
const BUDGET=1_000_000;

function walk(dir){
  const out=[];
  for(const ent of readdirSync(dir,{withFileTypes:true})){
    const p=join(dir,ent.name);
    if(ent.isDirectory())out.push(...walk(p));
    else if(ent.isFile()&&ent.name.endsWith(".stats.json"))out.push(p);
  }
  return out;
}
function correct(expected,status){
  if(expected==="accept")return status==="ACCEPT";
  if(expected==="reject")return status==="REJECT";
  if(expected==="either")return status==="ACCEPT"||status==="REJECT";
  return status==="UNKNOWN";
}
function counts(rows){
  const out={ACCEPT:0,REJECT:0,UNKNOWN:0};
  for(const r of rows)out[r.status]=(out[r.status]??0)+1;
  return out;
}
function evaluate(K){
  const root=new URL("../_build/tests/",import.meta.url).pathname,rows=[];
  for(const sp of walk(root).sort()){
    const st=JSON.parse(readFileSync(sp,"utf8"));
    let input;
    try{input=readFileSync(sp.replace(/\.stats\.json$/,".ndjson"),"utf8");}catch{continue;}
    const r=K.checkExport(input,CAPS,BUDGET);
    rows.push({name:st.name,expected:st.outcome,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null,
      frontier_declaration:r.frontier_declaration??null,
      correct:correct(st.outcome,r.status)});
  }
  return rows;
}

const baseline=evaluate(B);

// Candidate is deliberately applied only after the full baseline pass so the
// comparison uses the same retained production kernel and corpus in one process.
await import("./closed-closure-conversion-layer.mjs");
await import("./test.mjs?closed-closure-candidate=1");
console.log("CLOSED_CLOSURE_GENESIS_SUITE_PASS");
const candidate=evaluate(B);

const by=new Map(candidate.map(x=>[x.name,x]));
const baselineWrong=baseline.filter(x=>!x.correct);
const candidateWrong=candidate.filter(x=>!x.correct);
const baselineDecidedWrong=baseline.filter(x=>x.status!=="UNKNOWN"&&!x.correct);
const candidateDecidedWrong=candidate.filter(x=>x.status!=="UNKNOWN"&&!x.correct);
const protectedChanged=[];
for(const b of baseline){
  if(b.status==="UNKNOWN")continue;
  const c=by.get(b.name);
  if(!c||c.status!==b.status)
    protectedChanged.push({name:b.name,expected:b.expected,before:b.status,after:c?.status??null,
      beforeReason:b.reason,afterReason:c?.reason??null});
}
const newlyResolved=[];
for(const b of baseline){
  if(b.status!=="UNKNOWN")continue;
  const c=by.get(b.name);
  if(c&&c.status!=="UNKNOWN"&&c.correct)
    newlyResolved.push({name:b.name,expected:b.expected,status:c.status,reason:c.reason,
      steps:c.steps,constructed:c.constructed});
}
const regressions=candidate.filter(c=>{
  const b=baseline.find(x=>x.name===c.name);
  return b?.status==="UNKNOWN"&&c.status!=="UNKNOWN"&&!c.correct;
});
const shared=candidate.find(x=>x.name==="perf/shared-subterm");
const summary={
  experiment:"closed-closure-conversion-full-protected-replay",
  budget:BUDGET,total:baseline.length,
  baselineCounts:counts(baseline),candidateCounts:counts(candidate),
  baselineWrong:baselineWrong.slice(0,30),candidateWrong:candidateWrong.slice(0,30),
  protectedChanged:protectedChanged.slice(0,30),regressions:regressions.slice(0,30),
  newlyResolved,
  baselineDecidedWrong:baselineDecidedWrong.slice(0,30),
  candidateDecidedWrong:candidateDecidedWrong.slice(0,30),
  shared,
  lawful:baselineDecidedWrong.length===0&&candidateDecidedWrong.length===0&&
    protectedChanged.length===0&&regressions.length===0,
  promotable:baselineDecidedWrong.length===0&&candidateDecidedWrong.length===0&&
    protectedChanged.length===0&&regressions.length===0&&shared?.status==="ACCEPT",
  focusedEvidence:{
    run:"https://github.com/heathsanchez/lean-kernel-arena/actions/runs/35044352963",
    shared:"ACCEPT at 269867 steps; cross ldepth/ldepth2 equality closed in 18016 steps",
    claim:"Structurally verified closed unary-iterator consequence; nonmatching or noncanonical cases fall back."
  },
  claim_boundary:"Candidate adds an exact conversion execution procedure for closed terms. Substitution is represented by interned environments; exact alias, application-spine, WHNF and proven-pair consequences are retained within one kernel run. The unary-iterator shortcut is enabled only after structurally checking the definition is a two-constructor recursive iterator whose base is its second argument and whose recursive minor is exactly the unary successor constructor applied to the recursive hypothesis. The concrete major must then be verified constructor-by-constructor as canonical; stuck, opaque, indexed, parameterized, malformed or nonmatching cases fall back to retained conversion. No typing rule, reduction rule, constructor equation, or verdict is accepted by assumption."
};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/closed-closure-conversion-full-replay.json",import.meta.url),
  JSON.stringify({summary,baseline,candidate},null,2)+"\n");
console.log("CLOSED_CLOSURE_FULL_REPLAY "+JSON.stringify(summary));
if(!summary.promotable)process.exit(1);
