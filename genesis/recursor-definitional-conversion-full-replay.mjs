import {cpSync,readFileSync,writeFileSync,mkdirSync,readdirSync,rmSync} from "node:fs";
import {join,dirname} from "node:path";
import {pathToFileURL} from "node:url";
import * as B from "./kernel.mjs";

const CAPS=[
  "sort","binders","application","reduction","declarations","universes",
  "theorems","proof-irrelevance","function-eta","inductive-envelope",
  "single-inductives","reflexive-inductives","inductive-reduction","rule-k",
  "unit-eta","prop-inductives","nat-literals","string-literals","quotients",
  "projections","structure-eta","rigid-conversion","opaque-declarations"
];
const BUDGET=1_000_000;
const tmp="/tmp/mda-recursor-conversion-replay";
rmSync(tmp,{recursive:true,force:true});
cpSync(new URL("./",import.meta.url),tmp,{recursive:true});
cpSync(new URL("../tests/",import.meta.url),"/tmp/tests",{recursive:true});
const basePath=join(tmp,"kernel-base.mjs");
let src=readFileSync(basePath,"utf8");
const typeOld='if(!this.same(rec.type,derived.recType)) this.reject("recursor-type:"+d.name);';
const typeNew='if(!this.same(rec.type,derived.recType)) { if(!Array.isArray(rec.type)||!Array.isArray(derived.recType)||rec.type[0]!==derived.recType[0]) this.reject("recursor-type:"+d.name); this.equal(rec.type,derived.recType,[]); }';
const ruleOld='if(!this.same(rr.rhs,derived.ruleBodies[i])) this.reject("recursor-rule-"+i);';
const ruleNew='if(!this.same(rr.rhs,derived.ruleBodies[i])) { if(!Array.isArray(rr.rhs)||!Array.isArray(derived.ruleBodies[i])||rr.rhs[0]!==derived.ruleBodies[i][0]) this.reject("recursor-rule-"+i); this.equal(rr.rhs,derived.ruleBodies[i],[]); }';
if(!src.includes(typeOld)||!src.includes(ruleOld))
  throw new Error("recursor conversion patch points moved");
src=src.replace(typeOld,typeNew).replace(ruleOld,ruleNew);
writeFileSync(basePath,src);
const C=await import(pathToFileURL(join(tmp,"kernel.mjs")).href+"?candidate=1");
await import(pathToFileURL(join(tmp,"test.mjs")).href+"?guarded-recursor-candidate=1");
console.log("GUARDED_RECURSOR_GENESIS_SUITE_PASS");

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
const baseline=evaluate(B),candidate=evaluate(C);
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
const baselineWrongKey=new Set(baselineWrong.map(x=>x.name+"|"+x.status+"|"+x.reason));
const newWrong=candidateWrong.filter(x=>!baselineWrongKey.has(x.name+"|"+x.status+"|"+x.reason));
const summary={
  experiment:"recursor-definitional-conversion-full-protected-replay",
  budget:BUDGET,total:baseline.length,
  baselineCounts:counts(baseline),candidateCounts:counts(candidate),
  baselineWrong:baselineWrong.slice(0,30),candidateWrong:candidateWrong.slice(0,30),
  protectedChanged:protectedChanged.slice(0,30),regressions:regressions.slice(0,30),
  newlyResolved,
  baselineDecidedWrong:baselineDecidedWrong.slice(0,30),
  candidateDecidedWrong:candidateDecidedWrong.slice(0,30),
  lawful:baselineDecidedWrong.length===0&&candidateDecidedWrong.length===0&&
    protectedChanged.length===0&&regressions.length===0,
  promotable:baselineDecidedWrong.length===0&&candidateDecidedWrong.length===0&&
    protectedChanged.length===0&&regressions.length===0,
  focusedEvidence:{
    run:"https://github.com/heathsanchez/lean-kernel-arena/actions/runs/35038406536",
    initPrelude:"2/2 recursor-type and 2/2 recursor-rule definitional conversions succeeded before later budget exhaustion",
    controls:"all focused forged/protected controls preserved"
  },
  claim_boundary:"Candidate changes only the fallback after exact structural equality fails for generated recursor types and generated recursor rule bodies with the same outer syntax constructor: the already-retained definitional equality checker must verify the pair. Outer-shape changes retain the original immediate rejection. No mismatch is accepted by assumption. Every previously decided protected CI Arena verdict must remain status-identical; UNKNOWN may only change when the resulting verdict matches the test expectation."
};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/recursor-definitional-conversion-full-replay.json",import.meta.url),
  JSON.stringify({summary,baseline,candidate},null,2)+"\n");
console.log("RECURSOR_CONVERSION_FULL_REPLAY "+JSON.stringify(summary));
if(!summary.promotable)process.exit(1);
