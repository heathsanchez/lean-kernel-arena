// Focused prospective test for recursive raw application congruence.
//
// The previous separator only tried one raw application layer. These creative
// conversion witnesses require recursive descent through exact same-head raw
// applications until an argument pair is discharged by proof irrelevance.
//
// No new equality rule is introduced:
//   congruence: F a... == F b... if every ai == bi
//   proof irrelevance: existing retained Lean rule
// Failed speculation is transactional and falls back to retained conversion.
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {dirname} from "node:path";
import * as K from "./kernel.mjs";

const CAPABILITIES=[
  "sort","binders","application","reduction","declarations","universes",
  "theorems","proof-irrelevance","function-eta","inductive-envelope",
  "single-inductives","reflexive-inductives","inductive-reduction","rule-k",
  "unit-eta","prop-inductives","nat-literals","string-literals","quotients",
  "projections","structure-eta","rigid-conversion","opaque-declarations"
];
const BUDGET=1_000_000;
const SPECULATION_CAP=250_000;
const TARGETS=[
  "undecidability/alg-conv-trans-acc-left",
  "undecidability/subject-reduction-redex"
];

const proto=K.Kernel.prototype;
const retainedEqual=proto.equal;

function rawSpine(e){
  const args=[];
  while(Array.isArray(e)&&e[0]==="app"){args.push(e[2]);e=e[1];}
  args.reverse();
  return {head:e,args};
}
function sameHead(k,a,b){
  return a===b || (Array.isArray(a)&&Array.isArray(b)&&k.same(a,b));
}
function snap(k){
  return {steps:k.steps,budget:k.budget,frontier:k.conversionFrontier};
}
function restore(k,s){
  k.steps=s.steps;k.budget=s.budget;k.conversionFrontier=s.frontier;
}
function inconclusive(e){
  return e instanceof K.Stop || e instanceof RangeError;
}
function proofIrrelevantPair(k,a,b,ctx){
  if(!k.caps.has("proof-irrelevance")) return false;
  const s=snap(k);
  const old=k._recursiveRawProofProbe;
  k._recursiveRawProofProbe=true;
  try{
    const ta=k.proofType(a,ctx),tb=k.proofType(b,ctx);
    if(ta===null||tb===null){restore(k,s);return false;}
    if(!k.same(ta,tb)) retainedEqual.call(k,ta,tb,ctx);
    return true;
  }catch(e){
    if(!inconclusive(e)) throw e;
    restore(k,s);
    return false;
  }finally{
    k._recursiveRawProofProbe=old;
  }
}

proto.equal=function(a,b,ctx=[]){
  if(this.localDefs || this._recursiveRawProofProbe)
    return retainedEqual.call(this,a,b,ctx);
  if(this.same(a,b)) return;

  const sa=rawSpine(a),sb=rawSpine(b);
  const eligible=sa.args.length>0 && sa.args.length===sb.args.length &&
    sameHead(this,sa.head,sb.head);
  if(!eligible) return retainedEqual.call(this,a,b,ctx);

  const s=snap(this);
  const outer=(this._recursiveRawCongruenceDepth??0)===0;
  if(outer) this.budget=Math.min(this.budget,this.steps+SPECULATION_CAP);
  this._recursiveRawCongruenceDepth=(this._recursiveRawCongruenceDepth??0)+1;

  try{
    for(let i=0;i<sa.args.length;i++){
      const x=sa.args[i],y=sb.args[i];
      if(x===y||this.same(x,y)) continue;
      if(proofIrrelevantPair(this,x,y,ctx)) continue;
      this.equal(x,y,ctx);
    }
    this._recursiveRawCongruenceDepth--;
    if(outer) this.budget=s.budget;
    return;
  }catch(e){
    this._recursiveRawCongruenceDepth--;
    if(!inconclusive(e)){
      if(outer) this.budget=s.budget;
      throw e;
    }
    restore(this,s);
    return retainedEqual.call(this,a,b,ctx);
  }
};

function inputFor(name){
  const p=new URL("../_build/tests/"+name+".ndjson",import.meta.url);
  return readFileSync(p,"utf8");
}

const candidateEqual=proto.equal;
const rows=[];
for(const name of TARGETS){
  const input=inputFor(name);
  proto.equal=retainedEqual;
  const baseline=K.checkExport(input,CAPABILITIES,BUDGET);
  proto.equal=candidateEqual;
  const candidate=K.checkExport(input,CAPABILITIES,BUDGET);
  rows.push({name,baseline,candidate});
}
proto.equal=retainedEqual;

const summary={
  candidate:"recursive-raw-application-congruence+proof-irrelevance",
  budget:BUDGET,speculation_cap:SPECULATION_CAP,rows,
  all_targets_accept:rows.every(r=>r.candidate.status==="ACCEPT"),
  claim_boundary:"Recursive exact same-head raw application congruence only. Each differing raw argument is either independently discharged by retained proof irrelevance or recursively by the same congruence rule. Any inconclusive speculative branch restores semantic steps, budget, and frontier before retained conversion."
};
const evidence=new URL("./evidence/recursive-raw-congruence-focus.json",import.meta.url);
mkdirSync(dirname(evidence.pathname),{recursive:true});
writeFileSync(evidence,JSON.stringify(summary,null,2)+"\\n");
console.log("RECURSIVE_RAW_CONGRUENCE_FOCUS "+JSON.stringify(summary));
if(!summary.all_targets_accept) process.exit(1);
