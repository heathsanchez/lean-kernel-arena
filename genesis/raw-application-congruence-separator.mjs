// Prospective separator: raw same-head application congruence before eager normalization.
//
// Certified obstruction:
//   * undecidability/alg-conv-trans-acc-left
//   * undecidability/subject-reduction-redex
//
// Both are accepted by Lean, but the retained checker can reject after eager
// normalization destroys a common application spine. This candidate adds no
// equality axiom: it tries ordinary application congruence on the raw spine,
// with proof irrelevance available on raw argument pairs, then transactionally
// falls back to the retained converter on any inconclusive attempt.
//
// This file is experiment-only. Production is unchanged until full protected
// Arena replay qualifies the consequence.
import {readFileSync,writeFileSync,mkdirSync,readdirSync} from "node:fs";
import {join,relative,dirname} from "node:path";
import * as K from "./kernel.mjs";

const CAPABILITIES=[
  "sort","binders","application","reduction","declarations","universes",
  "theorems","proof-irrelevance","function-eta","inductive-envelope",
  "single-inductives","reflexive-inductives","inductive-reduction","rule-k",
  "unit-eta","prop-inductives","nat-literals","string-literals","quotients",
  "projections","structure-eta","rigid-conversion","opaque-declarations"
];
const BUDGET=1_000_000;
const SPECULATION_CAP=180_000;
const TARGETS=new Set([
  "undecidability/alg-conv-trans-acc-left",
  "undecidability/subject-reduction-redex"
]);
const ALLOWED_REMAINING=new Set([
  "init-prelude",
  "perf/grind-ring-5",
  "perf/shared-subterm"
]);

const proto=K.Kernel.prototype;
const retainedEqual=proto.equal;

function rawSpine(e) {
  const args=[];
  while(Array.isArray(e) && e[0]==="app") {
    args.push(e[2]);
    e=e[1];
  }
  args.reverse();
  return {head:e,args};
}

function cheapPair(a,b) {
  if(a===b) return -1_000_000;
  if(!Array.isArray(a)||!Array.isArray(b)) return 0;
  if(a[0]!==b[0]) return -10_000;
  if(["const","var","nat","strlit","sort"].includes(a[0])) return -5_000;
  let score=0,stack=[a,b],seen=new Set();
  while(stack.length && score<128) {
    const x=stack.pop();
    if(!Array.isArray(x)||seen.has(x)) continue;
    seen.add(x); score++;
    for(let i=1;i<x.length;i++) if(Array.isArray(x[i])) stack.push(x[i]);
  }
  return score;
}

function restore(k,snap) {
  k.steps=snap.steps;
  k.budget=snap.budget;
  k.conversionFrontier=snap.frontier;
}

function rawProofIrrelevance(k,a,b,ctx) {
  if(!k.caps.has("proof-irrelevance")) return false;
  const snap={steps:k.steps,budget:k.budget,frontier:k.conversionFrontier};
  try {
    const ta=k.proofType(a,ctx),tb=k.proofType(b,ctx);
    if(ta===null||tb===null) {
      restore(k,snap);
      return false;
    }
    if(k.same(ta,tb)) return true;
    retainedEqual.call(k,ta,tb,ctx);
    return true;
  } catch(e) {
    if(!(e instanceof K.Stop || e instanceof RangeError)) throw e;
    restore(k,snap);
    return false;
  }
}

proto.equal=function(a,b,ctx=[]) {
  if(this.localDefs || (this._rawAppCongruenceDepth??0)>0)
    return retainedEqual.call(this,a,b,ctx);
  if(this.same(a,b)) return;

  const sa=rawSpine(a),sb=rawSpine(b);
  const sameHead=sa.args.length>0 && sa.args.length===sb.args.length &&
    (sa.head===sb.head || this.same(sa.head,sb.head));
  if(!sameHead) return retainedEqual.call(this,a,b,ctx);

  const differing=sa.args.map((_,i)=>i).filter(i=>!this.same(sa.args[i],sb.args[i]));
  if(!differing.length) return;

  const snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};
  this.budget=Math.min(this.budget,this.steps+SPECULATION_CAP);
  this._rawAppCongruenceDepth=1;

  try {
    differing.sort((i,j)=>cheapPair(sa.args[i],sb.args[i])-cheapPair(sa.args[j],sb.args[j]));
    for(const i of differing) {
      if(rawProofIrrelevance(this,sa.args[i],sb.args[i],ctx)) continue;
      retainedEqual.call(this,sa.args[i],sb.args[i],ctx);
    }
    this._rawAppCongruenceDepth=0;
    this.budget=snap.budget;
    return;
  } catch(e) {
    this._rawAppCongruenceDepth=0;
    this.budget=snap.budget;
    if(!(e instanceof K.Stop || e instanceof RangeError)) throw e;
    restore(this,snap);
    return retainedEqual.call(this,a,b,ctx);
  }
};

function walk(dir) {
  const out=[];
  for(const ent of readdirSync(dir,{withFileTypes:true})) {
    const p=join(dir,ent.name);
    if(ent.isDirectory()) out.push(...walk(p));
    else if(ent.isFile() && ent.name.endsWith(".stats.json")) out.push(p);
  }
  return out;
}

const root=new URL("../_build/tests/",import.meta.url);
const rootPath=root.pathname;
const rows=[];
let protectedChecked=0;
let protectedFailures=0;
let wrong=0;
let unknownProtected=0;

for(const statsPath of walk(rootPath).sort()) {
  const stats=JSON.parse(readFileSync(statsPath,"utf8"));
  const name=stats.name;
  const ndjsonPath=statsPath.replace(/\.stats\.json$/,".ndjson");
  const input=readFileSync(ndjsonPath,"utf8");
  const r=K.checkExport(input,CAPABILITIES,BUDGET);
  const expected=stats.outcome;
  const correct=expected==="either"
    ? (r.status==="ACCEPT"||r.status==="REJECT")
    : expected==="accept" ? r.status==="ACCEPT"
    : expected==="reject" ? r.status==="REJECT"
    : false;

  const row={name,expected,status:r.status,reason:r.reason,steps:r.steps??null,
    constructed:r.constructed??null,correct};
  rows.push(row);

  if(TARGETS.has(name)) {
    if(r.status!=="ACCEPT") wrong++;
    continue;
  }
  if(ALLOWED_REMAINING.has(name)) continue;

  protectedChecked++;
  if(!correct) {
    protectedFailures++;
    if(r.status==="UNKNOWN") unknownProtected++;
    else wrong++;
  }
}

for(const t of TARGETS) {
  const r=rows.find(x=>x.name===t);
  if(!r) throw new Error("missing target "+t);
  if(r.status!=="ACCEPT") throw new Error("target not solved: "+JSON.stringify(r));
}

if(protectedFailures) {
  const bad=rows.filter(r=>!TARGETS.has(r.name)&&!ALLOWED_REMAINING.has(r.name)&&!r.correct);
  throw new Error("protected replay changed: "+JSON.stringify(bad.slice(0,20)));
}

const targetRows=rows.filter(r=>TARGETS.has(r.name));
const remainingRows=rows.filter(r=>ALLOWED_REMAINING.has(r.name));
const summary={
  candidate:"raw-application-congruence+raw-proof-irrelevance",
  budget:BUDGET,
  speculation_cap:SPECULATION_CAP,
  total:rows.length,
  protected_checked:protectedChecked,
  protected_failures:protectedFailures,
  target_rows:targetRows,
  remaining_rows:remainingRows,
  wrong,
  unknown_protected:unknownProtected,
  claim_boundary:"Ordinary same-head application congruence is attempted on raw spines before eager normalization. Raw proof arguments may close by the already-authorized proof-irrelevance rule. Every speculative failure rolls back and delegates to the retained converter. No new definitional equality axiom or rigid rejection rule is introduced."
};
const evidencePath=new URL("./evidence/raw-application-congruence-separator.json",import.meta.url);
mkdirSync(dirname(evidencePath.pathname),{recursive:true});
writeFileSync(evidencePath,JSON.stringify({summary,rows},null,2)+"\n");
console.log("RAW_APPLICATION_CONGRUENCE_SEPARATOR "+JSON.stringify(summary));
