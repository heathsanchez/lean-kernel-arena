import {cpSync,readFileSync,writeFileSync,mkdirSync,readdirSync,rmSync} from "node:fs";
import {join} from "node:path";
import {pathToFileURL} from "node:url";
import * as B from "./kernel.mjs";

const CAPS=["sort","binders","application","reduction","declarations","universes","theorems",
"proof-irrelevance","function-eta","inductive-envelope","single-inductives","reflexive-inductives",
"inductive-reduction","rule-k","unit-eta","prop-inductives","nat-literals","string-literals",
"quotients","projections","structure-eta","rigid-conversion","opaque-declarations"];
const BUDGET=1_000_000,tmp="/tmp/mda-hashcons-hit-replay";
rmSync(tmp,{recursive:true,force:true});cpSync(new URL("./",import.meta.url),tmp,{recursive:true});
const kp=join(tmp,"kernel.mjs");
let ks=readFileSync(kp,"utf8");
const marker='export * from "./kernel-semantic.mjs";';
if(!ks.includes(marker))throw new Error("kernel import marker moved");
ks=ks.replace(marker,'import "./hashcons-hit-reuse-layer.mjs";\n'+marker);
writeFileSync(kp,ks);
const C=await import(pathToFileURL(kp).href+"?candidate=1");

function walk(dir){const out=[];for(const ent of readdirSync(dir,{withFileTypes:true})){const p=join(dir,ent.name);
 if(ent.isDirectory())out.push(...walk(p));else if(ent.isFile()&&ent.name.endsWith(".stats.json"))out.push(p);}return out;}
function correct(expected,status){if(expected==="accept")return status==="ACCEPT";if(expected==="reject")return status==="REJECT";
 if(expected==="either")return status==="ACCEPT"||status==="REJECT";return status==="UNKNOWN";}
function counts(rows){const o={ACCEPT:0,REJECT:0,UNKNOWN:0};for(const r of rows)o[r.status]=(o[r.status]??0)+1;return o;}
function evaluate(K){const root=new URL("../_build/tests/",import.meta.url).pathname,rows=[];
 for(const sp of walk(root).sort()){const st=JSON.parse(readFileSync(sp,"utf8"));let input;
  try{input=readFileSync(sp.replace(/\.stats\.json$/,".ndjson"),"utf8");}catch{continue;}
  const r=K.checkExport(input,CAPS,BUDGET);
  rows.push({name:st.name,expected:st.outcome,status:r.status,reason:r.reason,steps:r.steps??null,
   constructed:r.constructed??null,correct:correct(st.outcome,r.status)});}
 return rows;}
const baseline=evaluate(B),candidate=evaluate(C),by=new Map(candidate.map(x=>[x.name,x]));
const baselineDecidedWrong=baseline.filter(x=>x.status!=="UNKNOWN"&&!x.correct);
const candidateDecidedWrong=candidate.filter(x=>x.status!=="UNKNOWN"&&!x.correct);
const protectedChanged=[];
for(const b of baseline){if(b.status==="UNKNOWN")continue;const c=by.get(b.name);
 if(!c||c.status!==b.status)protectedChanged.push({name:b.name,expected:b.expected,before:b.status,after:c?.status??null,
  beforeReason:b.reason,afterReason:c?.reason??null});}
const newlyResolved=[],regressions=[];
for(const b of baseline){if(b.status!=="UNKNOWN")continue;const c=by.get(b.name);if(!c||c.status==="UNKNOWN")continue;
 if(c.correct)newlyResolved.push({name:b.name,expected:b.expected,status:c.status,reason:c.reason,steps:c.steps,constructed:c.constructed});
 else regressions.push({name:b.name,expected:b.expected,status:c.status,reason:c.reason});}
const improvements=[];
for(const b of baseline){const c=by.get(b.name);if(!c||b.status==="UNKNOWN"||c.status!==b.status)continue;
 if(Number.isFinite(b.steps)&&Number.isFinite(c.steps)&&c.steps<b.steps)
  improvements.push({name:b.name,status:b.status,before:b.steps,after:c.steps,delta:c.steps-b.steps,
   pct:(b.steps-c.steps)/Math.max(1,b.steps)*100});}
improvements.sort((a,b)=>a.delta-b.delta);
const summary={experiment:"hashcons-hit-reuse-full-protected-replay",budget:BUDGET,total:baseline.length,
 baselineCounts:counts(baseline),candidateCounts:counts(candidate),protectedChanged:protectedChanged.slice(0,30),
 regressions:regressions.slice(0,30),newlyResolved,
 baselineDecidedWrong:baselineDecidedWrong.slice(0,30),candidateDecidedWrong:candidateDecidedWrong.slice(0,30),
 improvedDecided:improvements.length,topImprovements:improvements.slice(0,30),
 lawful:baselineDecidedWrong.length===0&&candidateDecidedWrong.length===0&&protectedChanged.length===0&&regressions.length===0,
 promotable:baselineDecidedWrong.length===0&&candidateDecidedWrong.length===0&&protectedChanged.length===0&&regressions.length===0,
 claim_boundary:"Only resource accounting for exact structural hash-cons hits changes: an immutable term node already present under the identical constructor/child-identity/scalar key is returned without repaying a budget tick. Hash-cons misses retain the original tick and allocation. No term semantics, equality, typing, reduction, or rejection rule changes. Every previously decided status must remain identical; an UNKNOWN may resolve only to its expected verdict."};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/hashcons-hit-full-replay.json",import.meta.url),JSON.stringify({summary,baseline,candidate},null,2)+"\n");
console.log("HASHCONS_HIT_FULL_REPLAY "+JSON.stringify(summary));
if(!summary.promotable)process.exit(1);
