import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";

const initialCaps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="0cdb181ce17bc4f685beea8d3ccb90675ecc029cae9c4dc86629d2adbcb6e8dd";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok)throw new Error("Arena corpus fetch "+response.status);
const data=Buffer.from(await response.arrayBuffer());
const sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash)throw new Error("Arena corpus changed: got "+sha);

const py=String.raw`
import io,tarfile,json,sys
rows=[];data=sys.stdin.buffer.read()
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    p=m.name.split("/")
    if not m.isfile() or not m.name.endswith(".ndjson") or m.size>2000000: continue
    e="ACCEPT" if "good" in p else "REJECT" if "bad" in p else None
    if e: rows.append({"name":m.name,"expected":e,"input":a.extractfile(m).read().decode()})
print(json.dumps(rows))
`;
const rows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));

const CHECK_BUDGET=1_000_000;
const DEADLINE=Date.now()+14*60*1000;
const MAX_ROUNDS=8;
let timedOut=false;
const cache=new Map();

function key(caps){return [...caps].sort().join("|");}
function evaluate(caps){
  const k=key(caps);
  if(cache.has(k))return cache.get(k);
  if(Date.now()>DEADLINE){timedOut=true;return null;}
  const results=[];const counts={ACCEPT:0,REJECT:0,UNKNOWN:0};let wrong=0;
  for(const row of rows){
    if(Date.now()>DEADLINE){timedOut=true;return null;}
    const r=K.checkExport(row.input,caps,CHECK_BUDGET);
    const item={name:row.name,expected:row.expected,status:r.status,reason:r.reason??null};
    results.push(item);counts[r.status]=(counts[r.status]??0)+1;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected)wrong++;
  }
  const out={caps:[...caps],counts,wrong,results};
  cache.set(k,out);return out;
}

const baseline=evaluate(initialCaps);
if(!baseline)throw new Error("deadline before baseline");
if(baseline.wrong)throw new Error("baseline has wrong verdicts: "+baseline.wrong);
const baseByName=new Map(baseline.results.map(r=>[r.name,r]));
const protectedRows=baseline.results.filter(r=>r.status!=="UNKNOWN");

function lawful(ev){
  if(!ev||ev.wrong)return false;
  for(const b of protectedRows){
    const r=ev.results.find(x=>x.name===b.name);
    if(!r||r.status!==b.status)return false;
  }
  return true;
}
function firstDivergence(ev){
  if(!ev)return null;
  for(const b of protectedRows){
    const r=ev.results.find(x=>x.name===b.name);
    if(!r||r.status!==b.status)return {name:b.name,expected:b.expected,baseline:b.status,candidate:r?.status??"MISSING",reason:r?.reason??null};
  }
  return null;
}
function dedupStates(states){
  const m=new Map();for(const s of states)m.set(key(s),s);return [...m.values()];
}
function strictSubset(a,b){
  if(a.length>=b.length)return false;
  const B=new Set(b);return a.every(x=>B.has(x));
}

let frontier=[initialCaps];
const rounds=[];
for(let round=0;round<MAX_ROUNDS&&!timedOut;round++){
  const next=[];let changed=false;
  for(const state of frontier){
    if(Date.now()>DEADLINE){timedOut=true;break;}
    const removable=[];const blocked=[];
    for(const cap of state){
      const child=state.filter(x=>x!==cap);
      const ev=evaluate(child);
      if(!ev){timedOut=true;break;}
      if(lawful(ev))removable.push(cap);
      else blocked.push({cap,witness:firstDivergence(ev)});
    }
    if(timedOut)break;
    if(!removable.length){
      next.push(state);
      rounds.push({round,state:[...state],action:"fixed-point",removable:[],blocked});
      continue;
    }
    const batch=state.filter(x=>!removable.includes(x));
    const batchEval=evaluate(batch);
    if(!batchEval){timedOut=true;break;}
    if(lawful(batchEval)){
      next.push(batch);changed=true;
      rounds.push({round,state:[...state],action:"batch-contract",removed:removable,next:[...batch],blocked});
    }else{
      for(const cap of removable)next.push(state.filter(x=>x!==cap));
      changed=true;
      rounds.push({round,state:[...state],action:"branch-contract",removable,
        batchFailure:firstDivergence(batchEval),branches:removable.map(cap=>state.filter(x=>x!==cap)),blocked});
    }
  }
  if(timedOut)break;
  frontier=dedupStates(next);
  if(!changed)break;
}

frontier=dedupStates(frontier);
const minimalFrontier=frontier.filter((s,i)=>!frontier.some((t,j)=>i!==j&&strictSubset(t,s)));

const necessity=[];
for(const state of minimalFrontier){
  const witnesses=[];
  for(const cap of state){
    const ev=evaluate(state.filter(x=>x!==cap));
    if(!ev){timedOut=true;break;}
    witnesses.push({cap,removable:lawful(ev),witness:firstDivergence(ev)});
  }
  necessity.push({state,witnesses});
  if(timedOut)break;
}

// Distill an irreducible separator suite for the candidate family actually evaluated.
// This is qualification acceleration only; every novel candidate still owes full replay.
const candidates=[...cache.values()];
const fullPairs=[];
for(let a=0;a<candidates.length;a++)for(let b=a+1;b<candidates.length;b++){
  const A=candidates[a].results,B=candidates[b].results;
  if(A.some((r,i)=>r.status!==B[i].status))fullPairs.push([a,b]);
}
const pairKey=(a,b)=>a+"|"+b;
const universe=new Set(fullPairs.map(([a,b])=>pairKey(a,b)));
const covers=rows.map((_,i)=>{
  const s=new Set();
  for(const [a,b] of fullPairs)if(candidates[a].results[i].status!==candidates[b].results[i].status)s.add(pairKey(a,b));
  return s;
});
const chosen=[],uncovered=new Set(universe);
while(uncovered.size){
  let best=-1,gain=-1;
  for(let i=0;i<rows.length;i++){
    if(chosen.includes(i))continue;
    let g=0;for(const p of covers[i])if(uncovered.has(p))g++;
    if(g>gain){gain=g;best=i;}
  }
  if(best<0||gain<=0)break;
  chosen.push(best);for(const p of covers[best])uncovered.delete(p);
}
let deleted=true;
while(deleted){
  deleted=false;
  for(let ci=chosen.length-1;ci>=0;ci--){
    const trial=chosen.filter((_,j)=>j!==ci);
    let ok=true;
    for(const [a,b] of fullPairs){
      if(!trial.some(i=>candidates[a].results[i].status!==candidates[b].results[i].status)){ok=false;break;}
    }
    if(ok){chosen.splice(ci,1);deleted=true;}
  }
}
let partitionExact=true;
for(let a=0;a<candidates.length;a++)for(let b=a+1;b<candidates.length;b++){
  const full=candidates[a].results.some((r,i)=>r.status!==candidates[b].results[i].status);
  const small=chosen.some(i=>candidates[a].results[i].status!==candidates[b].results[i].status);
  if(full!==small)partitionExact=false;
}

const report={
  experiment:"kernel-minimal-lawful-frontier-v1",
  constitution:"MDA-v7 / MSI-style protected behavioural replay / RealityGraph-style backward deletion",
  arena_sha256:sha,
  authorityCases:rows.length,
  protectedConsequences:protectedRows.length,
  baselineCounts:baseline.counts,
  initialCapabilities:initialCaps,
  evaluatedCandidateCount:cache.size,
  rounds,
  frontier:minimalFrontier,
  necessity,
  separatorSuite:{
    size:chosen.length,
    names:chosen.map(i=>({name:rows[i].name,expected:rows[i].expected,separates:covers[i].size})),
    partitionExact
  },
  status:timedOut?"UNKNOWN_SEARCH":"VERIFIED_SINGLE_DELETION_IRREDUCIBLE_FRONTIER",
  claim_boundary:"The frontier is exact only for this pinned 188-case authority, the present capability language, and repeated lawful single-capability contraction with verified batch contraction when all current single deletions are lawful. It does not prove a globally minimal Lean kernel, mathematical necessity of retained primitives, or rule out jointly enabling multi-feature rewrites/translators. Novel candidates must replay the full authority corpus."
};
console.log("KERNEL_MINIMAL_LAWFUL_FRONTIER "+JSON.stringify(report));
