import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="0cdb181ce17bc4f685beea8d3ccb90675ecc029cae9c4dc86629d2adbcb6e8dd";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok)throw new Error("Arena corpus fetch "+response.status);
const data=Buffer.from(await response.arrayBuffer()),sha=createHash("sha256").update(data).digest("hex");
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
const candidates=[{name:"baseline",caps},...caps.map(cap=>({name:"drop:"+cap,caps:caps.filter(x=>x!==cap),drop:cap}))];

const signatures=new Map();
for(const cand of candidates){
  const sig=[];
  let wrong=0;
  for(const row of rows){
    const r=K.checkExport(row.input,cand.caps,1000000);
    sig.push(r.status);
    if(r.status!=="UNKNOWN"&&r.status!==row.expected)wrong++;
  }
  signatures.set(cand.name,{sig,wrong});
}
const baseline=signatures.get("baseline").sig;

const necessity=[];
for(const cand of candidates.slice(1)){
  const s=signatures.get(cand.name);
  let witness=-1;
  for(let i=0;i<rows.length;i++) if(s.sig[i]!==baseline[i]){witness=i;break;}
  necessity.push({
    capability:cand.drop,
    status:witness<0?"NO_VERDICT_WITNESS":"RETAINED_BY_CURRENT_C",
    witness:witness<0?null:{
      name:rows[witness].name,expected:rows[witness].expected,
      baseline:baseline[witness],ablated:s.sig[witness]
    },
    wrong:s.wrong
  });
}

// Partition-preserving separator suite for the CURRENT candidate family.
// A probe subset S is sufficient iff every pair separated by full C is separated by S.
const n=candidates.length;
const fullPairs=[];
for(let a=0;a<n;a++)for(let b=a+1;b<n;b++){
  const sa=signatures.get(candidates[a].name).sig,sb=signatures.get(candidates[b].name).sig;
  if(sa.some((v,i)=>v!==sb[i])) fullPairs.push([a,b]);
}
const pairKey=(a,b)=>a+"|"+b;
const universe=new Set(fullPairs.map(([a,b])=>pairKey(a,b)));
const covers=rows.map((_,i)=>{
  const set=new Set();
  for(const [a,b] of fullPairs){
    const sa=signatures.get(candidates[a].name).sig[i],sb=signatures.get(candidates[b].name).sig[i];
    if(sa!==sb)set.add(pairKey(a,b));
  }
  return set;
});

// Greedy cover, then exact backward deletion to irreducibility.
const chosen=[],uncovered=new Set(universe);
while(uncovered.size){
  let best=-1,bestGain=-1;
  for(let i=0;i<rows.length;i++){
    if(chosen.includes(i))continue;
    let gain=0;for(const p of covers[i])if(uncovered.has(p))gain++;
    if(gain>bestGain){bestGain=gain;best=i;}
  }
  if(best<0||bestGain<=0)throw new Error("separator cover stuck");
  chosen.push(best);for(const p of covers[best])uncovered.delete(p);
}
let changed=true;
while(changed){
  changed=false;
  for(let ci=chosen.length-1;ci>=0;ci--){
    const trial=chosen.filter((_,j)=>j!==ci);
    let ok=true;
    for(const [a,b] of fullPairs){
      const sa=signatures.get(candidates[a].name).sig,sb=signatures.get(candidates[b].name).sig;
      if(!trial.some(i=>sa[i]!==sb[i])){ok=false;break;}
    }
    if(ok){chosen.splice(ci,1);changed=true;}
  }
}

const sep=chosen.map(i=>({
  name:rows[i].name,expected:rows[i].expected,
  separates:[...covers[i]].length
}));

// Verify the resulting suite preserves the full partition exactly.
let partitionExact=true;
for(let a=0;a<n;a++)for(let b=a+1;b<n;b++){
  const sa=signatures.get(candidates[a].name).sig,sb=signatures.get(candidates[b].name).sig;
  const full=sa.some((v,i)=>v!==sb[i]);
  const small=chosen.some(i=>sa[i]!==sb[i]);
  if(full!==small)partitionExact=false;
}

console.log("VERIFIED_SEMANTIC_DISTILLATION_MAP "+JSON.stringify({
  arena_sha256:sha,
  authorityCases:rows.length,
  candidateFamily:candidates.map(c=>c.name),
  candidateCount:candidates.length,
  fullSeparatedPairs:fullPairs.length,
  necessity,
  separatorSuite:{
    size:chosen.length,
    names:sep,
    partitionExact,
    claim_boundary:"This suite preserves the verdict partition of this exact current candidate family only. It is not a universal Lean equivalence basis; every new candidate must replay the full authority family before the suite can be updated."
  }
}));
