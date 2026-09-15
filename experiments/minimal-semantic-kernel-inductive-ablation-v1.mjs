import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const url="https://arena.lean-lang.org/lean-arena-tests.tar.gz";
const expectedHash="0cdb181ce17bc4f685beea8d3ccb90675ecc029cae9c4dc86629d2adbcb6e8dd";
const response=await fetch(url,{signal:AbortSignal.timeout(15000)});
if(!response.ok)throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer());
const sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash)throw new Error("Arena corpus changed: got "+sha+" expected "+expectedHash);

const py=String.raw`
import io,tarfile,json,sys
data=sys.stdin.buffer.read();rows=[]
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    p=m.name.split("/")
    if not m.isfile() or not m.name.endswith(".ndjson") or m.size>2000000: continue
    e="ACCEPT" if "good" in p else "REJECT" if "bad" in p else None
    if e: rows.append({"name":m.name,"expected":e,"input":a.extractfile(m).read().decode("utf-8")})
print(json.dumps(rows))
`;
const rows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));

function classify(row){
  let bundles=0,types=0,mutual=0,nested=0,single=0,structureLike=0,recursive=0,propLike=0,projections=0;
  for(const line of row.input.split(/\r?\n/)){
    if(!line.trim())continue;
    const r=JSON.parse(line);
    if(r.proj)projections++;
    if(!r.inductive)continue;
    const b=r.inductive;bundles++;
    const ts=Array.isArray(b.types)?b.types:[];
    types+=ts.length;
    if(ts.length>1)mutual++;
    else if(ts.length===1)single++;
    if(ts.some(t=>(t?.numNested??0)>0))nested++;
    if(ts.some(t=>t?.isRec===true))recursive++;
    if(ts.some(t=>t?.type!==undefined && t?.isRec===false && (t?.ctors?.length??0)===1))structureLike++;
    if(ts.some(t=>t?.isRec===false))propLike++;
  }
  return {bundles,types,mutual,nested,single,structureLike,recursive,propLike,projections};
}

function runSet(cset,selected=rows,budget=1000000){
  const results=[];let wrong=0;
  for(const row of selected){
    const r=K.checkExport(row.input,cset,budget);
    if(r.status!=="UNKNOWN"&&r.status!==row.expected)wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,steps:r.steps??null,
      frontier_declaration:r.frontier_declaration??null});
  }
  const counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  for(const r of results)counts[r.status]++;
  return {counts,wrong,results};
}

const census=rows.map(r=>({name:r.name,expected:r.expected,...classify(r)}));
const aggregate={cases:rows.length,casesWithInductive:0,casesWithMutual:0,casesWithNested:0,casesWithProjection:0,
  bundles:0,types:0,mutualBundles:0,nestedBundles:0,singleBundles:0,structureLike:0,recursive:0};
for(const c of census){
  if(c.bundles)aggregate.casesWithInductive++;
  if(c.mutual)aggregate.casesWithMutual++;
  if(c.nested)aggregate.casesWithNested++;
  if(c.projections)aggregate.casesWithProjection++;
  aggregate.bundles+=c.bundles;aggregate.types+=c.types;aggregate.mutualBundles+=c.mutual;
  aggregate.nestedBundles+=c.nested;aggregate.singleBundles+=c.single;aggregate.structureLike+=c.structureLike;
  aggregate.recursive+=c.recursive;
}

const baseline=runSet(caps);
if(baseline.wrong)throw new Error("baseline wrong verdicts: "+baseline.wrong);
const baselineMap=new Map(baseline.results.map(r=>[r.name,r]));
const relevantRows=rows.filter(r=>{
  const c=census.find(x=>x.name===r.name);
  return c.bundles||c.projections;
});

const inductiveCaps=[
  "single-inductives","enum-inductives","empty-inductives","prop-inductives",
  "reflexive-inductives","inductive-reduction","rule-k","unit-eta","structure-eta","projections"
].filter(c=>caps.includes(c));

const variants=[];
function addVariant(name,removed){
  const cset=caps.filter(c=>!removed.includes(c));
  const rr=runSet(cset,relevantRows);
  const lost=[],changed=[],retainedResolved=[];
  for(const r of rr.results){
    const b=baselineMap.get(r.name);
    if(b.status!=="UNKNOWN"){
      if(r.status==="UNKNOWN")lost.push({name:r.name,before:b.status,reason:r.reason});
      else if(r.status!==b.status)changed.push({name:r.name,before:b.status,after:r.status,reason:r.reason});
      else retainedResolved.push(r.name);
    }
  }
  variants.push({name,removed,counts:rr.counts,wrong:rr.wrong,lostCount:lost.length,changedCount:changed.length,
    retainedResolvedCount:retainedResolved.length,lost:lost.slice(0,80),changed});
}
for(const c of inductiveCaps)addVariant("drop:"+c,[c]);
const general=["single-inductives","enum-inductives","empty-inductives","prop-inductives",
  "reflexive-inductives","inductive-reduction","rule-k"].filter(c=>caps.includes(c));
addVariant("structures+Nat-ish:drop-general-inductives",general);
addVariant("drop-all-inductive-adjacent",inductiveCaps);

const mutualNames=census.filter(c=>c.mutual).map(c=>c.name);
const nestedNames=census.filter(c=>c.nested).map(c=>c.name);
const mutualBaseline=baseline.results.filter(r=>mutualNames.includes(r.name));
const nestedBaseline=baseline.results.filter(r=>nestedNames.includes(r.name));

const report={
  experiment:"minimal-semantic-kernel-inductive-ablation-v1",
  arena_sha256:sha,
  retainedCapabilities:caps,
  baselineCounts:baseline.counts,
  census:aggregate,
  mutualBaseline:mutualBaseline.map(r=>({name:r.name,expected:r.expected,status:r.status,reason:r.reason})),
  nestedBaseline:nestedBaseline.map(r=>({name:r.name,expected:r.expected,status:r.status,reason:r.reason})),
  inductiveCaps,
  variants,
  claim_boundary:"Diagnostic ablation only. Removing a capability may turn a formerly decided case into UNKNOWN; no removed capability is replaced by a translator in this experiment. A primitive is shown necessary only for current native execution on this protected corpus, not mathematically necessary in principle."
};
console.log("MINIMAL_SEMANTIC_KERNEL_INDUCTIVE_ABLATION "+JSON.stringify(report));
