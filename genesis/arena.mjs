// Independent published Arena cases; no Lean/mathlib build.
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import {checkExport} from "./kernel.mjs";
import {checkExport as previousCheckExport} from "./reference-v1.mjs";
const caps=JSON.parse(readFileSync(new URL("./evidence/retained.json",import.meta.url),"utf8"));
const url="https://arena.lean-lang.org/lean-arena-tests.tar.gz";
const response=await fetch(url,{signal:AbortSignal.timeout(15000)});
if(!response.ok) throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer());
if(data.length>10000000) throw new Error("unexpected corpus size");
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
if(createHash("sha256").update(data).digest("hex")!==expectedHash) throw new Error("Arena corpus changed; freeze a new baseline before comparison");
const python=String.raw`
import io, tarfile, json, sys
data=sys.stdin.buffer.read()
rows=[]
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as archive:
    for member in archive:
        parts=member.name.split("/")
        if not member.isfile() or not member.name.endswith(".ndjson") or member.size>2000000:
            continue
        outcome="ACCEPT" if "good" in parts else "REJECT" if "bad" in parts else None
        if outcome is not None:
            rows.append({"name":member.name,"expected":outcome,"input":archive.extractfile(member).read().decode("utf-8")})
print(json.dumps(rows))
`;
const rows=JSON.parse(execFileSync("python3",["-c",python],{input:data,maxBuffer:50000000,timeout:10000}));
if(!rows.length) throw new Error("empty Arena corpus");
const counts={ACCEPT:0,REJECT:0,UNKNOWN:0};const results=[];const start=Date.now();
for(const row of rows) {
  const r=checkExport(row.input,caps,1000000);
  const before=previousCheckExport(row.input,caps.filter(c=>c!=="universes"),50000);
  if(before.status!=="UNKNOWN" && r.status!==before.status) {
    console.error("PROTECTED_ARENA_REGRESSION "+JSON.stringify({name:row.name,before,after:r}));
    writeFileSync(new URL("./evidence/arena-counterexample.ndjson",import.meta.url),row.input);
    process.exit(1);
  }
  counts[r.status]++;
  results.push({name:row.name,expected:row.expected,...r});
  if(r.status!=="UNKNOWN" && r.status!==row.expected) {
    console.error("ARENA_COUNTEREXAMPLE "+JSON.stringify(results.at(-1)));
    writeFileSync(new URL("./evidence/arena-counterexample.ndjson",import.meta.url),row.input);
    writeFileSync(new URL("./evidence/arena-failure.json",import.meta.url),JSON.stringify(results.at(-1),null,2));
    process.exit(1);
  }
}
const report={url,sha256:createHash("sha256").update(data).digest("hex"),counts,total:rows.length,elapsed_ms:Date.now()-start,results,
  scope:"Finite Arena integration. UNKNOWN is explicit missing coverage, never a correctness pass."};
writeFileSync(new URL("./evidence/arena.json",import.meta.url),JSON.stringify(report,null,2));
console.log("ARENA_FRAGMENT_PASS "+JSON.stringify({counts,total:rows.length,elapsed_ms:report.elapsed_ms,corpus_sha256:report.sha256}));

const frontier={};
for(const r of results.filter(r=>r.status==="UNKNOWN")) {
  const group=frontier[r.reason]??={count:0,examples:[]};
  group.count++;
  if(group.examples.length<3) group.examples.push(r.name);
}
writeFileSync(new URL("./evidence/frontier.json",import.meta.url),JSON.stringify(frontier,null,2));
const noninductiveFrontier=rows.flatMap(row=>{
  const result=results.find(r=>r.name===row.name);
  if(result?.status!=="UNKNOWN" || ["declaration-frontier:inductive","inductive-semantics-frontier"].includes(result.reason)) return [];
  return [{name:row.name,expected:row.expected,reason:result.reason,input:row.input}];
});
writeFileSync(new URL("./evidence/noninductive-frontier.json",import.meta.url),
  JSON.stringify(noninductiveFrontier,null,2));

// Preserve the exact first blocked inductive record for diagnosis without changing
// checker semantics. The next growth step is chosen from this residual, not guessed.
const inductiveFrontier=[];
for(const row of rows) {
  const result=results.find(r=>r.name===row.name);
  if(result?.status!=="UNKNOWN" || !["declaration-frontier:inductive","inductive-semantics-frontier"].includes(result.reason)) continue;
  let first=null;
  for(const line of row.input.split(/\r?\n/)) {
    if(!line.trim()) continue;
    const record=JSON.parse(line);
    if(Object.prototype.hasOwnProperty.call(record,"inductive")) { first=record.inductive; break; }
  }
  inductiveFrontier.push({name:row.name,expected:row.expected,first_inductive:first,input:row.input});
}
writeFileSync(new URL("./evidence/inductive-frontier.json",import.meta.url),
  JSON.stringify(inductiveFrontier,null,2));

for(const [reason,group] of Object.entries(frontier).sort((a,b)=>b[1].count-a[1].count))
  console.log("NEXT_RESIDUAL "+JSON.stringify({reason,...group}));
if(inductiveFrontier.length) {
  const signatures={},profiles={},byExpected={ACCEPT:0,REJECT:0};
  const names={ACCEPT:[],REJECT:[]};
  for(const x of inductiveFrontier) {
    const r=x.first_inductive??{};
    byExpected[x.expected]=(byExpected[x.expected]??0)+1;
    names[x.expected].push(x.name);
    const sig=JSON.stringify(Object.keys(r).sort().map(k=>[k,Array.isArray(r[k])?r[k].length:typeof r[k]]));
    signatures[sig]=(signatures[sig]??0)+1;
    const t=r.types?.[0]??{}, rec=r.recs?.[0]??{};
    const profile=JSON.stringify({
      expected:x.expected,ctors:r.ctors?.length??-1,
      params:t.numParams??null,indices:t.numIndices??null,
      levels:t.levelParams?.length??null,nested:t.numNested??null,
      recursive:t.isRec??null,reflexive:t.isReflexive??null,
      recParams:rec.numParams??null,recIndices:rec.numIndices??null,
      motives:rec.numMotives??null,minors:rec.numMinors??null,
      rules:rec.rules?.length??null,k:rec.k??null
    });
    profiles[profile]=(profiles[profile]??0)+1;
  }
  console.log("INDUCTIVE_FRONTIER_SHAPES "+JSON.stringify(
    Object.entries(signatures).sort((a,b)=>b[1]-a[1]).map(([signature,count])=>({count,signature}))));
  console.log("INDUCTIVE_FRONTIER_EXPECTED "+JSON.stringify(byExpected));
  const actual={};
  for(const x of inductiveFrontier) {
    const rr=results.find(r=>r.name===x.name);
    const n=rr?.frontier_inductive?.name??"<unknown>";
    const key=JSON.stringify([x.expected,n]);
    actual[key]=(actual[key]??0)+1;
  }
  console.log("ACTUAL_INDUCTIVE_FRONTIER "+JSON.stringify(
    Object.entries(actual).sort((a,b)=>b[1]-a[1]).map(([key,count])=>{
      const [expected,name]=JSON.parse(key); return {count,expected,name};
    })));
  console.log("INDUCTIVE_FRONTIER_PROFILES "+JSON.stringify(
    Object.entries(profiles).sort((a,b)=>b[1]-a[1]).map(([profile,count])=>({count,...JSON.parse(profile)}))));
  console.log("INDUCTIVE_FRONTIER_NAMES "+JSON.stringify(names));
  const wanted=new Set([
    "good/tutorial/037_boolType.ndjson",
    "good/tutorial/040_prodType.ndjson",
    "good/tutorial/043_eqType.ndjson",
    "good/tutorial/044_natDef.ndjson",
    "bad/bogus1.ndjson",
    "bad/nat-rec-rules.ndjson"
  ]);
  for(const x of inductiveFrontier.filter(x=>wanted.has(x.name)))
    console.log("INDUCTIVE_SAMPLE "+JSON.stringify({name:x.name,expected:x.expected,bundle:x.first_inductive}));
}
