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
  const r=checkExport(row.input,caps,50000);
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
for(const [reason,group] of Object.entries(frontier).sort((a,b)=>b[1].count-a[1].count))
  console.log("NEXT_RESIDUAL "+JSON.stringify({reason,...group}));
