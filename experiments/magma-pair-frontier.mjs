// Diagnostic only: print the exact conversion frontiers now exposed for
// the two magma-list-pair residuals by the retained execution caches.
import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const targets=new Set([
  "good/perf/magma-list-pair-n7.ndjson",
  "good/perf/magma-list-pair-n21.ndjson"
]);

const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok) throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer());
const sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash) throw new Error("Arena corpus changed");
const py=String.raw`
import io,tarfile,json,sys
data=sys.stdin.buffer.read(); rows=[]
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    p="/".join(m.name.split("/")[-3:])
    if m.isfile() and m.name.endswith(".ndjson") and p in {
      "good/perf/magma-list-pair-n7.ndjson",
      "good/perf/magma-list-pair-n21.ndjson"
    }:
      rows.append({"name":p,"input":a.extractfile(m).read().decode("utf-8")})
print(json.dumps(rows))
`;
const rows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));
if(rows.length!==2) throw new Error("target rows missing: "+rows.map(x=>x.name));

function headSummary(s) {
  try {
    const e=JSON.parse(s);
    let cur=e,args=0;
    while(Array.isArray(cur)&&cur[0]==="app"){args++;cur=cur[1];}
    return {tag:Array.isArray(cur)?cur[0]:typeof cur,
      head:Array.isArray(cur)&&cur[0]==="const"?cur[1]:cur,
      app_args:args};
  } catch {
    return {parse:"truncated"};
  }
}

for(const row of rows.sort((a,b)=>a.name.localeCompare(b.name))) {
  const r=K.checkExport(row.input,caps,1_000_000);
  const f=r.conversion_frontier??null;
  console.log("MAGMA_PAIR_FRONTIER "+JSON.stringify({
    name:row.name,status:r.status,reason:r.reason,steps:r.steps,
    constructed:r.constructed,frontier_declaration:r.frontier_declaration??null,
    frontier:f?{
      ctx_depth:f.ctx_depth,
      left_bytes:f.left_bytes,right_bytes:f.right_bytes,
      left_head:headSummary(f.left),right_head:headSummary(f.right),
      left:f.left,right:f.right
    }:null
  }));
}
