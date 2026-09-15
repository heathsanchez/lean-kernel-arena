import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import {checkExport} from "../genesis/kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
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
    if m.isfile() and m.name.endswith(".ndjson") and "refute-cheap-" in m.name:
      rows.append({"name":m.name,"input":a.extractfile(m).read().decode("utf-8")})
print(json.dumps(sorted(rows,key=lambda x:x["name"])))
`;
const rows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));
if(rows.length!==2) throw new Error("expected 2 refutation rows, got "+rows.length);

const budgets=[2_000_000,4_000_000,8_000_000];
for(const row of rows){
  const attempts=[];
  for(const budget of budgets){
    const t0=Date.now();
    const r=checkExport(row.input,caps,budget);
    const item={budget,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
      elapsed_ms:Date.now()-t0,frontier_declaration:r.frontier_declaration??null,
      conversion_frontier:r.conversion_frontier??null,fallback_mode:r.fallback_mode??null,
      fallback_attempt_reason:r.fallback_attempt_reason??null,fallback_attempt_steps:r.fallback_attempt_steps??null};
    attempts.push(item);
    console.log("REFUTE_COMPLETION_ATTEMPT "+JSON.stringify({name:row.name,...item}));
    if(r.status!=="UNKNOWN") break;
  }
  console.log("REFUTE_COMPLETION_CLIFF "+JSON.stringify({arena_sha256:sha,name:row.name,attempts}));
}
