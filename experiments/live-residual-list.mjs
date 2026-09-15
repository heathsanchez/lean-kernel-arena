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
    p=m.name.split("/")
    if not m.isfile() or not m.name.endswith(".ndjson") or m.size>2000000: continue
    e="ACCEPT" if "good" in p else "REJECT" if "bad" in p else None
    if e: rows.append({"name":m.name,"expected":e,"input":a.extractfile(m).read().decode("utf-8")})
print(json.dumps(rows))
`;
const rows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));
const counts={ACCEPT:0,REJECT:0,UNKNOWN:0}, unknown=[];
for(const row of rows){
  const r=checkExport(row.input,caps,1_000_000);
  counts[r.status]=(counts[r.status]??0)+1;
  if(r.status!=="UNKNOWN" && r.status!==row.expected) throw new Error("wrong verdict "+row.name);
  if(r.status==="UNKNOWN") unknown.push({
    name:row.name,expected:row.expected,reason:r.reason,steps:r.steps??null,
    constructed:r.constructed??null,fallback_mode:r.fallback_mode??null,
    retained_reason:r.retained_reason??null,retained_steps:r.retained_steps??null,
    stack_attempt_reason:r.stack_attempt_reason??null,stack_attempt_steps:r.stack_attempt_steps??null,
    fallback_attempt_reason:r.fallback_attempt_reason??null,fallback_attempt_steps:r.fallback_attempt_steps??null
  });
}
console.log("LIVE_RESIDUAL_LIST "+JSON.stringify({arena_sha256:sha,counts,unknown}));
