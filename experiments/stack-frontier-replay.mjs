import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const wanted=new Set([
  "good/perf/args-before-unfold.ndjson",
  "good/perf/folded-constant-first.ndjson",
  "good/perf/folded-constant-last.ndjson",
  "good/perf/unroll-versus-evaluate.ndjson",
  "good/perf/beta-ladder.ndjson",
  "good/perf/shift-cascade.ndjson",
  "good/perf/church-numerals.ndjson",
  "good/perf/repeated-subproblem.ndjson"
]);

const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok) throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer());
const sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash) throw new Error("Arena corpus changed");
const py=String.raw`
import io,tarfile,json,sys
data=sys.stdin.buffer.read(); rows=[]
wanted=set(json.loads(sys.argv[1]))
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    if m.name in wanted:
      rows.append({"name":m.name,"expected":"ACCEPT","input":a.extractfile(m).read().decode("utf-8")})
print(json.dumps(rows))
`;
const rows=JSON.parse(execFileSync("python3",["-c",py,JSON.stringify([...wanted])],{input:data,maxBuffer:50000000,timeout:10000}));
if(rows.length!==wanted.size) throw new Error("frontier row count "+rows.length);

const results=[];
for(const row of rows){
  const r=K.checkExport(row.input,caps,1_000_000);
  if(r.status!=="UNKNOWN"&&r.status!==row.expected) throw new Error("wrong "+JSON.stringify({name:row.name,r}));
  const item={name:row.name,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
    fallback_mode:r.fallback_mode??null,retained_reason:r.retained_reason??null,
    retained_steps:r.retained_steps??null,stack_attempt_reason:r.stack_attempt_reason??null,
    stack_attempt_steps:r.stack_attempt_steps??null,fallback_attempt_reason:r.fallback_attempt_reason??null,
    fallback_attempt_steps:r.fallback_attempt_steps??null,diagnostic_error:r.diagnostic_error??null};
  results.push(item);
  console.log("STACK_FRONTIER "+JSON.stringify(item));
}
console.log("STACK_FRONTIER_SUMMARY "+JSON.stringify({arena_sha256:sha,results}));
