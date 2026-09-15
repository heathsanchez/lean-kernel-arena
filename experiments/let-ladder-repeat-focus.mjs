import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok) throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer());
const sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash) throw new Error("Arena corpus changed");
const py=String.raw`
import io,tarfile,json,sys
data=sys.stdin.buffer.read(); row=None
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    if m.isfile() and m.name.endswith("good/perf/let-ladder.ndjson"):
      row={"name":m.name,"input":a.extractfile(m).read().decode("utf-8")};break
print(json.dumps(row))
`;
const row=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));
if(!row) throw new Error("let-ladder missing");

const proto=K.Kernel.prototype;
const originalRun=proto.run;
let localRuns=[];

proto.run=function(...args){
  const r=originalRun.apply(this,args);
  if(this.localDefs===true){
    localRuns.push({
      status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
      diagnostic_error:r.diagnostic_error??null
    });
  }
  return r;
};

for(let i=0;i<8;i++){
  localRuns=[];
  const r=K.checkExport(row.input,caps,1_000_000);
  console.log("LET_LADDER_REPEAT "+JSON.stringify({
    iteration:i+1,status:r.status,reason:r.reason,steps:r.steps??null,
    fallback_mode:r.fallback_mode??null,retained_reason:r.retained_reason??null,
    retained_steps:r.retained_steps??null,
    fallback_attempt_reason:r.fallback_attempt_reason??null,
    fallback_attempt_steps:r.fallback_attempt_steps??null,
    localRuns
  }));
}
proto.run=originalRun;
