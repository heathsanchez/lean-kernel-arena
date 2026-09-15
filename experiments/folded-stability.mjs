import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import {checkExport} from "../genesis/kernel.mjs";
const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
const data=Buffer.from(await response.arrayBuffer());
if(createHash("sha256").update(data).digest("hex")!==expectedHash)throw new Error("corpus changed");
const py=String.raw`
import io,tarfile,json,sys
data=sys.stdin.buffer.read()
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    if m.isfile() and m.name.endswith("good/perf/folded-constant-first.ndjson"):
      print(json.dumps(a.extractfile(m).read().decode("utf-8")));break
`;
const input=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:10000000,timeout:10000}));
for(let i=0;i<8;i++){
  const r=checkExport(input,caps,1_000_000);
  console.log("FOLDED_STABILITY "+JSON.stringify({i,status:r.status,reason:r.reason,steps:r.steps??null,
    constructed:r.constructed??null,diagnostic_error:r.diagnostic_error??null,
    fallback_mode:r.fallback_mode??null,stack_attempt_reason:r.stack_attempt_reason??null}));
}
