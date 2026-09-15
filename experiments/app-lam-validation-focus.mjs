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
    if m.isfile() and m.name.endswith("good/perf/app-lam.ndjson"):
      row={"name":m.name,"input":a.extractfile(m).read().decode("utf-8")};break
print(json.dumps(row))
`;
const row=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));
if(!row) throw new Error("app-lam missing");

const proto=K.Kernel.prototype;
const originalRun=proto.run, originalValidate=proto.validate;

function paramsKey(kernel){ return [...(kernel.params??[])].sort().join("\u0000"); }
function install(mode){
  proto.run=originalRun; proto.validate=originalValidate;
  if(mode==="baseline") return;
  proto.run=function(...args){
    this.__validationOk=new WeakMap();
    return originalRun.apply(this,args);
  };
  proto.validate=function(e){
    if(!Array.isArray(e)) return originalValidate.call(this,e);
    this.__validationOk??=new WeakMap();
    const key=paramsKey(this);
    let ok=this.__validationOk.get(e);
    if(ok?.has(key)) return;
    const out=originalValidate.call(this,e);
    ok=this.__validationOk.get(e);
    if(!(ok instanceof Set)){ok=new Set();this.__validationOk.set(e,ok);}
    ok.add(key);
    return out;
  };
}

for(const budget of [1_000_000,1_250_000,1_500_000,2_000_000,3_000_000,5_000_000]){
  for(const mode of ["baseline","validation-free"]){
    install(mode);
    const r=K.checkExport(row.input,caps,budget);
    console.log("APP_LAM_VALIDATION_FOCUS "+JSON.stringify({mode,budget,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:r.elapsed_ms??null}));
  }
}
proto.run=originalRun;proto.validate=originalValidate;
