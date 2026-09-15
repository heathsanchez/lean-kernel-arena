import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";
import {Stop} from "../genesis/kernel-base.mjs";

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
    if m.isfile() and m.name.endswith("/good/perf/irrelevance-before-evaluation.ndjson"):
      row={"name":m.name,"input":a.extractfile(m).read().decode("utf-8")};break
print(json.dumps(row))
`;
const row=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));
if(!row) throw new Error("irrelevance case missing");

const proto=K.Kernel.prototype, retained=proto.equal;

function install(cap){
  proto.equal=retained;
  if(cap===null)return;
  proto.equal=function(a,b,ctx=[]){
    if(this._earlyIrrelSpeculating || !this.caps.has("proof-irrelevance"))
      return retained.call(this,a,b,ctx);
    if(this.same(a,b)) return;
    const snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};
    this.budget=Math.min(this.budget,this.steps+cap);
    this._earlyIrrelSpeculating=true;
    try{
      const ta=this.proofType(a,ctx),tb=this.proofType(b,ctx);
      if(ta!==null&&tb!==null){
        retained.call(this,ta,tb,ctx);
        this._earlyIrrelSpeculating=false;
        this.budget=snap.budget;
        return;
      }
    }catch(e){
      if(!(e instanceof Stop||e instanceof RangeError))throw e;
    }
    this._earlyIrrelSpeculating=false;
    this.steps=snap.steps;this.budget=snap.budget;this.conversionFrontier=snap.frontier;
    return retained.call(this,a,b,ctx);
  };
}

for(const cap of [null,5000,10000,25000,50000,100000,250000]){
  install(cap);
  const r=K.checkExport(row.input,caps,1_000_000);
  console.log("IRRELEVANCE_FIRST_FOCUS "+JSON.stringify({cap:cap??"baseline",status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:r.elapsed_ms??null}));
}
proto.equal=retained;
