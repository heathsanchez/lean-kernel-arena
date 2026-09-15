import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";
import {Stop} from "../genesis/kernel-base.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok) throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer()),sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash) throw new Error("Arena corpus changed");
const py=String.raw`
import io,tarfile,json,sys
wanted={"irrelevance-before-evaluation.ndjson","args-before-unfold.ndjson",
"folded-constant-first.ndjson","unroll-versus-evaluate.ndjson"}
data=sys.stdin.buffer.read();rows=[]
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    if not m.isfile() or m.name.rsplit("/",1)[-1] not in wanted: continue
    p=m.name.split("/");e="ACCEPT" if "good" in p else "REJECT" if "bad" in p else None
    if e: rows.append({"name":m.name,"expected":e,"input":a.extractfile(m).read().decode("utf-8")})
print(json.dumps(rows))
`;
const rows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));
const proto=K.Kernel.prototype, retained=proto.equal;

function install(mode){
  proto.equal=retained;
  if(mode==="baseline") return;
  proto.equal=function(a,b,ctx=[]){
    if(this.localDefs || !this.caps.has("proof-irrelevance"))
      return retained.call(this,a,b,ctx);
    if(mode==="scoped" && (this._lazyDeltaDepth??0)===0 && (this._rigidTypeSpineDepth??0)===0)
      return retained.call(this,a,b,ctx);
    if(this.same(a,b)) return;

    const snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};
    try{
      const ta=this.proofType(a,ctx),tb=this.proofType(b,ctx);
      if(ta!==null&&tb!==null){
        if(this.same(ta,tb)) return;
        retained.call(this,ta,tb,ctx);
        return;
      }
    }catch(e){
      if(!(e instanceof Stop||e instanceof RangeError)) throw e;
    }
    this.steps=snap.steps;
    this.budget=snap.budget;
    this.conversionFrontier=snap.frontier;
    return retained.call(this,a,b,ctx);
  };
}

for(const mode of ["baseline","global","scoped"]){
  install(mode);
  for(const row of rows){
    const r=K.checkExport(row.input,caps,1_000_000);
    console.log("EARLY_PROOF_FOCUS "+JSON.stringify({mode,name:row.name,expected:row.expected,
      status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
      correct:r.status==="UNKNOWN"||r.status===row.expected,diagnostic_error:r.diagnostic_error??null}));
  }
}
proto.equal=retained;
