import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";
import {Stop,UNKNOWN} from "../genesis/kernel-base.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok)throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer()),sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash)throw new Error("Arena corpus changed");
const py=String.raw`
import io,tarfile,json,sys
wanted={"good/perf/magma-list-pair-n7.ndjson","good/perf/magma-list-pair-n21.ndjson"}
data=sys.stdin.buffer.read();rows=[]
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    p="/".join(m.name.split("/")[-3:])
    if m.isfile() and p in wanted:
      rows.append({"name":p,"input":a.extractfile(m).read().decode("utf-8")})
print(json.dumps(rows))
`;
const rows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));

const proto=K.Kernel.prototype,retained=proto.equal;
proto.equal=function(a,b,ctx=[]){
  if(this.localDefs || (this._projThresholdDepth??0)>0)
    return retained.call(this,a,b,ctx);
  try{
    return retained.call(this,a,b,ctx);
  }catch(e){
    if(!(e instanceof Stop)||e.status!==UNKNOWN||e.message!=="conversion-frontier")throw e;
    const original=e,snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier};
    let x,y;
    try{x=this.normal(a);y=this.normal(b);}catch(_){throw original;}
    if(!Array.isArray(x)||!Array.isArray(y)||x[0]!=="proj"||y[0]!=="proj"||x[1]!==y[1]||x[2]!==y[2])
      throw original;
    this._projThresholdDepth=1;
    try{
      this.equal(x[3],y[3],ctx);
      this._projThresholdDepth=0;
      return;
    }catch(_){
      this._projThresholdDepth=0;
      this.conversionFrontier=snap.frontier;
      throw original;
    }
  }
};

for(const budget of [1000000,2000000,4000000]){
  for(const row of rows){
    const r=K.checkExport(row.input,caps,budget);
    console.log("PROJECTION_THRESHOLD "+JSON.stringify({
      budget,name:row.name,status:r.status,reason:r.reason,steps:r.steps??null,
      constructed:r.constructed??null,frontier_declaration:r.frontier_declaration??null
    }));
  }
}
proto.equal=retained;
