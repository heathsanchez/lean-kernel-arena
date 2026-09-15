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
wanted={"args-before-unfold.ndjson","folded-constant-first.ndjson","folded-constant-last.ndjson",
"refute-cheap-first.ndjson","refute-cheap-last.ndjson","unroll-versus-evaluate.ndjson"}
data=sys.stdin.buffer.read(); rows=[]
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    if not m.isfile(): continue
    base=m.name.rsplit("/",1)[-1]
    if base not in wanted: continue
    p=m.name.split("/"); e="ACCEPT" if "good" in p else "REJECT" if "bad" in p else None
    if e: rows.append({"name":m.name,"expected":e,"input":a.extractfile(m).read().decode("utf-8")})
print(json.dumps(rows))
`;
const rows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));
const proto=K.Kernel.prototype, retained=proto.equal;
function rawSpine(e){const args=[];while(Array.isArray(e)&&e[0]==="app"){args.push(e[2]);e=e[1];}args.reverse();return {head:e,args};}
function snap(k){return {steps:k.steps,frontier:k.conversionFrontier};}
function restore(k,s){k.steps=s.steps;k.conversionFrontier=s.frontier;}
function declined(e){return e instanceof Stop||e instanceof RangeError;}
function install(candidate){
  proto.equal=retained;
  if(!candidate)return;
  proto.equal=function(a,b,ctx=[]){
    if(this.same(a,b)) return;
    const sa=rawSpine(a),sb=rawSpine(b);
    if(sa.args.length>0&&sa.args.length===sb.args.length&&(sa.head===sb.head||this.same(sa.head,sb.head))){
      const s=snap(this);
      try{
        for(let i=0;i<sa.args.length;i++) this.equal(sa.args[i],sb.args[i],ctx);
        return;
      }catch(e){if(!declined(e))throw e;restore(this,s);}
    }
    return retained.call(this,a,b,ctx);
  };
}
for(const row of rows){
  install(false); const b=K.checkExport(row.input,caps,1_000_000);
  install(true); const c=K.checkExport(row.input,caps,1_000_000);
  console.log("SPINE_FOCUS "+JSON.stringify({name:row.name,expected:row.expected,
    baseline:{status:b.status,reason:b.reason,steps:b.steps??null},
    candidate:{status:c.status,reason:c.reason,steps:c.steps??null},
    candidate_correct:c.status==="UNKNOWN"||c.status===row.expected}));
}
proto.equal=retained;
