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
if(!row)throw new Error("app-lam missing");

const proto=K.Kernel.prototype, retainedRun=proto.run, retainedValidate=proto.validate;
function paramsKey(k){return [...(k.params??[])].sort().join("\u0000");}
function slot(k,e,key){
  if(!Array.isArray(e))return null;
  k.__validationDag??=new WeakMap();
  let s=k.__validationDag.get(e);
  if(!(s instanceof Set)){s=new Set();k.__validationDag.set(e,s);}
  return {has:()=>s.has(key),set:()=>s.add(key)};
}
function install(candidate){
  proto.run=retainedRun;proto.validate=retainedValidate;
  if(!candidate)return;
  proto.run=function(...args){this.__validationDag=new WeakMap();return retainedRun.apply(this,args);};
  proto.validate=function(root){
    const key=paramsKey(this),work=[{kind:"visit",e:root}];
    while(work.length){
      const f=work.pop(),e=f.e,s=slot(this,e,key);
      if(f.kind==="done"){s?.set();continue;}
      if(s?.has())continue;
      if(Array.isArray(e)&&["sort","var","const","nat","strlit"].includes(e[0])){
        retainedValidate.call(this,e);s?.set();continue;
      }
      this.tick();
      if(!Array.isArray(e)||typeof e[0]!=="string")this.reject("malformed-term");
      const arities={sort:2,var:2,const:2,nat:2,strlit:2,proj:4,pi:3,lam:3,app:3,let:4};
      if(!(e[0] in arities))this.unknown("syntax:"+e[0]);
      if(e.length!==arities[e[0]]&&!(e[0]==="const"&&e.length===3))this.reject("malformed-arity");
      work.push({kind:"done",e});
      if(e[0]==="proj"){
        this.need("projections");
        if(typeof e[1]!=="string"||!Number.isSafeInteger(e[2])||e[2]<0)this.reject("malformed-projection");
        work.push({kind:"visit",e:e[3]});
      }else for(let i=e.length-1;i>=1;i--)work.push({kind:"visit",e:e[i]});
    }
  };
}
for(const budget of [1000000,2000000,5000000,10000000]){
  for(const candidate of [false,true]){
    install(candidate);
    const r=K.checkExport(row.input,caps,budget);
    console.log("APP_LAM_VALIDATION_DAG "+JSON.stringify({candidate,budget,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:r.elapsed_ms??null,fallback_mode:r.fallback_mode??null}));
  }
}
proto.run=retainedRun;proto.validate=retainedValidate;
