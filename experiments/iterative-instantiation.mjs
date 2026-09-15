// Prospective separator for the one recursive term walker not covered by stack-safe.mjs:
// universe-instantiating declaration bodies. Exact semantics, explicit work stack.
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
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
if(rows.length!==188) throw new Error("Arena row count changed: "+rows.length);

const proto=K.Kernel.prototype;
const original=proto.instantiateDeclaration;

function levelSub(kernel,u,sub){
  kernel.tick();
  if(typeof u==="number") return u;
  if(u[0]==="param") return sub.has(u[1])?sub.get(u[1]):u;
  return [u[0],...u.slice(1).map(x=>levelSub(kernel,x,sub))];
}

function install(enabled){
  proto.instantiateDeclaration=original;
  if(!enabled) return;
  proto.instantiateDeclaration=function(ref,term){
    this.tick();
    const d=this.env.get(ref[1]),ps=d.levelParams??[],args=ref[2]??[];
    if(ps.length!==args.length) this.reject("universe-arity");
    if(!ps.length) return term;
    this.need("universes");
    const sub=new Map(ps.map((p,i)=>[p,args[i]]));
    const work=[{kind:"visit",e:term}],vals=[];
    while(work.length){
      const f=work.pop();
      if(f.kind==="build"){
        if(f.tag==="proj"){
          const x=vals.pop();
          vals.push(this.make("proj",f.name,f.index,x));
        } else {
          const xs=new Array(f.n);
          for(let i=f.n-1;i>=0;i--) xs[i]=vals.pop();
          vals.push(this.make(f.tag,...xs));
        }
        continue;
      }
      const e=f.e;
      this.tick();
      if(e[0]==="sort"){
        vals.push(this.make("sort",levelSub(this,e[1],sub)));
      } else if(e[0]==="const"){
        vals.push(e.length===2?e:this.make("const",e[1],e[2].map(u=>levelSub(this,u,sub))));
      } else if(e[0]==="var"||e[0]==="nat"||e[0]==="strlit"){
        vals.push(e);
      } else if(e[0]==="proj"){
        work.push({kind:"build",tag:"proj",name:e[1],index:e[2]});
        work.push({kind:"visit",e:e[3]});
      } else {
        work.push({kind:"build",tag:e[0],n:e.length-1});
        for(let i=e.length-1;i>=1;i--) work.push({kind:"visit",e:e[i]});
      }
    }
    return vals.pop();
  };
}

const budget=1_000_000;
function evaluate(name,enabled){
  install(enabled);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;
  const t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0; totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null,
      fallback_attempt_reason:r.fallback_attempt_reason??null,
      fallback_attempt_steps:r.fallback_attempt_steps??null});
  }
  return {name,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,results};
}

const baseline=evaluate("baseline",false);
if(baseline.wrong) throw new Error("baseline wrong");
const residual=new Set(baseline.results.filter(r=>r.status==="UNKNOWN").map(r=>r.name));
const candidate=evaluate("iterative-instantiation",true);
proto.instantiateDeclaration=original;

let protectedChanged=0,resolved=0,resolvedAccept=0,resolvedReject=0;
const resolvedCases=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++){
  const b=baseline.results[i],r=candidate.results[i];
  if(b.status!=="UNKNOWN"&&r.status!==b.status){
    protectedChanged++;
    regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});
  }
  if(residual.has(r.name)){
    if(r.status!=="UNKNOWN"){
      if(r.status!==r.expected) throw new Error("WRONG_RESOLUTION "+JSON.stringify(r));
      resolved++; if(r.status==="ACCEPT") resolvedAccept++; else resolvedReject++;
      resolvedCases.push({name:r.name,status:r.status,steps:r.steps,constructed:r.constructed});
    } else remaining.push({name:r.name,reason:r.reason,steps:r.steps});
  }
}
const summary={arena_sha256:sha,budget,
  baseline:{counts:baseline.counts,wrong:baseline.wrong,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
  candidate:{counts:candidate.counts,wrong:candidate.wrong,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,elapsed_ms:candidate.elapsed_ms,
    protectedChanged,resolved,resolvedAccept,resolvedReject,resolvedCases,regressions,remaining},
  lawful:candidate.wrong===0&&protectedChanged===0,
  claim_boundary:"Prospective execution repair only. Replaces recursive declaration-term instantiation with an explicit work stack; universe substitution and constructed syntax are unchanged."};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/iterative-instantiation-separator.json",import.meta.url),JSON.stringify({summary,baseline,candidate},null,2));
console.log("ITERATIVE_INSTANTIATION "+JSON.stringify(summary));
