// Prospective separator: compile substitutions whose bound argument is
// provably unused. Exact de-Bruijn semantics are preserved: if var(depth)
// does not occur, the result is independent of the argument and consists only
// of dropping the removed binder from outer indices. The occurrence proof and
// resulting drop are cached by exact expression identity + exact depth.
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
if(rows.length!==188) throw new Error("Arena row count changed");

const proto=K.Kernel.prototype;
const retainedRun=proto.run,retainedSubstitute=proto.substitute;

function ensure(k){
  k.__unusedOccurrence ??= new WeakMap();
  k.__unusedDrop ??= new WeakMap();
  k.__unusedStats ??= {queries:0,provedUnused:0,occurrenceHits:0,dropHits:0,drops:0};
}
function depthMap(wm,e){
  let m=wm.get(e);
  if(!m){m=new Map();wm.set(e,m);}
  return m;
}
function occurs(k,root,depth){
  ensure(k); k.__unusedStats.queries++;
  const rootMap=depthMap(k.__unusedOccurrence,root);
  if(rootMap.has(depth)){k.__unusedStats.occurrenceHits++;return rootMap.get(depth);}

  // Postorder exact occurrence analysis. A binder increments the target index
  // only in its body, matching substitute's semantics exactly.
  const work=[{e:root,d:depth,post:false}],vals=[];
  while(work.length){
    const f=work.pop(),e=f.e,d=f.d,m=depthMap(k.__unusedOccurrence,e);
    if(m.has(d)){k.__unusedStats.occurrenceHits++;vals.push(m.get(d));continue;}
    k.tick();
    if(f.post){
      let n=f.n,yes=false;
      while(n-->0) yes=vals.pop()||yes;
      m.set(d,yes); vals.push(yes); continue;
    }
    switch(e[0]){
      case "sort": case "const": case "nat": case "strlit":
        m.set(d,false); vals.push(false); break;
      case "var":{
        const yes=e[1]===d; m.set(d,yes); vals.push(yes); break;
      }
      case "pi": case "lam":
        work.push({e,d,post:true,n:2});
        work.push({e:e[2],d:d+1,post:false});
        work.push({e:e[1],d,post:false});
        break;
      case "app":
        work.push({e,d,post:true,n:2});
        work.push({e:e[2],d,post:false});
        work.push({e:e[1],d,post:false});
        break;
      case "proj":
        work.push({e,d,post:true,n:1});
        work.push({e:e[3],d,post:false});
        break;
      case "let":
        work.push({e,d,post:true,n:3});
        work.push({e:e[3],d:d+1,post:false});
        work.push({e:e[2],d,post:false});
        work.push({e:e[1],d,post:false});
        break;
      default:
        // Unknown syntax must remain owned by the retained substitution.
        m.set(d,true); vals.push(true); break;
    }
  }
  return vals.pop();
}
function dropUnused(k,root,depth){
  ensure(k);
  const rootMap=depthMap(k.__unusedDrop,root);
  if(rootMap.has(depth)){k.__unusedStats.dropHits++;return rootMap.get(depth);}

  const work=[{e:root,d:depth,post:false}],vals=[];
  while(work.length){
    const f=work.pop(),e=f.e,d=f.d,m=depthMap(k.__unusedDrop,e);
    if(m.has(d)){k.__unusedStats.dropHits++;vals.push(m.get(d));continue;}
    if(f.post){
      const xs=new Array(f.n);
      for(let i=f.n-1;i>=0;i--) xs[i]=vals.pop();
      let out;
      if(f.tag==="proj") out=k.make("proj",f.name,f.index,xs[0]);
      else out=k.make(f.tag,...xs);
      m.set(d,out);vals.push(out);continue;
    }
    k.tick();
    let out;
    switch(e[0]){
      case "sort": case "const": case "nat": case "strlit":
        m.set(d,e);vals.push(e);break;
      case "var":
        out=e[1]>d?k.make("var",e[1]-1):e;
        m.set(d,out);vals.push(out);break;
      case "pi": case "lam":
        work.push({e,d,post:true,n:2,tag:e[0]});
        work.push({e:e[2],d:d+1,post:false});
        work.push({e:e[1],d,post:false});
        break;
      case "app":
        work.push({e,d,post:true,n:2,tag:"app"});
        work.push({e:e[2],d,post:false});
        work.push({e:e[1],d,post:false});
        break;
      case "proj":
        work.push({e,d,post:true,n:1,tag:"proj",name:e[1],index:e[2]});
        work.push({e:e[3],d,post:false});
        break;
      case "let":
        work.push({e,d,post:true,n:3,tag:"let"});
        work.push({e:e[3],d:d+1,post:false});
        work.push({e:e[2],d,post:false});
        work.push({e:e[1],d,post:false});
        break;
      default: k.unknown("unused-substitution-syntax");
    }
  }
  k.__unusedStats.drops++;
  return vals.pop();
}
function install(enabled){
  proto.run=retainedRun; proto.substitute=retainedSubstitute;
  if(!enabled) return;
  proto.run=function(...args){
    this.__unusedOccurrence=new WeakMap();
    this.__unusedDrop=new WeakMap();
    this.__unusedStats={queries:0,provedUnused:0,occurrenceHits:0,dropHits:0,drops:0};
    return retainedRun.apply(this,args);
  };
  proto.substitute=function(e,arg,depth=0){
    if(Array.isArray(e)&&occurs(this,e,depth)===false){
      this.__unusedStats.provedUnused++;
      return dropUnused(this,e,depth);
    }
    return retainedSubstitute.call(this,e,arg,depth);
  };
}
const budget=1_000_000;
function evaluate(mode,enabled){
  install(enabled);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;
  const aggregate={queries:0,provedUnused:0,occurrenceHits:0,dropHits:0,drops:0};
  const t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0;totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected)wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null});
    if(enabled){
      // checkExport may use multiple Kernel instances; stats here are best-effort
      // only and are not part of the correctness claim.
    }
  }
  return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,results,aggregate};
}
const candidate=evaluate("unused-argument-substitution",true);
const baseline=evaluate("baseline",false);
install(false);
if(baseline.wrong||candidate.wrong)throw new Error("wrong verdict");
const residual=new Set(baseline.results.filter(r=>r.status==="UNKNOWN").map(r=>r.name));
let protectedChanged=0,resolved=0;const resolvedCases=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++){
  const b=baseline.results[i],r=candidate.results[i];
  if(b.status!=="UNKNOWN"&&r.status!==b.status){
    protectedChanged++;regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});
  }
  if(residual.has(r.name)&&r.status!=="UNKNOWN"&&r.status===r.expected){
    resolved++;resolvedCases.push({name:r.name,status:r.status,reason:r.reason,steps:r.steps,constructed:r.constructed});
  }else if(residual.has(r.name))remaining.push({name:r.name,reason:r.reason,steps:r.steps,constructed:r.constructed});
}
const summary={arena_sha256:sha,budget,
  baseline:{counts:baseline.counts,wrong:baseline.wrong,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
  candidate:{counts:candidate.counts,wrong:candidate.wrong,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,elapsed_ms:candidate.elapsed_ms,
    protectedChanged,resolved,resolvedCases,regressions,remaining},
  lawful:candidate.wrong===0&&protectedChanged===0,
  promotable:candidate.wrong===0&&protectedChanged===0&&resolved>0,
  claim_boundary:"Exact substitution specialization only. When a complete de-Bruijn occurrence analysis proves var(depth) absent, substitution is independent of the argument; only the exact binder-drop transform remains, cached by expression identity + depth. Any term containing the target binder delegates unchanged to retained substitution."
};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/unused-argument-substitution.json",import.meta.url),JSON.stringify({summary,baseline,candidate},null,2));
console.log("UNUSED_ARGUMENT_SUBSTITUTION "+JSON.stringify(summary));
