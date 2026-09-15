// Prospective separator: compile exact successful shift/substitution
// consequences so an identical cache hit does not repay semantic work.
//
// Keys are unchanged from the retained structural cache: exact expression
// identity, exact argument identity, and every numeric parameter. Only
// successful completed results exist in the cache. No failure, conversion,
// typing, or semantic verdict is cached.
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
const retainedShift=proto.shift, retainedSubstitute=proto.substitute;

function shiftMap(kernel,e) {
  kernel._shiftCache ??= new WeakMap();
  let m=kernel._shiftCache.get(e);
  if(!m) { m=new Map(); kernel._shiftCache.set(e,m); }
  return m;
}
function substMap(kernel,e,arg) {
  kernel._substCache ??= new WeakMap();
  let byExpr=kernel._substCache.get(e);
  if(!byExpr) { byExpr=new WeakMap(); kernel._substCache.set(e,byExpr); }
  let byDepth=byExpr.get(arg);
  if(!byDepth) { byDepth=new Map(); byExpr.set(arg,byDepth); }
  return byDepth;
}

function install(enabled) {
  proto.shift=retainedShift;
  proto.substitute=retainedSubstitute;
  if(!enabled) return;

  proto.shift=function(root,amount,cut=0) {
    const work=[{kind:"visit",e:root,cut}],vals=[];
    while(work.length) {
      const f=work.pop();
      if(f.kind==="build") {
        let out;
        if(f.tag==="proj") out=this.make("proj",f.name,f.index,vals.pop());
        else {
          const xs=new Array(f.n);
          for(let i=f.n-1;i>=0;i--) xs[i]=vals.pop();
          out=this.make(f.tag,...xs);
        }
        shiftMap(this,f.e).set(f.key,out);
        vals.push(out);
        continue;
      }
      const e=f.e,c=f.cut,key=`${amount}:${c}`,cache=shiftMap(this,e);
      if(cache.has(key)) {
        vals.push(cache.get(key)); // compiled exact consequence: no repayment
        continue;
      }

      this.tick();
      let out;
      switch(e[0]) {
        case "sort": case "const": case "nat": case "strlit":
          out=e; cache.set(key,out); vals.push(out); break;
        case "var":
          out=e[1]<c?e:this.make("var",e[1]+amount);
          cache.set(key,out); vals.push(out); break;
        case "pi": case "lam":
          work.push({kind:"build",tag:e[0],n:2,e,key});
          work.push({kind:"visit",e:e[2],cut:c+1});
          work.push({kind:"visit",e:e[1],cut:c});
          break;
        case "app":
          work.push({kind:"build",tag:"app",n:2,e,key});
          work.push({kind:"visit",e:e[2],cut:c});
          work.push({kind:"visit",e:e[1],cut:c});
          break;
        case "proj":
          work.push({kind:"build",tag:"proj",name:e[1],index:e[2],e,key});
          work.push({kind:"visit",e:e[3],cut:c});
          break;
        case "let":
          work.push({kind:"build",tag:"let",n:3,e,key});
          work.push({kind:"visit",e:e[3],cut:c+1});
          work.push({kind:"visit",e:e[2],cut:c});
          work.push({kind:"visit",e:e[1],cut:c});
          break;
        default: this.unknown("shift-syntax");
      }
    }
    return vals.pop();
  };

  proto.substitute=function(root,arg,depth=0) {
    const work=[{kind:"visit",e:root,depth}],vals=[];
    while(work.length) {
      const f=work.pop();
      if(f.kind==="build") {
        let out;
        if(f.tag==="proj") out=this.make("proj",f.name,f.index,vals.pop());
        else {
          const xs=new Array(f.n);
          for(let i=f.n-1;i>=0;i--) xs[i]=vals.pop();
          out=this.make(f.tag,...xs);
        }
        substMap(this,f.e,arg).set(f.depth,out);
        vals.push(out);
        continue;
      }
      const e=f.e,d=f.depth,cache=substMap(this,e,arg);
      if(cache.has(d)) {
        vals.push(cache.get(d)); // compiled exact consequence: no repayment
        continue;
      }

      this.tick();
      let out;
      switch(e[0]) {
        case "sort": case "const": case "nat": case "strlit":
          out=e; cache.set(d,out); vals.push(out); break;
        case "var":
          out=e[1]===d?this.shift(arg,d):e[1]>d?this.make("var",e[1]-1):e;
          cache.set(d,out); vals.push(out); break;
        case "pi": case "lam":
          work.push({kind:"build",tag:e[0],n:2,e,depth:d});
          work.push({kind:"visit",e:e[2],depth:d+1});
          work.push({kind:"visit",e:e[1],depth:d});
          break;
        case "app":
          work.push({kind:"build",tag:"app",n:2,e,depth:d});
          work.push({kind:"visit",e:e[2],depth:d});
          work.push({kind:"visit",e:e[1],depth:d});
          break;
        case "proj":
          work.push({kind:"build",tag:"proj",name:e[1],index:e[2],e,depth:d});
          work.push({kind:"visit",e:e[3],depth:d});
          break;
        case "let":
          work.push({kind:"build",tag:"let",n:3,e,depth:d});
          work.push({kind:"visit",e:e[3],depth:d+1});
          work.push({kind:"visit",e:e[2],depth:d});
          work.push({kind:"visit",e:e[1],depth:d});
          break;
        default: this.unknown("substitution-syntax");
      }
    }
    return vals.pop();
  };
}

const budget=1_000_000;
function evaluate(mode,enabled) {
  install(enabled);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;
  const t0=Date.now();
  for(const row of rows) {
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0; totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null});
  }
  return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,results};
}

const baseline=evaluate("baseline",false);
const candidate=evaluate("free-exact-structural-cache-hits",true);
install(false);
if(baseline.wrong) throw new Error("baseline wrong");

const residual=new Set(baseline.results.filter(r=>r.status==="UNKNOWN").map(r=>r.name));
let protectedChanged=0,resolved=0;
const resolvedCases=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++) {
  const b=baseline.results[i],r=candidate.results[i];
  if(b.status!=="UNKNOWN"&&r.status!==b.status) {
    protectedChanged++;
    regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});
  }
  if(residual.has(r.name)&&r.status!=="UNKNOWN"&&r.status===r.expected) {
    resolved++;
    resolvedCases.push({name:r.name,status:r.status,reason:r.reason,steps:r.steps,constructed:r.constructed});
  } else if(residual.has(r.name)) {
    remaining.push({name:r.name,reason:r.reason,steps:r.steps,constructed:r.constructed});
  }
}
const summary={arena_sha256:sha,budget,
  baseline:{counts:baseline.counts,wrong:baseline.wrong,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
  candidate:{counts:candidate.counts,wrong:candidate.wrong,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,elapsed_ms:candidate.elapsed_ms,
    protectedChanged,resolved,resolvedCases,regressions,remaining},
  lawful:candidate.wrong===0&&protectedChanged===0,
  promotable:candidate.wrong===0&&protectedChanged===0&&resolved>0,
  claim_boundary:"Exact successful de-Bruijn transform consequence reuse only. Cache keys remain expression identity + argument identity + every numeric parameter; failures are never cached. Cache hits do not repay already verified structural work."
};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/free-structural-cache-hits.json",import.meta.url),JSON.stringify({summary,baseline,candidate},null,2));
console.log("FREE_STRUCTURAL_CACHE_HITS "+JSON.stringify(summary));
