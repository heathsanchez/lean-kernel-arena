// Prospective separator: compile exact binder-span metadata once, outside the
// semantic tick budget, then use it only to skip de-Bruijn transforms proven
// extensionally identical. Iterative analysis avoids adding host recursion.
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "./kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("./evidence/retained.json",import.meta.url),"utf8"));
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
const originalRun=proto.run, originalShift=proto.shift, originalSubstitute=proto.substitute;

function span(kernel,root) {
  if(!Array.isArray(root)) return Infinity;
  kernel.__binderSpan??=new WeakMap();
  const memo=kernel.__binderSpan;
  if(memo.has(root)) return memo.get(root);

  // Postorder over expression DAG. span(x) = maximum free de-Bruijn index
  // relative to x's root; binder bodies subtract one.
  const stack=[[root,false]];
  while(stack.length) {
    const [x,done]=stack.pop();
    if(!Array.isArray(x)||memo.has(x)) continue;
    if(!done) {
      stack.push([x,true]);
      switch(x[0]) {
        case "pi": case "lam":
          if(Array.isArray(x[2])&&!memo.has(x[2])) stack.push([x[2],false]);
          if(Array.isArray(x[1])&&!memo.has(x[1])) stack.push([x[1],false]);
          break;
        case "app":
          if(Array.isArray(x[2])&&!memo.has(x[2])) stack.push([x[2],false]);
          if(Array.isArray(x[1])&&!memo.has(x[1])) stack.push([x[1],false]);
          break;
        case "proj":
          if(Array.isArray(x[3])&&!memo.has(x[3])) stack.push([x[3],false]);
          break;
        case "let":
          if(Array.isArray(x[3])&&!memo.has(x[3])) stack.push([x[3],false]);
          if(Array.isArray(x[2])&&!memo.has(x[2])) stack.push([x[2],false]);
          if(Array.isArray(x[1])&&!memo.has(x[1])) stack.push([x[1],false]);
          break;
      }
      continue;
    }
    const m=y=>Array.isArray(y)?(memo.get(y)??Infinity):-Infinity;
    let v;
    switch(x[0]) {
      case "sort": case "const": case "nat": case "strlit": v=-Infinity; break;
      case "var": v=x[1]; break;
      case "pi": case "lam": v=Math.max(m(x[1]),m(x[2])-1); break;
      case "app": v=Math.max(m(x[1]),m(x[2])); break;
      case "proj": v=m(x[3]); break;
      case "let": v=Math.max(m(x[1]),m(x[2]),m(x[3])-1); break;
      default: v=Infinity;
    }
    memo.set(x,v);
  }
  return memo.get(root)??Infinity;
}

function install(mode) {
  proto.run=originalRun; proto.shift=originalShift; proto.substitute=originalSubstitute;
  proto.run=function(...args){ this.__binderSpan=new WeakMap(); return originalRun.apply(this,args); };
  if(mode==="shift"||mode==="both") {
    proto.shift=function(e,amount,cut=0) {
      if(Array.isArray(e)&&span(this,e)<cut) return e;
      return originalShift.call(this,e,amount,cut);
    };
  }
  if(mode==="substitute"||mode==="both") {
    proto.substitute=function(e,arg,depth=0) {
      if(Array.isArray(e)&&span(this,e)<depth) return e;
      return originalSubstitute.call(this,e,arg,depth);
    };
  }
}

const budget=1_000_000;
function evaluate(mode) {
  install(mode);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0}; let wrong=0,totalSteps=0;
  const t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1; totalSteps+=r.steps??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null});
  }
  return {mode:mode||"none",counts,wrong,totalSteps,elapsed_ms:Date.now()-t0,results};
}
const variants=[evaluate(""),evaluate("shift"),evaluate("substitute"),evaluate("both")];
proto.run=originalRun; proto.shift=originalShift; proto.substitute=originalSubstitute;
const baseline=variants[0]; if(baseline.wrong) throw new Error("baseline wrong");
const residual=new Set(baseline.results.filter(r=>r.status==="UNKNOWN").map(r=>r.name));
const summaries=[];
for(const v of variants){
  let protectedChanged=0,resolved=0,resolvedAccept=0,resolvedReject=0;
  const resolvedCases=[],regressions=[],remaining=[];
  for(let i=0;i<rows.length;i++){
    const b=baseline.results[i],r=v.results[i];
    if(b.status!=="UNKNOWN"&&r.status!==b.status){
      protectedChanged++; regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});
    }
    if(residual.has(r.name)){
      if(r.status!=="UNKNOWN"){
        if(r.status!==r.expected) throw new Error("WRONG_RESOLUTION "+JSON.stringify({mode:v.mode,result:r}));
        resolved++; if(r.status==="ACCEPT") resolvedAccept++; else resolvedReject++;
        resolvedCases.push({name:r.name,status:r.status,steps:r.steps,constructed:r.constructed});
      } else remaining.push({name:r.name,reason:r.reason});
    }
  }
  const s={mode:v.mode,counts:v.counts,wrong:v.wrong,protectedChanged,resolved,resolvedAccept,resolvedReject,
    totalSteps:v.totalSteps,elapsed_ms:v.elapsed_ms,resolvedCases,remaining,regressions};
  summaries.push(s); console.log("COMPILED_BINDER_SPAN_VARIANT "+JSON.stringify(s));
}
const lawful=summaries.filter(s=>s.mode!=="none"&&s.wrong===0&&s.protectedChanged===0&&s.resolved>0)
  .sort((a,b)=>b.resolved-a.resolved||a.totalSteps-b.totalSteps);
const conclusion={arena_sha256:sha,budget,baseline:summaries[0],candidates:summaries.slice(1),
  lawful_candidates:lawful.map(x=>x.mode),provisional_winner:lawful[0]?.mode??null,
  claim_boundary:"Exact compiled structural metadata. A transform is skipped only when max free relative index proves it is identity; metadata computation is iterative and outside semantic ticks."};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/compiled-binder-span-separator.json",import.meta.url),JSON.stringify({conclusion,variants},null,2));
console.log("COMPILED_BINDER_SPAN_CONCLUSION "+JSON.stringify(conclusion));
