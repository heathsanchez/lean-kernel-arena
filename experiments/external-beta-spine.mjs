// Prospective external application beta-spine compilation.
//
// Retained scoped-beta-spine batches a nested immediate-redex shape, but a
// standard left-associated application spine (((lam a) b) c) has an outer
// application whose immediate function is another application, so it does not
// enter that batch path.
//
// This separator flattens an external application spine, reduces only its head,
// and when the head exposes >=2 consecutive lambdas, erases those binders in one
// exact simultaneous de-Bruijn substitution over the shared DAG. External
// arguments all live in the same outer context, so var j under local depth d is:
//   j < d             : locally bound, unchanged
//   d <= j < d+m      : argument[m-1-(j-d)], shifted by d
//   j >= d+m          : var(j-m)
// No typing/equality/reduction law changes; it is a compiled implementation of
// repeated beta reduction.
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";
import {Stop} from "../genesis/kernel-base.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok)throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer()),sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash)throw new Error("Arena corpus changed");

const wanted=[
  "good/perf/fueled-chain.ndjson",
  "good/perf/magma-list-deep-n21.ndjson",
  "good/perf/magma-list-deep-n36.ndjson",
  "good/perf/magma-list-pair-n21.ndjson",
  "good/perf/magma-list-pair-n7.ndjson",
  "good/perf/shared-subterm.ndjson"
];
const py=[
  "import io,tarfile,json,sys",
  "wanted=set("+JSON.stringify(wanted)+")",
  "data=sys.stdin.buffer.read();rows=[]",
  "with tarfile.open(fileobj=io.BytesIO(data),mode='r:gz') as a:",
  "  for m in a:",
  "    p='/'.join(m.name.split('/')[-3:])",
  "    if m.isfile() and p in wanted:",
  "      rows.append({'name':p,'expected':'ACCEPT','input':a.extractfile(m).read().decode('utf-8')})",
  "print(json.dumps(rows))"
].join("\n");
const focusRows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));
if(focusRows.length!==6)throw new Error("focus rows missing");

const proto=K.Kernel.prototype,retainedRun=proto.run,retainedWhnf=proto.whnf;
const stats={queries:0,eligible:0,successes:0,binders:0,substNodes:0,substHits:0,fallbacks:0};

function flattenRaw(e){
  const args=[];let h=e;
  while(Array.isArray(h)&&h[0]==="app"){args.push(h[2]);h=h[1];}
  args.reverse();return{head:h,args};
}
function rebuild(k,h,args){
  let out=h;for(const a of args)out=k.make("app",out,a);return out;
}

function substMany(k,body,args){
  const m=args.length,memo=new WeakMap();
  function go(e,depth){
    if(!Array.isArray(e))return e;
    let byDepth=memo.get(e);
    if(!byDepth){byDepth=new Map();memo.set(e,byDepth);}
    if(byDepth.has(depth)){stats.substHits++;return byDepth.get(depth);}
    stats.substNodes++;
    let out=e;
    switch(e[0]){
      case "sort":case "const":case "nat":case "strlit":
        out=e;break;
      case "var":{
        const i=e[1];
        if(i<depth)out=e;
        else {
          const j=i-depth;
          if(j<m) out=k.shift(args[m-1-j],depth);
          else out=k.make("var",i-m);
        }
        break;
      }
      case "pi":case "lam":{
        const a=go(e[1],depth),b=go(e[2],depth+1);
        out=(a===e[1]&&b===e[2])?e:k.make(e[0],a,b);
        break;
      }
      case "app":{
        const f=go(e[1],depth),a=go(e[2],depth);
        out=(f===e[1]&&a===e[2])?e:k.make("app",f,a);
        break;
      }
      case "proj":{
        const x=go(e[3],depth);
        out=x===e[3]?e:k.make("proj",e[1],e[2],x);
        break;
      }
      case "let":{
        const a=go(e[1],depth),v=go(e[2],depth),b=go(e[3],depth+1);
        out=(a===e[1]&&v===e[2]&&b===e[3])?e:k.make("let",a,v,b);
        break;
      }
      default: throw new Error("external-beta-syntax:"+e[0]);
    }
    byDepth.set(depth,out);return out;
  }
  return go(body,0);
}

function install(enabled){
  proto.run=retainedRun;proto.whnf=retainedWhnf;
  if(!enabled)return;
  proto.run=function(...args){this.__externalBetaDepth=0;return retainedRun.apply(this,args);};
  proto.whnf=function(e){
    if(this.__externalBetaDepth || this.localDefs===true || !Array.isArray(e)||e[0]!=="app")
      return retainedWhnf.call(this,e);
    stats.queries++;
    const sp=flattenRaw(e);
    if(sp.args.length<2)return retainedWhnf.call(this,e);

    const snap={steps:this.steps,budget:this.budget,frontier:this.conversionFrontier,allocations:this.allocations};
    this.__externalBetaDepth=1;
    try{
      const h=retainedWhnf.call(this,sp.head);
      let cur=h,m=0;
      while(m<sp.args.length && Array.isArray(cur)&&cur[0]==="lam"){
        m++;cur=cur[2];
      }
      if(m<2){
        this.__externalBetaDepth=0;
        this.steps=snap.steps;this.budget=snap.budget;this.conversionFrontier=snap.frontier;this.allocations=snap.allocations;
        stats.fallbacks++;
        return retainedWhnf.call(this,e);
      }
      stats.eligible++;stats.binders+=m;
      for(let i=0;i<m;i++){this.tick();this.need("application");this.need("reduction");}
      const out=substMany(this,cur,sp.args.slice(0,m));
      const next=sp.args.length===m?out:rebuild(this,out,sp.args.slice(m));
      const result=retainedWhnf.call(this,next);
      stats.successes++;
      this.__externalBetaDepth=0;
      return result;
    }catch(err){
      this.__externalBetaDepth=0;
      if(err instanceof Stop||err instanceof RangeError){
        this.steps=snap.steps;this.budget=snap.budget;this.conversionFrontier=snap.frontier;this.allocations=snap.allocations;
        stats.fallbacks++;
        return retainedWhnf.call(this,e);
      }
      throw err;
    }
  };
}

function evaluate(enabled,subset,budget){
  install(enabled);
  const before={...stats},results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;const t0=Date.now();
  for(const row of subset){
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0;totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected)wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null,
      frontier_declaration:r.frontier_declaration??null,
      fallback_mode:r.fallback_mode??null,fallback_attempt_reason:r.fallback_attempt_reason??null});
  }
  const d={};for(const k of Object.keys(before))d[k]=stats[k]-before[k];
  return {enabled,budget,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,stats:d,results};
}

const baseline=evaluate(false,focusRows,1_000_000);
const candidate=evaluate(true,focusRows,1_000_000);
if(baseline.wrong||candidate.wrong)throw new Error("focus wrong verdict");

let cliff=null;
if(!candidate.results.some(r=>r.status==="ACCEPT")){
  cliff=evaluate(true,focusRows,2_000_000);
  if(cliff.wrong)throw new Error("cliff wrong verdict");
}

let full=null;
if(candidate.results.some(r=>r.status==="ACCEPT")||cliff?.results.some(r=>r.status==="ACCEPT")){
  const pyAll=[
    "import io,tarfile,json,sys",
    "data=sys.stdin.buffer.read();rows=[]",
    "with tarfile.open(fileobj=io.BytesIO(data),mode='r:gz') as a:",
    "  for m in a:",
    "    p=m.name.split('/')",
    "    if not m.isfile() or not m.name.endswith('.ndjson') or m.size>2000000: continue",
    "    e='ACCEPT' if 'good' in p else 'REJECT' if 'bad' in p else None",
    "    if e: rows.append({'name':m.name,'expected':e,'input':a.extractfile(m).read().decode('utf-8')})",
    "print(json.dumps(rows))"
  ].join("\n");
  const allRows=JSON.parse(execFileSync("python3",["-c",pyAll],{input:data,maxBuffer:50000000,timeout:10000}));
  const cand=evaluate(true,allRows,1_000_000),base=evaluate(false,allRows,1_000_000);
  if(cand.wrong||base.wrong)throw new Error("full wrong verdict");
  let protectedChanged=0;const resolved=[],regressions=[],remaining=[];
  for(let i=0;i<allRows.length;i++){
    const b=base.results[i],c=cand.results[i];
    if(b.status!=="UNKNOWN"&&c.status!==b.status){
      protectedChanged++;regressions.push({name:c.name,before:b.status,after:c.status,reason:c.reason});
    }
    if(b.status==="UNKNOWN"){
      if(c.status!=="UNKNOWN"&&c.status===c.expected)
        resolved.push({name:c.name,status:c.status,steps:c.steps,constructed:c.constructed});
      else remaining.push({name:c.name,status:c.status,reason:c.reason,steps:c.steps,frontier_declaration:c.frontier_declaration});
    }
  }
  full={
    baseline:{counts:base.counts,totalSteps:base.totalSteps,totalConstructed:base.totalConstructed,elapsed_ms:base.elapsed_ms},
    candidate:{counts:cand.counts,totalSteps:cand.totalSteps,totalConstructed:cand.totalConstructed,
      elapsed_ms:cand.elapsed_ms,stats:cand.stats,protectedChanged,resolved,regressions,remaining},
    lawful:cand.wrong===0&&protectedChanged===0,
    promotable:cand.wrong===0&&protectedChanged===0&&resolved.length>0
  };
}
install(false);

const report={
  arena_sha256:sha,baseline,candidate,cliff,full,
  claim_boundary:"Execution-only compilation of repeated beta reduction on ordinary-kernel external application spines. Multiple consecutive exposed lambda binders are eliminated by one exact simultaneous de-Bruijn substitution over immutable DAG syntax. LocalDef execution is excluded in this separator. No typing, equality or reduction law is added."
};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/external-beta-spine.json",import.meta.url),JSON.stringify(report,null,2)+"\n");
console.log("EXTERNAL_BETA_SPINE "+JSON.stringify(report));
