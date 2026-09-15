// Prospective separator: transparent lazy de-Bruijn closures.
// shift/substitute become exact pending operations on Array proxies. A subtree is
// transformed only when the kernel observes that subtree. This tests whether the
// remaining resource frontier is caused by eager tree rewriting rather than by
// the semantic rules themselves.
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
const META=Symbol("mda-lazy-term");

function isLazy(x) {
  return Array.isArray(x) && x[META]!==undefined;
}
function adjusted(op,underBinder) {
  if(!underBinder) return op;
  if(op.kind==="shift") return {kind:"shift",amount:op.amount,cut:op.cut+1};
  return {kind:"subst",arg:op.arg,depth:op.depth+1};
}
function objectId(kernel,x) {
  kernel.__lazyObjectIds ??= new WeakMap();
  kernel.__lazyNextObjectId ??= 1;
  let id=kernel.__lazyObjectIds.get(x);
  if(id!==undefined) return id;
  id=kernel.__lazyNextObjectId++;
  kernel.__lazyObjectIds.set(x,id);
  return id;
}
function opsKey(kernel,ops) {
  return ops.map(op=>op.kind==="shift"
    ? "s:"+op.amount+":"+op.cut
    : "u:"+objectId(kernel,op.arg)+":"+op.depth).join("|");
}
function closure(kernel,base,ops) {
  if(!Array.isArray(base) || ops.length===0) return base;
  if(isLazy(base)) {
    const m=base[META];
    base=m.base;
    ops=m.ops.concat(ops);
  }

  kernel.__lazyClosureCache ??= new WeakMap();
  let byOps=kernel.__lazyClosureCache.get(base);
  if(!byOps) { byOps=new Map(); kernel.__lazyClosureCache.set(base,byOps); }
  const key=opsKey(kernel,ops);
  const prior=byOps.get(key);
  if(prior!==undefined) return prior;

  const meta={kernel,base,ops,view:null,proxy:null};
  const target=[];
  const proxy=new Proxy(target,{
    get(_t,p) {
      if(p===META) return meta;
      const v=force(meta);
      if(p==="length") return v.length;
      const out=v[p];
      return typeof out==="function" ? out.bind(v) : out;
    }
  });
  meta.proxy=proxy;
  byOps.set(key,proxy);
  return proxy;
}
function force(meta) {
  if(meta.view!==null) return meta.view;
  const k=meta.kernel, base=meta.base, ops=meta.ops;

  if(!Array.isArray(base)) { meta.view=base; return base; }

  if(base[0]==="var") {
    let i=base[1];
    for(let oi=0;oi<ops.length;oi++) {
      const op=ops[oi]; k.tick();
      if(op.kind==="shift") {
        if(i>=op.cut) i+=op.amount;
        continue;
      }
      if(i===op.depth) {
        const tail=[];
        if(op.depth!==0) tail.push({kind:"shift",amount:op.depth,cut:0});
        for(let j=oi+1;j<ops.length;j++) tail.push(ops[j]);
        const next=closure(k,op.arg,tail);
        meta.view=isLazy(next)?force(next[META]):next;
        return meta.view;
      }
      if(i>op.depth) i--;
    }
    meta.view=i===base[1]?base:k.make("var",i);
    return meta.view;
  }

  for(let i=0;i<ops.length;i++) k.tick();

  switch(base[0]) {
    case "sort": case "const": case "nat": case "strlit":
      meta.view=base; return base;
    case "pi": case "lam": {
      const domain=closure(k,base[1],ops);
      const body=closure(k,base[2],ops.map(op=>adjusted(op,true)));
      meta.view=k.make(base[0],domain,body); return meta.view;
    }
    case "app":
      meta.view=k.make("app",closure(k,base[1],ops),closure(k,base[2],ops));
      return meta.view;
    case "proj":
      meta.view=k.make("proj",base[1],base[2],closure(k,base[3],ops));
      return meta.view;
    case "let":
      meta.view=k.make("let",
        closure(k,base[1],ops),
        closure(k,base[2],ops),
        closure(k,base[3],ops.map(op=>adjusted(op,true))));
      return meta.view;
    default:
      k.unknown("substitution-syntax");
  }
}

function install(enabled) {
  proto.run=originalRun; proto.shift=originalShift; proto.substitute=originalSubstitute;
  if(!enabled) return;

  proto.run=function(...args) {
    this.__lazyShiftCache=new WeakMap();
    this.__lazySubstCache=new WeakMap();
    this.__lazyClosureCache=new WeakMap();
    this.__lazyObjectIds=new WeakMap();
    this.__lazyNextObjectId=1;
    return originalRun.apply(this,args);
  };

  proto.shift=function(e,amount,cut=0) {
    if(!Array.isArray(e)) return originalShift.call(this,e,amount,cut);
    this.__lazyShiftCache ??= new WeakMap();
    let byKey=this.__lazyShiftCache.get(e);
    if(!byKey) { byKey=new Map(); this.__lazyShiftCache.set(e,byKey); }
    const key=amount+":"+cut;
    if(byKey.has(key)) return byKey.get(key);
    const out=closure(this,e,[{kind:"shift",amount,cut}]);
    byKey.set(key,out);
    return out;
  };

  proto.substitute=function(e,arg,depth=0) {
    if(!Array.isArray(e)||!Array.isArray(arg)) return originalSubstitute.call(this,e,arg,depth);
    this.__lazySubstCache ??= new WeakMap();
    let byExpr=this.__lazySubstCache.get(e);
    if(!byExpr) { byExpr=new WeakMap(); this.__lazySubstCache.set(e,byExpr); }
    let byDepth=byExpr.get(arg);
    if(!byDepth) { byDepth=new Map(); byExpr.set(arg,byDepth); }
    if(byDepth.has(depth)) return byDepth.get(depth);
    const out=closure(this,e,[{kind:"subst",arg,depth}]);
    byDepth.set(depth,out);
    return out;
  };
}

const budget=1_000_000;
function evaluate(name,enabled) {
  install(enabled);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;
  const start=Date.now();
  for(const row of rows) {
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0; totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:r.elapsed_ms??null,
      fallback_mode:r.fallback_mode??null});
  }
  return {name,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-start,results};
}

const baseline=evaluate("baseline",false);
if(baseline.wrong) throw new Error("baseline wrong");
const residualNames=new Set(baseline.results.filter(r=>r.status==="UNKNOWN").map(r=>r.name));
if(residualNames.size===0) throw new Error("expected nonempty residual frontier");
const candidate=evaluate("lazy-closures",true);
proto.run=originalRun; proto.shift=originalShift; proto.substitute=originalSubstitute;

let protectedChanged=0,resolved=0,resolvedAccept=0,resolvedReject=0;
const resolvedCases=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++) {
  const b=baseline.results[i],r=candidate.results[i];
  if(b.status!=="UNKNOWN"&&r.status!==b.status) {
    protectedChanged++; regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});
  }
  if(residualNames.has(r.name)&&r.status!=="UNKNOWN") {
    if(r.status!==r.expected) throw new Error("WRONG_RESOLUTION "+JSON.stringify(r));
    resolved++; if(r.status==="ACCEPT") resolvedAccept++; else resolvedReject++;
    resolvedCases.push({name:r.name,status:r.status,steps:r.steps,constructed:r.constructed,fallback_mode:r.fallback_mode});
  } else if(residualNames.has(r.name)) {
    remaining.push({name:r.name,reason:r.reason,steps:r.steps,constructed:r.constructed});
  }
}
const summary={arena_sha256:sha,budget,
  baseline:{counts:baseline.counts,wrong:baseline.wrong,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
  candidate:{counts:candidate.counts,wrong:candidate.wrong,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,elapsed_ms:candidate.elapsed_ms,
    protectedChanged,resolved,resolvedAccept,resolvedReject,resolvedCases,regressions,remaining},
  lawful:candidate.wrong===0&&protectedChanged===0,
  promotable:candidate.wrong===0&&protectedChanged===0&&resolved>0,
  claim_boundary:"Prospective representation/execution repair. Pending shift/substitute operations are exact and are forced only through ordinary Array observations. No typing, conversion, or reduction law is added."
};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/lazy-closure-separator.json",import.meta.url),JSON.stringify({summary,baseline,candidate},null,2));
console.log("LAZY_CLOSURE_SEPARATOR "+JSON.stringify(summary));
