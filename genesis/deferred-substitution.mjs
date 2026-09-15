// Prospective separator: remove materialized beta/let substitution from WHNF.
// Uses persistent lexical environments (O(1) extension) and reifies ordinary
// syntax only when the retained kernel requires it. No semantic rule changes.
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
const originalWhnf=proto.whnf;
const EMPTY={size:0,head:null,tail:null};
const extend=(head,tail)=>({head,tail,size:tail.size+1});

function lookup(kernel,env,i) {
  let p=env;
  while(i-->0) { kernel.tick(); p=p.tail; }
  return p.head;
}

function reify(kernel,closure,lift=0) {
  function go(term,env,depth,extra) {
    kernel.tick();
    switch(term[0]) {
      case "sort": case "const": case "nat": case "strlit": return term;
      case "var": {
        const i=term[1];
        if(i<depth) return term;
        const j=i-depth;
        if(j<env.size) return goClosure(lookup(kernel,env,j),extra+depth);
        const out=depth+(j-env.size)+extra;
        return out===i ? term : kernel.make("var",out);
      }
      case "pi": case "lam":
        return kernel.make(term[0],go(term[1],env,depth,extra),go(term[2],env,depth+1,extra));
      case "app":
        return kernel.make("app",go(term[1],env,depth,extra),go(term[2],env,depth,extra));
      case "proj":
        return kernel.make("proj",term[1],term[2],go(term[3],env,depth,extra));
      case "let":
        return kernel.make("let",go(term[1],env,depth,extra),go(term[2],env,depth,extra),go(term[3],env,depth+1,extra));
      default:
        kernel.unknown("deferred-reify-syntax");
    }
  }
  function goClosure(c,extra) { return go(c.term,c.env,0,extra); }
  return goClosure(closure,lift);
}

function installDeferred(enabled) {
  proto.whnf=originalWhnf;
  if(!enabled) return;
  proto.whnf=function(e) {
    let cur={term:e,env:EMPTY};
    const args=[];
    for(;;) {
      this.tick();
      const t=cur.term,env=cur.env;
      if(t[0]==="var") {
        if(t[1]<env.size) { cur=lookup(this,env,t[1]); continue; }
        const n=t[1]-env.size;
        cur={term:n===t[1]?t:this.make("var",n),env:EMPTY};
      } else if(t[0]==="let") {
        this.need("reduction");
        cur={term:t[3],env:extend({term:t[2],env},env)};
        continue;
      } else if(t[0]==="app") {
        this.need("application");
        args.push({term:t[2],env});
        cur={term:t[1],env};
        continue;
      } else if(t[0]==="lam" && args.length) {
        this.need("reduction");
        const arg=args.pop();
        cur={term:t[2],env:extend(arg,env)};
        continue;
      } else if(t[0]==="const") {
        this.need("declarations");
        const d=this.env.get(t[1]);
        if(!d) this.reject("undeclared-constant");
        if(d.kind==="def") {
          this.need("reduction");
          cur={term:this.instantiateDeclaration(t,d.value),env:EMPTY};
          continue;
        }
      }

      // Stable WHNF with no pending application can be returned directly.
      if(!args.length) {
        if(cur.env.size===0 && ["sort","var","pi","lam","const","strlit"].includes(cur.term[0]))
          return cur.term;
        if(cur.term[0]==="nat"||cur.term[0]==="proj")
          return originalWhnf.call(this,reify(this,cur));
        return cur.env.size===0 ? cur.term : reify(this,cur);
      }

      // Recursors, quotients and other retained head reductions still use the
      // certified evaluator. Reconstruct only this exposed spine.
      let out=cur.env.size===0?cur.term:reify(this,cur);
      for(let i=args.length-1;i>=0;i--) out=this.make("app",out,reify(this,args[i]));
      return originalWhnf.call(this,out);
    }
  };
}

const budget=1_000_000;
function evaluate(name,enabled) {
  installDeferred(enabled);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;
  const t0=Date.now();
  for(const row of rows) {
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0; totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null,elapsed_ms:r.elapsed_ms??null});
  }
  return {name,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,results};
}

const baseline=evaluate("baseline",false);
if(baseline.wrong) throw new Error("baseline wrong");
const residual=new Set(baseline.results.filter(r=>r.status==="UNKNOWN"&&
  ["budget-exhausted","host-stack-limit"].includes(r.reason)).map(r=>r.name));
if(residual.size!==17) throw new Error("qualified large-stack residual changed: "+residual.size);

const candidate=evaluate("persistent-env-whnf",true);
proto.whnf=originalWhnf;

let protectedChanged=0,resolved=0,resolvedAccept=0,resolvedReject=0;
const resolvedCases=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++) {
  const b=baseline.results[i],r=candidate.results[i];
  if(b.status!=="UNKNOWN"&&r.status!==b.status) {
    protectedChanged++;
    if(regressions.length<20) regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});
  }
  if(residual.has(r.name)) {
    if(r.status!=="UNKNOWN") {
      if(r.status!==r.expected) throw new Error("WRONG_RESOLUTION "+JSON.stringify(r));
      resolved++;
      if(r.status==="ACCEPT") resolvedAccept++; else resolvedReject++;
      resolvedCases.push({name:r.name,status:r.status,steps:r.steps,constructed:r.constructed});
    } else remaining.push({name:r.name,reason:r.reason,steps:r.steps,constructed:r.constructed});
  }
}
const summary={
  arena_sha256:sha,budget,
  baseline:{counts:baseline.counts,wrong:baseline.wrong,totalSteps:baseline.totalSteps,
    totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
  candidate:{counts:candidate.counts,wrong:candidate.wrong,totalSteps:candidate.totalSteps,
    totalConstructed:candidate.totalConstructed,elapsed_ms:candidate.elapsed_ms,
    protectedChanged,resolved,resolvedAccept,resolvedReject,resolvedCases,regressions,remaining},
  lawful:candidate.wrong===0&&protectedChanged===0,
  promotable:candidate.wrong===0&&protectedChanged===0&&resolved>0,
  claim_boundary:"Prospective evaluator representation separator. Persistent environments defer beta/let substitution only in WHNF; retained semantic rules remain authoritative. Promotion requires integration, ablation, default-stack replay, and full Arena replay."
};
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("./evidence/deferred-substitution.json",import.meta.url),JSON.stringify({summary,baseline,candidate},null,2));
console.log("DEFERRED_SUBSTITUTION "+JSON.stringify(summary));
