import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok) throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer()),sha=createHash("sha256").update(data).digest("hex");
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

const proto=K.Kernel.prototype, retainedWhnf=proto.whnf;

function rawRigidSpecial(root,kernel){
  let h=root;
  while(Array.isArray(h)&&h[0]==="app") h=h[1];
  if(h?.[0]!=="const") return false;
  const d=kernel.env?.get(h[1]);
  return d?.kind==="rec"||d?.kind==="quot";
}

function iterativeOrdinaryWhnf(root){
  if(this.localDefs||this._fullStackSafe===true||!Array.isArray(root))
    return retainedWhnf.call(this,root);
  if(root[0]==="app"&&rawRigidSpecial(root,this))
    return retainedWhnf.call(this,root);

  const original=root;
  let cur=root, args=[], dirty=false;

  const absorbApps=()=>{
    while(Array.isArray(cur)&&cur[0]==="app"){
      this.tick(); this.need("application");
      args.push(cur[2]);
      cur=cur[1];
    }
  };
  const rebuild=()=>{
    if(!dirty&&original[0]==="app") return original;
    let out=cur;
    for(let i=args.length-1;i>=0;i--) out=this.make("app",out,args[i]);
    return out;
  };

  absorbApps();
  while(true){
    if(!Array.isArray(cur)) return cur;

    if(cur[0]==="let"){
      this.tick(); this.need("reduction");
      cur=this.substitute(cur[3],cur[2]);
      dirty=true; absorbApps(); continue;
    }

    if(cur[0]==="const"){
      this.tick(); this.need("declarations");
      const d=this.env.get(cur[1]);
      if(!d) this.reject("undeclared-constant");
      if(d.kind==="def"){
        this.need("reduction");
        cur=this.instantiateDeclaration(cur,d.value);
        dirty=true; absorbApps(); continue;
      }
      if(args.length&&(d.kind==="rec"||d.kind==="quot")){
        const out=rebuild();
        return retainedWhnf.call(this,out);
      }
      return args.length?rebuild():cur;
    }

    if(cur[0]==="lam"){
      this.tick();
      if(args.length){
        this.need("reduction");
        const arg=args.pop();
        cur=this.substitute(cur[2],arg);
        dirty=true; absorbApps(); continue;
      }
      return cur;
    }

    if(cur[0]==="proj"){
      const out=retainedWhnf.call(this,cur);
      if(out!==cur){
        cur=out; dirty=true; absorbApps(); continue;
      }
      return args.length?rebuild():cur;
    }

    if(cur[0]==="nat"){
      const out=retainedWhnf.call(this,cur);
      cur=out; if(out!==root) dirty=true;
      return args.length?rebuild():cur;
    }

    // sort/var/opaque ctor/theorem and other rigid neutral heads.
    this.tick();
    return args.length?rebuild():cur;
  }
}

function install(mode){
  proto.whnf=retainedWhnf;
  if(mode==="iterative") proto.whnf=iterativeOrdinaryWhnf;
}

const budget=1_000_000;
function evaluate(mode){
  install(mode);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;
  const t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,budget);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0; totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected) wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null,fallback_mode:r.fallback_mode??null,
      retained_reason:r.retained_reason??null,stack_attempt_reason:r.stack_attempt_reason??null,
      stack_attempt_steps:r.stack_attempt_steps??null});
  }
  return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,results};
}

const baseline=evaluate("baseline"), candidate=evaluate("iterative");
proto.whnf=retainedWhnf;
if(baseline.wrong||candidate.wrong) throw new Error("wrong verdict");

const residual=new Set(baseline.results.filter(r=>r.status==="UNKNOWN").map(r=>r.name));
let protectedChanged=0,resolved=0;
const resolvedCases=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++){
  const b=baseline.results[i],r=candidate.results[i];
  if(b.status!=="UNKNOWN"&&r.status!==b.status){
    protectedChanged++; regressions.push({name:r.name,before:b.status,after:r.status,reason:r.reason});
  }
  if(residual.has(r.name)){
    if(r.status!=="UNKNOWN"){
      if(r.status!==r.expected) throw new Error("WRONG_RESOLUTION "+JSON.stringify(r));
      resolved++; resolvedCases.push({name:r.name,status:r.status,steps:r.steps,constructed:r.constructed,
        fallback_mode:r.fallback_mode});
    } else remaining.push({name:r.name,reason:r.reason,steps:r.steps,
      stack_attempt_reason:r.stack_attempt_reason,stack_attempt_steps:r.stack_attempt_steps});
  }
}
const summary={arena_sha256:sha,budget,
  baseline:{counts:baseline.counts,wrong:baseline.wrong,totalSteps:baseline.totalSteps,
    totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
  candidate:{counts:candidate.counts,wrong:candidate.wrong,totalSteps:candidate.totalSteps,
    totalConstructed:candidate.totalConstructed,elapsed_ms:candidate.elapsed_ms},
  protectedChanged,resolved,resolvedCases,regressions,remaining,
  lawful:candidate.wrong===0&&protectedChanged===0,
  promotable:candidate.wrong===0&&protectedChanged===0&&resolved>0,
  claim_boundary:"Execution-only separator. Ordinary application function-position WHNF is traversed iteratively. Recursor/quotient roots and local-definition semantics retain their existing reducers; no proof rule is added."};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/iterative-whnf-separator.json",import.meta.url),JSON.stringify({summary,baseline,candidate},null,2));
console.log("ITERATIVE_WHNF_RESULT "+JSON.stringify(summary));
