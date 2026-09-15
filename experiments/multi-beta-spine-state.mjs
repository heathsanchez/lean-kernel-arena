// Exact multi-beta materialization for consecutive raw beta chains.
//
// For
//   (fun x1 => (fun x2 => ... (fun xn => body) an ...) a2) a1
// collect a1..an without substituting. Argument ai is stored at index i-1 and
// was captured under exactly i-1 previously eliminated binders. The final body
// is materialized once with an explicit stack. A de-Bruijn variable referring
// to an eliminated binder maps in O(1) to args[capture - 1 - index], and that
// argument is recursively interpreted with capture equal to its own index.
//
// This is exact beta reduction, not a benchmark-specific identity. It changes
// only execution order and avoids the Θ(n²) repeated tree copying of sequential
// substitution. Chains shorter than two redexes use the retained WHNF unchanged.
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
const retainedRun=proto.run,retainedWhnf=proto.whnf;
const stats={queries:0,chains:0,redexes:0,maxChain:0,materializedNodes:0,varSubstitutions:0,
  iterativeCalls:0,flattenApps:0,rebuildApps:0,attachedArgs:0,defUnfolds:0,recFrames:0,recReductions:0,recBlocked:0,
  projFrames:0,projReductions:0,projBlocked:0};

function collect(root){
  const args=[];let cur=root;
  while(Array.isArray(cur)&&cur[0]==="app"&&Array.isArray(cur[1])&&cur[1][0]==="lam"){
    args.push(cur[2]);
    cur=cur[1][2];
  }
  return {body:cur,args};
}

function materialize(k,body,args){
  const work=[{kind:"visit",term:body,capture:args.length,depth:0,extra:0}],vals=[];
  while(work.length){
    const f=work.pop();
    if(f.kind==="build"){
      let out;
      if(f.tag==="proj"){
        out=k.make("proj",f.name,f.index,vals.pop());
      }else{
        const xs=new Array(f.n);
        for(let i=f.n-1;i>=0;i--)xs[i]=vals.pop();
        out=k.make(f.tag,...xs);
      }
      vals.push(out);
      continue;
    }

    const e=f.term;
    k.tick();stats.materializedNodes++;
    switch(e[0]){
      case "sort": case "const": case "nat": case "strlit":
        vals.push(e);break;
      case "var":{
        const i=e[1];
        if(i<f.depth){vals.push(e);break;}
        const j=i-f.depth;
        if(j<f.capture){
          const argIndex=f.capture-1-j;
          stats.varSubstitutions++;
          work.push({kind:"visit",term:args[argIndex],capture:argIndex,depth:0,extra:f.extra+f.depth});
        }else{
          const ni=f.depth+(j-f.capture)+f.extra;
          vals.push(ni===i?e:k.make("var",ni));
        }
        break;
      }
      case "pi": case "lam":
        work.push({kind:"build",tag:e[0],n:2});
        work.push({kind:"visit",term:e[2],capture:f.capture,depth:f.depth+1,extra:f.extra});
        work.push({kind:"visit",term:e[1],capture:f.capture,depth:f.depth,extra:f.extra});
        break;
      case "app":
        work.push({kind:"build",tag:"app",n:2});
        work.push({kind:"visit",term:e[2],capture:f.capture,depth:f.depth,extra:f.extra});
        work.push({kind:"visit",term:e[1],capture:f.capture,depth:f.depth,extra:f.extra});
        break;
      case "proj":
        work.push({kind:"build",tag:"proj",name:e[1],index:e[2]});
        work.push({kind:"visit",term:e[3],capture:f.capture,depth:f.depth,extra:f.extra});
        break;
      case "let":
        work.push({kind:"build",tag:"let",n:3});
        work.push({kind:"visit",term:e[3],capture:f.capture,depth:f.depth+1,extra:f.extra});
        work.push({kind:"visit",term:e[2],capture:f.capture,depth:f.depth,extra:f.extra});
        work.push({kind:"visit",term:e[1],capture:f.capture,depth:f.depth,extra:f.extra});
        break;
      default:
        k.unknown("multi-beta-materialize-syntax");
    }
  }
  return vals.pop();
}


function iterativeRecWhnf(k,root){
  stats.iterativeCalls++;
  const frames=[];

  function rebuild(head,args){
    let out=head;
    for(const a of args){ stats.rebuildApps++; out=k.make("app",out,a); }
    return out;
  }

  function flatten(term){
    const args=[];
    let head=term;
    while(Array.isArray(head)&&head[0]==="app"){
      stats.flattenApps++;
      k.tick(); k.need("application");
      args.push(head[2]); head=head[1];
    }
    args.reverse();
    return {head,args};
  }

  function attach(term,extraArgs){
    const st=flatten(term);
    if(extraArgs?.length){
      stats.attachedArgs+=extraArgs.length;
      st.args.push(...extraArgs);
    }
    return st;
  }

  function resumeRec(fr,major){
    const {head:rh,args:rargs,d:rd,total}=fr;
    const ms=flatten(major),mh=ms.head,margs=ms.args;
    const md=mh?.[0]==="const"?k.env.get(mh[1]):null;

    if(md?.kind==="ctor"&&md.induct===rd.induct&&
       margs.length===md.numParams+md.numFields){
      let paramsMatch=true;
      for(let i=0;i<rd.numParams;i++){
        if(!k.same(margs[i],rargs[i])){paramsMatch=false;break;}
      }
      if(paramsMatch){
        const rule=rd.rules.find(rr=>rr.ctor===md.name);
        if(rule){
          stats.recReductions++;
          k.need("inductive-reduction"); k.need("reduction");
          const rhs=k.instantiateDeclaration(rh,rule.rhs);
          const prefix=rargs.slice(0,rd.numParams+1+rd.numMinors);
          const nextArgs=prefix.concat(margs.slice(md.numParams),rargs.slice(total));
          return {state:attach(rhs,nextArgs)};
        }
      }
    }

    stats.recBlocked++;
    return {value:rebuild(rh,rargs)};
  }

  let state=flatten(root);

  for(;;){
    let {head,args}=state;

    if(!Array.isArray(head))
      return retainedWhnf.call(k,rebuild(head,args));

    if(head[0]==="let"){
      k.tick(); k.need("reduction");
      state=attach(k.substitute(head[3],head[2]),args);
      continue;
    }

    if(head[0]==="nat"){
      // Let the retained reducer perform the one-step literal rule. It cannot
      // recurse structurally on the literal itself.
      const lit=retainedWhnf.call(k,head);
      state=attach(lit,args);
      continue;
    }

    if(head[0]==="lam"){
      k.tick();
      if(args.length){
        k.need("reduction");
        state=attach(k.substitute(head[2],args[0]),args.slice(1));
        continue;
      }
    }

    if(head[0]==="proj"){
      stats.projFrames++;
      frames.push({kind:"proj",name:head[1],index:head[2],object:head[3],args});
      state=flatten(head[3]);
      continue;
    }

    if(head[0]==="const"){
      k.tick(); k.need("declarations");
      const d=k.env.get(head[1]);
      if(!d) k.reject("undeclared-constant");

      if(d.kind==="def"){
        stats.defUnfolds++;
        k.need("reduction");
        state=attach(k.instantiateDeclaration(head,d.value),args);
        continue;
      }

      if(d.kind==="rec"){
        const total=d.numParams+1+d.numMinors+d.numIndices+1;
        if(args.length>=total){
          stats.recFrames++;
          frames.push({kind:"rec",head,args,d,total});
          state=flatten(args[total-1]);
          continue;
        }
      }
    }

    let result=rebuild(head,args);
    while(frames.length){
      const fr=frames.pop();

      if(fr.kind==="proj"){
        const ms=flatten(result),mh=ms.head,margs=ms.args;
        const ind=k.env.get(fr.name);
        const ctor=ind?.kind==="inductive"&&ind.ctors?.length===1?ind.ctors[0]:null;
        if(ctor!==null&&mh?.[0]==="const"&&mh[1]===ctor){
          const pos=ind.numParams+fr.index;
          if(pos>=margs.length) k.reject("projection-out-of-range");
          stats.projReductions++;
          state=attach(margs[pos],fr.args);
          result=null;
          break;
        }
        stats.projBlocked++;
        const p=result===fr.object
          ? k.make("proj",fr.name,fr.index,fr.object)
          : k.make("proj",fr.name,fr.index,result);
        result=rebuild(p,fr.args);
        continue;
      }

      const resumed=resumeRec(fr,result);
      if(resumed.state){
        state=resumed.state;
        result=null;
        break;
      }
      result=resumed.value;
    }
    if(result!==null) return result;
  }
}

function iterativeCached(k,e){
  if(!Array.isArray(e)||k.localDefs===true) return iterativeRecWhnf(k,e);
  k.__multiBetaWhnfCache??=new WeakMap();
  if(k.__multiBetaWhnfCache.has(e)) return k.__multiBetaWhnfCache.get(e);
  const out=iterativeRecWhnf(k,e);
  k.__multiBetaWhnfCache.set(e,out);
  return out;
}

function install(enabled){
  proto.run=retainedRun;proto.whnf=retainedWhnf;
  if(!enabled)return;
  proto.run=function(...args){
    this.__multiBetaWhnfCache=new WeakMap();
    this.__multiBetaActivated=false;
    return retainedRun.apply(this,args);
  };
  proto.whnf=function(e){
    if(this._fullStackSafe===true)
      return iterativeCached(this,e);
    if(this._multiBetaDepth || this.__multiBetaActivated===true)
      return iterativeCached(this,e);
    if(!Array.isArray(e)||e[0]!=="app")
      return retainedWhnf.call(this,e);
    stats.queries++;
    const c=collect(e);
    if(c.args.length<2)return retainedWhnf.call(this,e);

    stats.chains++;stats.redexes+=c.args.length;stats.maxChain=Math.max(stats.maxChain,c.args.length);
    this.__multiBetaActivated=true;
    this._multiBetaDepth=1;
    try{
      for(let i=0;i<c.args.length;i++){
        this.tick();this.need("application");this.need("reduction");
      }
      const out=materialize(this,c.body,c.args);
      return iterativeCached(this,out);
    }finally{
      this._multiBetaDepth=0;
    }
  };
}

function evalRows(mode,enabled,subset){
  install(enabled);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;
  const before={...stats},t0=Date.now();
  for(const row of subset){
    const r=K.checkExport(row.input,caps,1_000_000);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0;totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected)wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null,frontier_declaration:r.frontier_declaration??null,
      diagnostic_error:r.diagnostic_error??null,stack_attempt_reason:r.stack_attempt_reason??null,
      stack_attempt_steps:r.stack_attempt_steps??null,fallback_mode:r.fallback_mode??null,
      fallback_attempt_reason:r.fallback_attempt_reason??null,fallback_attempt_steps:r.fallback_attempt_steps??null});
  }
  const delta={};for(const k of Object.keys(before))delta[k]=stats[k]-before[k];
  return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,stats:delta,results};
}

const focusRows=rows.filter(r=>r.name.endsWith("good/perf/beta-ladder.ndjson"));
const focus=evalRows("focus",true,focusRows);
console.log("MULTI_BETA_SPINE_STATE_FOCUS "+JSON.stringify({focus}));
if(focus.wrong)throw new Error("focus wrong");
if(focus.results[0]?.status!=="ACCEPT"){
  install(false);
  console.log("MULTI_BETA_SPINE_STATE_STOP "+JSON.stringify({reason:"beta-not-closed",focus}));
  process.exit(0);
}

const candidate=evalRows("candidate",true,rows);
const baseline=evalRows("baseline",false,rows);
install(false);
if(candidate.wrong||baseline.wrong)throw new Error("wrong verdict");

let protectedChanged=0;
const resolved=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++){
  const b=baseline.results[i],c=candidate.results[i];
  if(b.status!=="UNKNOWN"&&c.status!==b.status){
    protectedChanged++;regressions.push({name:c.name,before:b.status,after:c.status,reason:c.reason});
  }
  if(b.status==="UNKNOWN"&&c.status!=="UNKNOWN"&&c.status===c.expected)
    resolved.push({name:c.name,status:c.status,reason:c.reason,steps:c.steps,constructed:c.constructed});
  else if(b.status==="UNKNOWN")
    remaining.push({name:c.name,status:c.status,reason:c.reason,steps:c.steps});
}
const summary={arena_sha256:sha,budget:1_000_000,focus,
 baseline:{counts:baseline.counts,totalSteps:baseline.totalSteps,totalConstructed:baseline.totalConstructed,elapsed_ms:baseline.elapsed_ms},
 candidate:{counts:candidate.counts,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,
   elapsed_ms:candidate.elapsed_ms,stats:candidate.stats,protectedChanged,resolved,regressions,remaining},
 lawful:candidate.wrong===0&&protectedChanged===0,
 promotable:candidate.wrong===0&&protectedChanged===0&&resolved.some(r=>r.name.endsWith("beta-ladder.ndjson")),
 claim_boundary:"Exact execution-order change only. Two-or-more consecutive raw beta redexes are materialized once with exact de-Bruijn capture counts. Subsequent WHNF stays on one explicit continuation that carries application spines as head+argument state across definition unfolding, beta, recursor, and projection reductions, avoiding construction and immediate re-decomposition of equivalent intermediate app trees. Only retained projection and recursor rules are applied; no conversion, typing, or reduction law is added."
};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/multi-beta-spine-state.json",import.meta.url),JSON.stringify(summary,null,2)+"\n");
console.log("MULTI_BETA_SPINE_STATE "+JSON.stringify(summary));
