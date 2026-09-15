import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok)throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer()),sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash)throw new Error("Arena corpus changed");
const py=String.raw`
import io,tarfile,json,sys
wanted={"good/perf/fueled-chain.ndjson","good/perf/shared-subterm.ndjson"}
data=sys.stdin.buffer.read();rows=[]
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    p="/".join(m.name.split("/")[-3:])
    if m.isfile() and p in wanted:
      rows.append({"name":p,"expected":"ACCEPT","input":a.extractfile(m).read().decode("utf-8")})
print(json.dumps(rows))
`;
const focusRows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));
if(focusRows.length!==2)throw new Error("focus rows missing");

const proto=K.Kernel.prototype;
const retainedRun=proto.run,retainedMake=proto.make,retainedSame=proto.same;

const END=Symbol("end");
function ensure(k){
  k.__canonWeak??=new WeakMap();
  k.__canonRoot??=new Map();
}
function intern(k,e){
  if(!Array.isArray(e))return e;
  ensure(k);
  const old=k.__canonWeak.get(e);
  if(old!==undefined)return old;

  const xs=new Array(e.length);
  let changed=false;
  for(let i=0;i<e.length;i++){
    const x=e[i];
    const y=Array.isArray(x)?intern(k,x):x;
    xs[i]=y;
    if(y!==x)changed=true;
  }

  let node=k.__canonRoot;
  for(const x of xs){
    let next=node.get(x);
    if(!(next instanceof Map)){next=new Map();node.set(x,next);}
    node=next;
  }
  let rep=node.get(END);
  if(rep===undefined){
    rep=changed?xs:e;
    node.set(END,rep);
  }
  k.__canonWeak.set(e,rep);
  k.__canonWeak.set(rep,rep);
  return rep;
}

function install(mode){
  proto.run=retainedRun;proto.make=retainedMake;proto.same=retainedSame;
  if(mode==="baseline")return;
  proto.run=function(...args){
    this.__canonWeak=new WeakMap();
    this.__canonRoot=new Map();
    return retainedRun.apply(this,args);
  };
  proto.same=function(a,b){
    this.tick();
    if(a===b)return true;
    if(!Array.isArray(a)||!Array.isArray(b))return false;
    return intern(this,a)===intern(this,b);
  };
  if(mode==="canon-make-same"){
    proto.make=function(...xs){
      ensure(this);
      const ys=xs.map(x=>Array.isArray(x)?intern(this,x):x);
      const out=retainedMake.call(this,...ys);
      return intern(this,out);
    };
  }
}

function evalRows(mode,rows){
  install(mode);
  const results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;const t0=Date.now();
  for(const row of rows){
    const r=K.checkExport(row.input,caps,1_000_000);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0;totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected)wrong++;
    results.push({name:row.name,status:r.status,reason:r.reason,steps:r.steps??null,constructed:r.constructed??null,
      frontier_declaration:r.frontier_declaration??null});
  }
  return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,results};
}

const baseline=evalRows("baseline",focusRows);
const sameOnly=evalRows("canon-same",focusRows);
const full=evalRows("canon-make-same",focusRows);
install("baseline");
console.log("STRUCTURAL_CANON_FOCUS "+JSON.stringify({baseline,sameOnly,full}));

const resolved=x=>x.results.filter(r=>r.status==="ACCEPT").length;
let winner=resolved(full)>=resolved(sameOnly)?"canon-make-same":"canon-same";
let win=winner==="canon-make-same"?full:sameOnly;
if(win.wrong||resolved(win)===0){
  console.log("STRUCTURAL_CANON_STOP "+JSON.stringify({reason:"no-focus-resolution",winner,win}));
  process.exit(0);
}

const pyAll=String.raw`
import io,tarfile,json,sys
data=sys.stdin.buffer.read();rows=[]
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    p=m.name.split("/")
    if not m.isfile() or not m.name.endswith(".ndjson") or m.size>2000000: continue
    e="ACCEPT" if "good" in p else "REJECT" if "bad" in p else None
    if e: rows.append({"name":m.name,"expected":e,"input":a.extractfile(m).read().decode("utf-8")})
print(json.dumps(rows))
`;
const rows=JSON.parse(execFileSync("python3",["-c",pyAll],{input:data,maxBuffer:50000000,timeout:10000}));
const candidate=evalRows(winner,rows),base=evalRows("baseline",rows);install("baseline");
if(candidate.wrong||base.wrong)throw new Error("wrong verdict");
let protectedChanged=0;const resolvedCases=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++){
  const b=base.results[i],c=candidate.results[i];
  if(b.status!=="UNKNOWN"&&c.status!==b.status){
    protectedChanged++;regressions.push({name:c.name,before:b.status,after:c.status,reason:c.reason});
  }
  if(b.status==="UNKNOWN"){
    if(c.status!=="UNKNOWN"&&c.status===rows[i].expected)resolvedCases.push({name:c.name,status:c.status,steps:c.steps,constructed:c.constructed});
    else remaining.push({name:c.name,status:c.status,reason:c.reason,steps:c.steps});
  }
}
const report={arena_sha256:sha,budget:1000000,winner,focus:{baseline,sameOnly,full},
  baseline:{counts:base.counts,totalSteps:base.totalSteps,totalConstructed:base.totalConstructed,elapsed_ms:base.elapsed_ms},
  candidate:{counts:candidate.counts,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,elapsed_ms:candidate.elapsed_ms,
    protectedChanged,resolved:resolvedCases,regressions,remaining},
  lawful:candidate.wrong===0&&protectedChanged===0,
  promotable:candidate.wrong===0&&protectedChanged===0&&resolvedCases.length>0,
  claim_boundary:"Execution identity only. Exact recursive structural representatives are interned collision-free through nested Map tries. canon-same replaces repeated recursive structural equality with representative identity; canon-make-same additionally routes constructed nodes through exact canonical children/representatives. No semantic equality, typing, or reduction rule is added."
};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/structural-canonical-representatives.json",import.meta.url),JSON.stringify(report,null,2)+"\n");
console.log("STRUCTURAL_CANON "+JSON.stringify(report));
