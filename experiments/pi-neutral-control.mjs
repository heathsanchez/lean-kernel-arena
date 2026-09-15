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
data=sys.stdin.buffer.read();rows=[]
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    p=m.name.split("/")
    if not m.isfile() or not m.name.endswith(".ndjson") or m.size>2000000: continue
    e="ACCEPT" if "good" in p else "REJECT" if "bad" in p else None
    if e: rows.append({"name":m.name,"expected":e,"input":a.extractfile(m).read().decode("utf-8")})
print(json.dumps(rows))
`;
const rows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));
if(rows.length!==188)throw new Error("Arena row count changed");
const focusRows=rows.filter(r=>r.name.endsWith("good/perf/fueled-chain.ndjson"));

const proto=K.Kernel.prototype,retainedEqual=proto.equal;
const stats={raw:0,whnf:0,hits:0};

function neutralVarApp(e){
  if(!Array.isArray(e)||e[0]!=="app")return false;
  let h=e,n=0;
  while(Array.isArray(h)&&h[0]==="app"){n++;h=h[1];}
  return n>0&&Array.isArray(h)&&h[0]==="var";
}
function install(mode){
  proto.equal=retainedEqual;
  if(mode==="baseline")return;
  proto.equal=function(a,b,ctx=[]){
    if(this.localDefs===true && this.caps.has("rigid-conversion")){
      const raw=(Array.isArray(a)&&a[0]==="pi"&&neutralVarApp(b))||
                (Array.isArray(b)&&b[0]==="pi"&&neutralVarApp(a));
      if(raw){
        stats.raw++;
        const x=this.whnf(a),y=this.whnf(b); stats.whnf++;
        const hit=(Array.isArray(x)&&x[0]==="pi"&&neutralVarApp(y))||
                  (Array.isArray(y)&&y[0]==="pi"&&neutralVarApp(x));
        if(hit){
          stats.hits++;
          if(mode==="reject")this.reject("rigid-head-mismatch");
          this.unknown("pi-neutral-head-obstruction");
        }
      }
    }
    return retainedEqual.call(this,a,b,ctx);
  };
}
function evalRows(mode,subset){
  install(mode);
  const before={...stats},results=[],counts={ACCEPT:0,REJECT:0,UNKNOWN:0};
  let wrong=0,totalSteps=0,totalConstructed=0;const t0=Date.now();
  for(const row of subset){
    const r=K.checkExport(row.input,caps,1_000_000);
    counts[r.status]=(counts[r.status]??0)+1;
    totalSteps+=r.steps??0;totalConstructed+=r.constructed??0;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected)wrong++;
    results.push({name:row.name,expected:row.expected,status:r.status,reason:r.reason,
      steps:r.steps??null,constructed:r.constructed??null,frontier_declaration:r.frontier_declaration??null,
      fallback_mode:r.fallback_mode??null,fallback_attempt_reason:r.fallback_attempt_reason??null});
  }
  return {mode,counts,wrong,totalSteps,totalConstructed,elapsed_ms:Date.now()-t0,
    stats:{raw:stats.raw-before.raw,whnf:stats.whnf-before.whnf,hits:stats.hits-before.hits},results};
}

const baseline=evalRows("baseline",focusRows);
const unknown=evalRows("unknown",focusRows);
const reject=evalRows("reject",focusRows);
console.log("PI_NEUTRAL_CONTROL_FOCUS "+JSON.stringify({baseline,unknown,reject}));
let winner=null;
if(unknown.results[0]?.status==="ACCEPT")winner="unknown";
if(reject.results[0]?.status==="ACCEPT")winner="reject";
if(!winner){install("baseline");process.exit(0);}

const candidate=evalRows(winner,rows);
const control=evalRows("baseline",rows);
install("baseline");
if(candidate.wrong||control.wrong)throw new Error("wrong verdict");
let protectedChanged=0;const resolved=[],regressions=[],remaining=[];
for(let i=0;i<rows.length;i++){
  const b=control.results[i],c=candidate.results[i];
  if(b.status!=="UNKNOWN"&&c.status!==b.status){
    protectedChanged++;regressions.push({name:c.name,before:b.status,after:c.status,reason:c.reason});
  }
  if(b.status==="UNKNOWN"){
    if(c.status!=="UNKNOWN"&&c.status===c.expected)resolved.push({name:c.name,status:c.status,reason:c.reason,steps:c.steps});
    else remaining.push({name:c.name,status:c.status,reason:c.reason,steps:c.steps});
  }
}
console.log("PI_NEUTRAL_CONTROL_FULL "+JSON.stringify({
  arena_sha256:sha,winner,
  baseline:{counts:control.counts,totalSteps:control.totalSteps,totalConstructed:control.totalConstructed},
  candidate:{counts:candidate.counts,totalSteps:candidate.totalSteps,totalConstructed:candidate.totalConstructed,
    stats:candidate.stats,protectedChanged,resolved,regressions,remaining},
  lawful:candidate.wrong===0&&protectedChanged===0,
  promotable:candidate.wrong===0&&protectedChanged===0&&resolved.some(r=>r.name.endsWith("fueled-chain.ndjson"))
}));
