// Diagnostic only: capture the full normalized conversion-frontier terms
// and profile every aligned structural difference, including binder depth.
import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const target="good/perf/magma-list-pair-n7.ndjson";

const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok) throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer());
const sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash) throw new Error("Arena corpus changed");
const py=String.raw`
import io,tarfile,json,sys
data=sys.stdin.buffer.read()
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    p="/".join(m.name.split("/")[-3:])
    if m.isfile() and p=="good/perf/magma-list-pair-n7.ndjson":
      print(json.dumps({"name":p,"input":a.extractfile(m).read().decode("utf-8")}))
      break
`;
const row=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));

const realStringify=JSON.stringify;
const captured=[];
JSON.stringify=function(value,...rest) {
  const s=realStringify(value,...rest);
  if(Array.isArray(value) && s.length>20_000) captured.push({value,bytes:s.length});
  return s;
};
let result;
try { result=K.checkExport(row.input,caps,1_000_000); }
finally { JSON.stringify=realStringify; }
if(result.reason!=="conversion-frontier") throw new Error("frontier not reproduced");
const left=captured.at(-2)?.value,right=captured.at(-1)?.value;
if(!left||!right) throw new Error("frontier terms missing");

const mismatches=new Map();
const examples=[];
let paired=0,sharedIdentity=0,arrayShapeMismatch=0;
const work=[{a:left,b:right,path:[],binders:0}];
function bump(key,ex) {
  mismatches.set(key,(mismatches.get(key)??0)+1);
  if(examples.length<30) examples.push({key,...ex});
}
while(work.length) {
  const f=work.pop(),a=f.a,b=f.b;
  paired++;
  if(a===b) { sharedIdentity++; continue; }
  const aa=Array.isArray(a),bb=Array.isArray(b);
  if(!aa||!bb) {
    if(a!==b) bump(`primitive:${typeof a}:${String(a)}->${String(b)}`,
      {path:f.path,binders:f.binders,left:a,right:b});
    continue;
  }
  if(a.length!==b.length||a[0]!==b[0]) {
    arrayShapeMismatch++;
    bump(`shape:${a[0]}/${a.length}->${b[0]}/${b.length}`,
      {path:f.path,binders:f.binders});
    continue;
  }

  const tag=a[0];
  if(tag==="var") {
    if(a[1]!==b[1]) bump(`var:${a[1]}->${b[1]}@b${f.binders}`,
      {path:f.path,binders:f.binders,left:a[1],right:b[1],
       outerLeft:a[1]-f.binders,outerRight:b[1]-f.binders});
    continue;
  }
  if(tag==="nat"||tag==="strlit") {
    if(a[1]!==b[1]) bump(`${tag}:${a[1]}->${b[1]}@b${f.binders}`,
      {path:f.path,binders:f.binders});
    continue;
  }
  if(tag==="const") {
    if(a[1]!==b[1]) bump("const-name",{path:f.path,binders:f.binders,left:a[1],right:b[1]});
    // Universe arrays are ordinary children below.
  }
  if(tag==="sort") {
    // Level structures are ordinary children below.
  }

  for(let i=a.length-1;i>=1;i--) {
    const childBinders =
      (tag==="lam"||tag==="pi") && i===2 ? f.binders+1 :
      tag==="let" && i===3 ? f.binders+1 : f.binders;
    const x=a[i],y=b[i];
    if(Array.isArray(x)||Array.isArray(y)) {
      work.push({a:x,b:y,path:[...f.path,i],binders:childBinders});
    } else if(x!==y) {
      bump(`field:${tag}[${i}]:${String(x)}->${String(y)}@b${childBinders}`,
        {path:[...f.path,i],binders:childBinders,left:x,right:y});
    }
  }
}

const counts=[...mismatches.entries()].sort((a,b)=>b[1]-a[1]);
console.log("MAGMA_PAIR_DIFF_PROFILE "+realStringify({
  status:result.status,reason:result.reason,steps:result.steps,
  frontier_declaration:result.frontier_declaration,
  left_bytes:captured.at(-2).bytes,right_bytes:captured.at(-1).bytes,
  paired,sharedIdentity,arrayShapeMismatch,
  mismatchKinds:counts.length,totalMismatches:counts.reduce((s,x)=>s+x[1],0),
  counts,examples
}));
