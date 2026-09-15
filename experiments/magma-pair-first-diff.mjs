// Diagnostic only. Capture the full normalized terms at the current
// conversion frontier without changing kernel semantics, then locate the first
// structural difference and its nearest ancestors.
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
try {
  result=K.checkExport(row.input,caps,1_000_000);
} finally {
  JSON.stringify=realStringify;
}
if(result.reason!=="conversion-frontier") throw new Error("frontier not reproduced: "+realStringify(result));
if(captured.length<2) throw new Error("full frontier terms not captured: "+captured.length);
const left=captured[captured.length-2].value;
const right=captured[captured.length-1].value;

function brief(x) {
  if(!Array.isArray(x)) return x;
  if(x[0]==="const") return ["const",x[1],...(x.length===3?[x[2]]:[])];
  if(x[0]==="var"||x[0]==="nat"||x[0]==="strlit"||x[0]==="sort") return x;
  if(x[0]==="proj") return ["proj",x[1],x[2],"..."];
  return [x[0],"…",x.length-1];
}
function firstDiff(a,b) {
  const stack=[{a,b,path:[],ancestors:[]}];
  while(stack.length) {
    const f=stack.pop();
    if(f.a===f.b) continue;
    const aa=Array.isArray(f.a),bb=Array.isArray(f.b);
    if(!aa||!bb) {
      if(f.a!==f.b) return {...f,left:brief(f.a),right:brief(f.b)};
      continue;
    }
    if(f.a.length!==f.b.length)
      return {...f,left:["len",f.a.length,brief(f.a)],right:["len",f.b.length,brief(f.b)]};
    let primitiveMismatch=false;
    for(let i=0;i<f.a.length;i++) {
      if(!Array.isArray(f.a[i])&&!Array.isArray(f.b[i])&&f.a[i]!==f.b[i]) {
        return {path:[...f.path,i],ancestors:f.ancestors,
          left:brief(f.a[i]),right:brief(f.b[i]),
          parentLeft:brief(f.a),parentRight:brief(f.b)};
      }
      if(Array.isArray(f.a[i])!==Array.isArray(f.b[i])) {
        primitiveMismatch=true;
        return {path:[...f.path,i],ancestors:f.ancestors,
          left:brief(f.a[i]),right:brief(f.b[i]),
          parentLeft:brief(f.a),parentRight:brief(f.b)};
      }
    }
    if(primitiveMismatch) continue;
    const nextAnc=[...f.ancestors.slice(-10),{path:f.path,left:brief(f.a),right:brief(f.b)}];
    // Push in reverse so lowest child index is visited first.
    for(let i=f.a.length-1;i>=0;i--) {
      if(Array.isArray(f.a[i])||Array.isArray(f.b[i]))
        stack.push({a:f.a[i],b:f.b[i],path:[...f.path,i],ancestors:nextAnc});
    }
  }
  return null;
}

function stats(root) {
  let nodes=0,apps=0,proofish=0; const seen=new Set(),stack=[root];
  while(stack.length) {
    const x=stack.pop();
    if(!Array.isArray(x)||seen.has(x)) continue;
    seen.add(x); nodes++;
    if(x[0]==="app") apps++;
    if(x[0]==="const" && typeof x[1]==="string" &&
       (x[1].includes('\"Eq\"')||x[1].includes('\"HEq\"')||x[1].includes('\"le\"'))) proofish++;
    for(let i=1;i<x.length;i++) if(Array.isArray(x[i])) stack.push(x[i]);
  }
  return {nodes,apps,proofish};
}

const diff=firstDiff(left,right);
console.log("MAGMA_PAIR_FIRST_DIFF "+realStringify({
  status:result.status,reason:result.reason,steps:result.steps,
  frontier_declaration:result.frontier_declaration,
  left_bytes:captured[captured.length-2].bytes,
  right_bytes:captured[captured.length-1].bytes,
  left_stats:stats(left),right_stats:stats(right),
  diff
}));
