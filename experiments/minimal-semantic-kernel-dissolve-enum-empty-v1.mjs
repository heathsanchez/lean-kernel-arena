import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const reduced=caps.filter(c=>c!=="enum-inductives"&&c!=="empty-inductives");
const expectedHash="0cdb181ce17bc4f685beea8d3ccb90675ecc029cae9c4dc86629d2adbcb6e8dd";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok)throw new Error("Arena corpus fetch "+response.status);
const data=Buffer.from(await response.arrayBuffer()),sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash)throw new Error("Arena corpus changed");
const py=String.raw`
import io,tarfile,json,sys
rows=[];data=sys.stdin.buffer.read()
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    p=m.name.split("/")
    if not m.isfile() or not m.name.endswith(".ndjson") or m.size>2000000: continue
    e="ACCEPT" if "good" in p else "REJECT" if "bad" in p else None
    if e: rows.append({"name":m.name,"expected":e,"input":a.extractfile(m).read().decode()})
print(json.dumps(rows))
`;
const rows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:10000}));
const diffs=[];let wrong=0;const counts={baseline:{ACCEPT:0,REJECT:0,UNKNOWN:0},reduced:{ACCEPT:0,REJECT:0,UNKNOWN:0}};
for(const row of rows){
  const b=K.checkExport(row.input,caps,1000000);
  const r=K.checkExport(row.input,reduced,1000000);
  counts.baseline[b.status]++;counts.reduced[r.status]++;
  if(r.status!=="UNKNOWN"&&r.status!==row.expected)wrong++;
  if(r.status!==b.status||r.reason!==b.reason)diffs.push({name:row.name,expected:row.expected,before:{status:b.status,reason:b.reason},after:{status:r.status,reason:r.reason}});
}
console.log("MINIMAL_SEMANTIC_KERNEL_DISSOLVE_ENUM_EMPTY "+JSON.stringify({
  arena_sha256:sha,removed:["enum-inductives","empty-inductives"],counts,wrong,diffCount:diffs.length,diffs:diffs.slice(0,100),
  exactVerdictEquivalent:diffs.every(d=>d.before.status===d.after.status),
  exactStatusAndReasonEquivalent:diffs.length===0,
  claim_boundary:"Corpus equivalence only. This shows the retained enum/empty capability gates are redundant under the current single-inductive machinery on this frozen Arena corpus; it does not yet delete their implementation code or prove semantic equivalence universally."
}));
