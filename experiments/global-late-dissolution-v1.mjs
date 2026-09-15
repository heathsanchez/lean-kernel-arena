import {readFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const drop=process.env.KERNEL_DISSOLVE_CAP;
if(!drop||!caps.includes(drop))throw new Error("capability not in retained basis: "+drop);
const reduced=caps.filter(c=>c!==drop);
const expectedHash="0cdb181ce17bc4f685beea8d3ccb90675ecc029cae9c4dc86629d2adbcb6e8dd";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok)throw new Error("Arena corpus fetch "+response.status);
const data=Buffer.from(await response.arrayBuffer()),sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash)throw new Error("Arena corpus changed: got "+sha);
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

function run(cset){
  const out=[];const counts={ACCEPT:0,REJECT:0,UNKNOWN:0};let wrong=0;
  for(const row of rows){
    const r=K.checkExport(row.input,cset,1000000);
    counts[r.status]++;
    if(r.status!=="UNKNOWN"&&r.status!==row.expected)wrong++;
    out.push({name:row.name,status:r.status,reason:r.reason,expected:row.expected});
  }
  return {out,counts,wrong};
}
const b=run(caps),a=run(reduced);
if(b.wrong)throw new Error("baseline wrong="+b.wrong);
const diffs=[],statusDiffs=[];
for(let i=0;i<rows.length;i++){
  const x=b.out[i],y=a.out[i];
  if(x.status!==y.status||x.reason!==y.reason)
    diffs.push({name:x.name,expected:x.expected,before:{status:x.status,reason:x.reason},after:{status:y.status,reason:y.reason}});
  if(x.status!==y.status)
    statusDiffs.push({name:x.name,expected:x.expected,before:x.status,after:y.status,reason:y.reason});
}
console.log("GLOBAL_LATE_DISSOLUTION "+JSON.stringify({
  drop,arena_sha256:sha,basisSize:caps.length,reducedSize:reduced.length,
  baseline:b.counts,reduced:a.counts,wrong:a.wrong,
  statusDiffCount:statusDiffs.length,reasonOrStatusDiffCount:diffs.length,
  verdictEquivalent:a.wrong===0&&statusDiffs.length===0,
  exactEquivalent:a.wrong===0&&diffs.length===0,
  statusDiffs:statusDiffs.slice(0,60),diffs:diffs.slice(0,30)
}));
