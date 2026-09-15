// Diagnose the surviving Arena UNKNOWNs without changing kernel semantics.
// Same retained capabilities and pinned corpus; only operation budget / host stack vary.
import {readFileSync,writeFileSync,mkdirSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import {checkExport} from "./kernel.mjs";

const caps=JSON.parse(readFileSync(new URL("./evidence/retained.json",import.meta.url),"utf8"));
const url="https://arena.lean-lang.org/lean-arena-tests.tar.gz";
const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch(url,{signal:AbortSignal.timeout(15000)});
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

const baselineBudget=1_000_000;
const budgets=[2_000_000,4_000_000,8_000_000,16_000_000];
const residual=[];
for(const row of rows) {
  const r=checkExport(row.input,caps,baselineBudget);
  if(r.status==="UNKNOWN" && ["budget-exhausted","host-stack-limit"].includes(r.reason))
    residual.push({row,baseline:r});
}
if(residual.length!==19) throw new Error("residual count changed: "+residual.length);

const out=[];
for(const {row,baseline} of residual) {
  const attempts=[];
  let resolved=null;
  for(const budget of budgets) {
    const t=Date.now();
    const r=checkExport(row.input,caps,budget);
    const a={budget,status:r.status,reason:r.reason,steps:r.steps??null,elapsed_ms:Date.now()-t};
    attempts.push(a);
    if(r.status!=="UNKNOWN") {
      if(r.status!==row.expected) {
        writeFileSync(new URL("./evidence/resource-counterexample.ndjson",import.meta.url),row.input);
        throw new Error("WRONG_VERDICT "+JSON.stringify({name:row.name,expected:row.expected,result:r,budget}));
      }
      resolved=a; break;
    }
    if(r.reason!=="budget-exhausted" && r.reason!=="host-stack-limit") break;
  }
  out.push({name:row.name,expected:row.expected,baseline_reason:baseline.reason,attempts,resolved});
  console.log("RESOURCE_RESIDUAL "+JSON.stringify(out.at(-1)));
}
mkdirSync(new URL("./evidence/",import.meta.url),{recursive:true});
const summary={
  arena_sha256:sha,
  baseline_budget:baselineBudget,
  budgets,
  residual_count:out.length,
  resolved_count:out.filter(x=>x.resolved).length,
  unresolved_count:out.filter(x=>!x.resolved).length,
  resolved_accept:out.filter(x=>x.resolved?.status==="ACCEPT").length,
  resolved_reject:out.filter(x=>x.resolved?.status==="REJECT").length,
  unresolved:out.filter(x=>!x.resolved).map(x=>({name:x.name,expected:x.expected,baseline_reason:x.baseline_reason,last:x.attempts.at(-1)})),
  scope:"Resource diagnostic only. No semantic capability or verdict rule changed."
};
writeFileSync(new URL("./evidence/resource-frontier.json",import.meta.url),JSON.stringify({summary,results:out},null,2));
console.log("RESOURCE_FRONTIER_SUMMARY "+JSON.stringify(summary));
