import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";

const url="https://arena.lean-lang.org/lean-arena-tests.tar.gz";
const expectedHash="0cdb181ce17bc4f685beea8d3ccb90675ecc029cae9c4dc86629d2adbcb6e8dd";
const response=await fetch(url,{signal:AbortSignal.timeout(15000)});
if(!response.ok)throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer());
const sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash)throw new Error("Arena corpus changed: got "+sha);

const py=String.raw`
import io,tarfile,json,sys,collections
data=sys.stdin.buffer.read()
cases=[]; totals=collections.Counter(); examples=collections.defaultdict(list)
with tarfile.open(fileobj=io.BytesIO(data),mode="r:gz") as a:
  for m in a:
    if not m.isfile() or not m.name.endswith(".ndjson") or m.size>2000000: continue
    parts=m.name.split("/")
    expected="ACCEPT" if "good" in parts else "REJECT" if "bad" in parts else None
    if expected is None: continue
    text=a.extractfile(m).read().decode("utf-8")
    c=collections.Counter()
    for line in text.splitlines():
      if not line.strip(): continue
      r=json.loads(line)
      if "proj" in r: c["projections"]+=1
      b=r.get("inductive")
      if b is None: continue
      c["bundles"]+=1
      ts=b.get("types",[])
      c["types"]+=len(ts)
      if len(ts)>1: c["mutual"]+=1
      else: c["single"]+=1
      if any((t.get("numNested") or 0)>0 for t in ts): c["nested"]+=1
      if any(t.get("isRec") is True for t in ts): c["recursive"]+=1
      if len(ts)==1 and len(b.get("ctors",[]))==1 and ts[0].get("isRec") is False:
        c["single_ctor_nonrec"]+=1
      if any(t.get("isReflexive") is True for t in ts): c["reflexive"]+=1
    cases.append({"name":m.name,"expected":expected,**c})
    for k,v in c.items():
      totals[k]+=v
      if v and len(examples[k])<20: examples[k].append(m.name)
for key in ["bundles","types","mutual","single","nested","recursive","single_ctor_nonrec","reflexive","projections"]:
  totals["cases_"+key]=sum(1 for c in cases if c.get(key,0)>0)
print(json.dumps({"cases":len(cases),"totals":totals,"examples":examples,
  "mutual_cases":[c for c in cases if c.get("mutual",0)],
  "nested_cases":[c for c in cases if c.get("nested",0)]}))
`;
const out=execFileSync("python3",["-c",py],{input:data,encoding:"utf8",maxBuffer:50000000,timeout:10000});
console.log("MINIMAL_SEMANTIC_KERNEL_CENSUS "+out.trim());
