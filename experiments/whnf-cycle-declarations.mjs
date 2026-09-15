// Diagnostic-only declaration trace for the exact post-2M WHNF cycle.
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";

const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok)throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer()),sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash)throw new Error("Arena corpus changed");

const py=[
"import io,tarfile,json,sys,collections",
"wanted='good/perf/magma-list-pair-n7.ndjson'",
"data=sys.stdin.buffer.read();out={}",
"with tarfile.open(fileobj=io.BytesIO(data),mode='r:gz') as a:",
"  m=next(m for m in a if m.isfile() and '/'.join(m.name.split('/')[-3:])==wanted)",
"  names={0:''};exprs={};decls=[]",
"  for raw in a.extractfile(m).read().decode('utf-8').splitlines():",
"    if not raw.strip():continue",
"    row=json.loads(raw);keys=list(row)",
"    if 'in' in row:",
"      idx=row['in']",
"      if 'str' in row and isinstance(row['str'],dict):",
"        names[idx]=(names.get(row['str'].get('pre'),'')+'.'+row['str'].get('str','')).strip('.')",
"      elif 'num' in row and isinstance(row['num'],dict):",
"        names[idx]=(names.get(row['num'].get('pre'),'')+'.'+str(row['num'].get('i'))).strip('.')",
"    if 'ie' in row:",
"      tag=next((k for k in keys if k not in ('ie','in','il')),None);exprs[row['ie']]=(tag,row.get(tag))",
"    tag=next((k for k in keys if k in ('axiom','def','opaque','thm')),None)",
"    if tag:",
"      v=row[tag]",
"      if isinstance(v,dict) and isinstance(v.get('name'),int):decls.append((tag,names.get(v['name'],'<?>'),v))",
"",
"  targets={'LE.le','LE.mk','instLENat','Nat.le','Nat.succ_le_succ'}",
"  def refs(root):",
"    seen=set();stack=[root];cs=collections.Counter();tags=collections.Counter()",
"    while stack:",
"      i=stack.pop()",
"      if not isinstance(i,int) or i not in exprs or i in seen:continue",
"      seen.add(i);tag,v=exprs[i];tags[tag]+=1",
"      if tag=='const' and isinstance(v,dict):cs[names.get(v.get('name'),'<?>')]+=1",
"      kids=[]",
"      if tag in ('lam','forallE'):kids=[v.get('type'),v.get('body')]",
"      elif tag=='app':kids=[v.get('fn'),v.get('arg')]",
"      elif tag=='letE':kids=[v.get('type'),v.get('value'),v.get('body')]",
"      elif tag=='mdata':kids=[v.get('expr')]",
"      elif tag=='proj':kids=[v.get('struct')]",
"      stack.extend(k for k in kids if isinstance(k,int))",
"    return {'unique':len(seen),'tags':dict(tags),'const_refs':cs.most_common(30)}",
"",
"  for kind,name,v in decls:",
"    if name in targets:",
"      out[name]={'kind':kind,'type':refs(v.get('type')),'value':refs(v.get('value')) if 'value' in v else None,",
"                 'type_root':exprs.get(v.get('type')),'value_root':exprs.get(v.get('value')) if 'value' in v else None}",
"print(json.dumps(out))"
].join("\n");
const out=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:20000}));
console.log("WHNF_CYCLE_DECLARATIONS "+JSON.stringify({arena_sha256:sha,declarations:out}));
