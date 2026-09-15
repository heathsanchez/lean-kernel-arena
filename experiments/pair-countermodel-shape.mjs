// Diagnostic-only shape analysis of the final countermodel declaration in
// the two magma-list-pair Arena fixtures. No kernel execution is changed.
import {writeFileSync,mkdirSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";

const expectedHash="85942e6f19274699a476d4e5b772abf4bf16f6a719985938bfcb5349ad90d118";
const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok)throw new Error("Arena corpus fetch: "+response.status);
const data=Buffer.from(await response.arrayBuffer()),sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash)throw new Error("Arena corpus changed");

const py=[
"import io,tarfile,json,sys,collections",
"wanted={'good/perf/magma-list-pair-n7.ndjson','good/perf/magma-list-pair-n21.ndjson'}",
"data=sys.stdin.buffer.read();out=[]",
"",
"def analyze_expr(exprs,root):",
"    if root not in exprs:return None",
"    seen=set();stack=[(root,0)];indeg=collections.Counter();tags=collections.Counter();max_depth=0",
"    while stack:",
"        i,d=stack.pop()",
"        if i in seen: continue",
"        seen.add(i);max_depth=max(max_depth,d)",
"        tag,v=exprs[i];tags[tag]+=1;kids=[]",
"        if tag in ('lam','forallE'): kids=[v.get('type'),v.get('body')]",
"        elif tag=='app': kids=[v.get('fn'),v.get('arg')]",
"        elif tag=='letE': kids=[v.get('type'),v.get('value'),v.get('body')]",
"        elif tag=='mdata': kids=[v.get('expr')]",
"        elif tag=='proj': kids=[v.get('struct')]",
"        kids=[k for k in kids if isinstance(k,int) and k in exprs]",
"        for k in kids: indeg[k]+=1;stack.append((k,d+1))",
"    lam=app=letn=0;i=root",
"    while i in exprs and exprs[i][0]=='lam': lam+=1;i=exprs[i][1].get('body')",
"    i=root",
"    while i in exprs and exprs[i][0]=='app': app+=1;i=exprs[i][1].get('fn')",
"    i=root",
"    while i in exprs and exprs[i][0]=='letE': letn+=1;i=exprs[i][1].get('body')",
"    shared=[(n,c,exprs[n][0]) for n,c in indeg.items() if c>1];shared.sort(key=lambda x:x[1],reverse=True)",
"    return {'root_tag':exprs[root][0],'unique_nodes':len(seen),'max_depth':max_depth,'tags':dict(tags),",
"      'root_lambda_spine':lam,'root_app_spine':app,'root_let_spine':letn,'shared_nodes':len(shared),",
"      'max_indegree':max([c for _,c,_ in shared],default=1),",
"      'top_shared':[{'id':n,'indegree':c,'tag':t} for n,c,t in shared[:20]]}",
"",
"with tarfile.open(fileobj=io.BytesIO(data),mode='r:gz') as a:",
"  for m in a:",
"    p='/'.join(m.name.split('/')[-3:])",
"    if not m.isfile() or p not in wanted: continue",
"    names={0:''};exprs={};decls=[]",
"    for raw in a.extractfile(m).read().decode('utf-8').splitlines():",
"      if not raw.strip():continue",
"      row=json.loads(raw);keys=list(row)",
"      if 'in' in row:",
"        idx=row['in']",
"        if 'str' in row and isinstance(row['str'],dict):",
"          pre=names.get(row['str'].get('pre'),'');s=row['str'].get('str','');names[idx]=(pre+'.'+s).strip('.')",
"        elif 'num' in row and isinstance(row['num'],dict):",
"          pre=names.get(row['num'].get('pre'),'');names[idx]=(pre+'.'+str(row['num'].get('i'))).strip('.')",
"      if 'ie' in row:",
"        idx=row['ie'];tag=next((k for k in keys if k not in ('ie','in','il')),None);exprs[idx]=(tag,row.get(tag))",
"      tag=next((k for k in keys if k in ('axiom','def','opaque','thm')),None)",
"      if tag:",
"        v=row[tag]",
"        if isinstance(v,dict) and isinstance(v.get('name'),int): decls.append((tag,names.get(v['name'],'<?>'),v))",
"    targets=[]",
"    for kind,name,v in decls:",
"      if name.endswith('countermodel'):",
"        targets.append({'kind':kind,'name':name,'type':analyze_expr(exprs,v.get('type')),",
"          'value':analyze_expr(exprs,v.get('value')) if 'value' in v else None,'level_params':len(v.get('levelParams',[]))})",
"    out.append({'name':p,'expr_records':len(exprs),'declarations':len(decls),'targets':targets})",
"print(json.dumps(out))"
].join("\n");
const analysis=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50000000,timeout:20000}));
const report={arena_sha256:sha,analysis,claim_boundary:"Diagnostic only; raw export DAG shape for declarations whose resolved name ends with countermodel."};
mkdirSync(new URL("../genesis/evidence/",import.meta.url),{recursive:true});
writeFileSync(new URL("../genesis/evidence/pair-countermodel-shape.json",import.meta.url),JSON.stringify(report,null,2)+"\n");
console.log("PAIR_COUNTERMODEL_SHAPE "+JSON.stringify(report));
