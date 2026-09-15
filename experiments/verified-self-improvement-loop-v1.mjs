import {readFileSync,writeFileSync} from "node:fs";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import * as K from "../genesis/kernel.mjs";

const ACCEPT="ACCEPT",UNKNOWN="UNKNOWN";
const caps0=JSON.parse(readFileSync(new URL("../genesis/evidence/retained.json",import.meta.url),"utf8"));
const expectedHash="0cdb181ce17bc4f685beea8d3ccb90675ecc029cae9c4dc86629d2adbcb6e8dd";
const fastNames=[
  "good/tutorial/099_ruleK.ndjson",
  "bad/nested-unused-param.ndjson",
  "good/proof-irrel.ndjson",
  "bad/tutorial/101_ruleKAcc.ndjson",
  "bad/proj-of-stuck-prop.ndjson",
  "bad/nat-rec-rules.ndjson",
  "good/perf/folded-constant-first.ndjson",
  "good/tutorial/075_typeSingletonRecReduction.ndjson",
  "bad/tutorial/019_tut06_bad01.ndjson",
  "good/tutorial/111_structEta.ndjson",
  "good/tutorial/125_quotMkType.ndjson",
  "bad/extra-rec.ndjson",
  "good/tutorial/003_arrowType.ndjson"
];

const response=await fetch("https://arena.lean-lang.org/lean-arena-tests.tar.gz",{signal:AbortSignal.timeout(15000)});
if(!response.ok)throw new Error("Arena corpus fetch "+response.status);
const data=Buffer.from(await response.arrayBuffer());
const sha=createHash("sha256").update(data).digest("hex");
if(sha!==expectedHash)throw new Error("Arena corpus changed: got "+sha+" expected "+expectedHash);
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
const rows=JSON.parse(execFileSync("python3",["-c",py],{input:data,maxBuffer:50_000_000,timeout:10_000}));
const byName=new Map(rows.map(r=>[r.name,r]));
const fastRows=fastNames.map(n=>{const r=byName.get(n);if(!r)throw new Error("missing fast separator "+n);return r;});

let caseChecks=0;
function checkRows(caps,rs,budget=1_000_000){
  const out=[];let wrong=0;
  for(const row of rs){
    caseChecks++;
    const r=K.checkExport(row.input,caps,budget);
    const x={name:row.name,expected:row.expected,status:r.status,reason:r.reason??null,steps:r.steps??null};
    out.push(x);
    if(r.status!==UNKNOWN&&r.status!==row.expected)wrong++;
  }
  return {out,wrong};
}
function firstStatusDiff(base,cand){
  for(let i=0;i<base.length;i++)if(base[i].status!==cand[i].status)
    return {name:base[i].name,baseline:base[i].status,candidate:cand[i].status,reason:cand[i].reason};
  return null;
}

// Protected continuation absent from the frozen Arena corpus but present in the
// developmental constitution. It is deliberately independent of the fast Arena
// fingerprint, so Arena-only deletion of string-literals cannot self-authorize.
function stringLiteralProbe(caps){
  caseChecks++;
  const N=JSON.stringify(["[]","str","String"]);
  const meta={meta:{format:{version:"3.1.0"}}};
  const raw=[
    meta,
    {in:1,str:{pre:0,str:"String"}},
    {in:2,str:{pre:0,str:"s"}},
    {il:1,succ:0},
    {ie:0,sort:1},
    {ie:1,const:{name:1,us:[]}},
    {ie:2,strVal:"hello"},
    {axiom:{name:1,levelParams:[],type:0,isUnsafe:false}},
    {def:{name:2,levelParams:[],type:1,value:2,hints:"opaque",safety:"safe",all:[2]}}
  ].map(JSON.stringify).join("\n");
  const r=K.checkExport(raw,caps,1_000_000);
  return {name:"developmental:string-literal",expected:ACCEPT,status:r.status,reason:r.reason??null,steps:r.steps??null};
}

const baselineFull=checkRows(caps0,rows);
if(baselineFull.wrong)throw new Error("baseline wrong verdicts "+baselineFull.wrong);
const baselineFast=fastNames.map(n=>baselineFull.out.find(x=>x.name===n));
const baselineExtra=[stringLiteralProbe(caps0)];
if(baselineExtra[0].status!==ACCEPT)throw new Error("baseline developmental string probe not accepted");

const protectedFull=baselineFull.out.filter(x=>x.status!==UNKNOWN);
function fullPreserves(candidate){
  if(candidate.wrong)return {ok:false,witness:{kind:"wrong-verdict"}};
  for(const b of protectedFull){
    const r=candidate.out.find(x=>x.name===b.name);
    if(!r||r.status!==b.status)return {ok:false,witness:{kind:"authority",name:b.name,baseline:b.status,candidate:r?.status??"MISSING",reason:r?.reason??null}};
  }
  return {ok:true};
}

let state=[...caps0];
const rounds=[];
const knownFastSeparators=new Set(fastNames);
const compiledExtraSeparators=new Set();
const MAX_ROUNDS=4;
for(let round=0;round<MAX_ROUNDS;round++){
  const proposals=state.map(cap=>({kind:"DELETE",cap,caps:state.filter(x=>x!==cap)}));
  const decisions=[];let accepted=null;
  for(const p of proposals){
    // Lane 1: learned fast fingerprint. It may reject, never promote.
    const fast=checkRows(p.caps,fastRows);
    const fd=firstStatusDiff(baselineFast,fast.out);
    if(fast.wrong||fd){
      decisions.push({proposal:p.kind+":"+p.cap,decision:"RETAIN",lane:"fast",witness:fd??{kind:"wrong-verdict"}});
      continue;
    }

    // Lane 2: full frozen Arena authority. A fast-suite miss simply pays for full replay.
    const full=checkRows(p.caps,rows);
    const fp=fullPreserves(full);
    if(!fp.ok){
      decisions.push({proposal:p.kind+":"+p.cap,decision:"RETAIN",lane:"arena-authority",witness:fp.witness});
      continue;
    }

    // Lane 3: non-Arena developmental continuations. No candidate promotes without them.
    const extra=[stringLiteralProbe(p.caps)];
    const ed=baselineExtra[0].status===extra[0].status?null:{
      kind:"developmental",name:extra[0].name,baseline:baselineExtra[0].status,candidate:extra[0].status,reason:extra[0].reason
    };
    if(ed){
      compiledExtraSeparators.add(extra[0].name);
      decisions.push({proposal:p.kind+":"+p.cap,decision:"RETAIN",lane:"extended-authority",witness:ed});
      continue;
    }

    // Conservative v1: only a fully replay-equivalent deletion may change state.
    decisions.push({proposal:p.kind+":"+p.cap,decision:"DELETE",lane:"full-authority"});
    accepted=p;break;
  }
  rounds.push({round,state:[...state],decisions});
  if(!accepted)break;
  state=accepted.caps;
  // Any accepted change forces another backward-dissolution round.
}

const knownCandidateCount=caps0.length;
const naiveChecks=rows.length*(1+knownCandidateCount)+1*(1+knownCandidateCount);
const compiledGate=[...knownFastSeparators,...compiledExtraSeparators];
const everyKnownDeletionSeparated=rounds[0]?.decisions.length===caps0.length &&
  rounds[0].decisions.every(d=>d.decision==="RETAIN");

const report={
  experiment:"verified-self-improvement-loop-v1",
  constitution:{
    rule:"proposal intelligence may self-improve; truth cannot be self-awarded",
    moves:["DELETE","DERIVE","SPLIT","RETAIN","UNKNOWN"],
    promotion:"fast lane may reject only; every survivor owes full authority replay and extended protected continuations"
  },
  arena_sha256:sha,
  initialCapabilities:caps0,
  finalCapabilities:state,
  baselineCounts:baselineFull.out.reduce((m,x)=>(m[x.status]=(m[x.status]??0)+1,m),{}),
  fastSuite:{size:fastNames.length,names:fastNames},
  extendedAuthority:{probes:baselineExtra.map(x=>x.name)},
  rounds,
  compiledNextGate:{
    probes:compiledGate,
    size:compiledGate.length,
    separatesEveryKnownSingleDeletion:everyKnownDeletionSeparated,
    claim_boundary:"This compiled gate is complete only for deletion of one capability from this exact retained basis. Novel rewrites/translators must still replay full authority before promotion."
  },
  economics:{
    actualProtectedCaseChecks:caseChecks,
    naiveFullReplayCaseChecks:naiveChecks,
    reduction:naiveChecks/caseChecks
  },
  status:everyKnownDeletionSeparated?"VERIFIED_LOCAL_FIXED_POINT_AND_FASTER_NEXT_LOOP":"DEVELOPED_STATE_CHANGED",
  security:{
    fastCanPromote:false,
    wrongVerdictPromotion:false,
    unknownPreserved:true,
    stringArenaBlindSpotCaughtByExtendedAuthority:rounds[0]?.decisions.some(d=>d.proposal==="DELETE:string-literals"&&d.lane==="extended-authority")??false
  },
  claim_boundary:"Bounded self-improvement of the development/qualification process. It does not prove unrestricted recursive self-improvement or a globally minimal Lean kernel. The checker semantics are unchanged; only independently verified candidate deletion decisions can alter the retained capability state."
};
writeFileSync("verified-self-improvement-loop-v1.json",JSON.stringify(report,null,2)+"\n");
console.log("VERIFIED_SELF_IMPROVEMENT_LOOP_V1 "+JSON.stringify(report));
