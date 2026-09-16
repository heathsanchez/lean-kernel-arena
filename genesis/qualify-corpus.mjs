import {readFileSync,writeFileSync,mkdirSync,realpathSync} from "node:fs";
import {spawnSync} from "node:child_process";
import {dirname,resolve,relative,isAbsolute} from "node:path";
import {fileURLToPath} from "node:url";
import {createHash} from "node:crypto";
import {PRODUCTION_DEFAULTS,PRODUCTION_ENV} from "./production.mjs";
import {runtimeIdentity} from "./runtime-identity.mjs";

const defaults={manifest:resolve("_build/tests/manifest.json"),output:resolve("genesis/evidence/qualification.json"),
  budget:PRODUCTION_DEFAULTS.semanticBudget,timeout:60_000,inputCap:PRODUCTION_DEFAULTS.inputBytes,
  recordCap:PRODUCTION_DEFAULTS.recordLimit,diagnostic:false};
const options={...defaults},args=process.argv.slice(2);
for(let i=0;i<args.length;i++) {
  const arg=args[i];
  if(arg==="--diagnostic") options.diagnostic=true;
  else if(["--manifest","--output","--budget","--timeout","--input-cap","--record-cap"].includes(arg)) {
    if(i+1===args.length) throw new Error("missing value for "+arg);
    const key={"--manifest":"manifest","--output":"output","--budget":"budget","--timeout":"timeout","--input-cap":"inputCap","--record-cap":"recordCap"}[arg];
    options[key]=key==="manifest"||key==="output"?resolve(args[++i]):Number(args[++i]);
  } else throw new Error("unknown argument: "+arg);
}
for(const key of ["budget","timeout","inputCap","recordCap"]) if(!Number.isSafeInteger(options[key])||options[key]<=0) throw new Error("invalid "+key);
let source,manifestData;
try { manifestData=readFileSync(options.manifest);source=JSON.parse(manifestData); } catch(error) { console.error("manifest: "+String(error?.message??error));process.exit(1); }
const rows=Array.isArray(source)?source:source?.rows;
if(!Array.isArray(rows)||rows.length===0) { console.error("manifest must contain at least one row");process.exit(1); }
const base=realpathSync(dirname(options.manifest));
const worker=fileURLToPath(new URL("./qualify-worker.mjs",import.meta.url));
const runtime=runtimeIdentity();
const results=[];
for(const row of rows) {
  const result={name:row?.name??null,expected:row?.expected??null,bytes:row?.bytes??null,sha256:row?.sha256??null,
    status:null,reason:null,frontier:null,steps:null,elapsed:0,crash:null,timeout:false};
  try {
    if(!row||typeof row.name!=="string"||!row.name||isAbsolute(row.name)||!["ACCEPT","REJECT"].includes(row.expected)||
       !Number.isSafeInteger(row.bytes)||row.bytes<0||typeof row.sha256!=="string"||!/^[0-9a-f]{64}$/.test(row.sha256)) throw new Error("invalid-manifest-row");
    const path=resolve(base,row.name),rel=relative(base,path);
    if(rel===""||rel.startsWith("..")||isAbsolute(rel)) throw new Error("unsafe-path");
    const actual=realpathSync(path),actualRel=relative(base,actual);
    if(actualRel.startsWith("..")||isAbsolute(actualRel)) throw new Error("unsafe-path");
    const childStarted=Date.now();
    const env={...process.env,[PRODUCTION_ENV.semanticBudget]:String(options.budget),
      [PRODUCTION_ENV.inputBytes]:String(options.inputCap),[PRODUCTION_ENV.recordLimit]:String(options.recordCap)};
    const child=spawnSync(process.execPath,[worker,actual,String(row.bytes),row.sha256],
      {encoding:"utf8",timeout:options.timeout,maxBuffer:1024*1024,env});
    result.elapsed=Date.now()-childStarted;
    if(child.error?.code==="ETIMEDOUT"||child.signal) { result.timeout=child.error?.code==="ETIMEDOUT";result.crash=result.timeout?null:(child.signal||"child-signal"); }
    else {
      const lines=child.stdout.trim().split(/\r?\n/).filter(Boolean);
      if(lines.length!==1) throw new Error("invalid-worker-output");
      Object.assign(result,JSON.parse(lines[0]));
      if(child.status!==0&&!result.crash) result.crash="child-exit-"+child.status;
      if(result.runtime_sha256!==runtime.sha256) result.crash="runtime-source-mismatch";
    }
    if(runtimeIdentity().sha256!==runtime.sha256) result.crash="runtime-source-changed";
  } catch(error) { result.crash=String(error?.message??error); }
  results.push(result);
}
const totals={correct:0,wrong:0,unknown:0,errors:0};
for(const row of results) {
  if(row.crash||row.timeout||!["ACCEPT","REJECT","UNKNOWN"].includes(row.status)) totals.errors++;
  else if(row.status==="UNKNOWN") totals.unknown++;
  else if(row.status===row.expected) totals.correct++;
  else totals.wrong++;
}
const passed=totals.wrong===0&&totals.unknown===0&&totals.errors===0;
const report={gate:options.diagnostic?"DIAGNOSTIC":passed?"PASS":"FAIL",strict:!options.diagnostic,
  manifest:options.manifest,budget:options.budget,timeout_ms:options.timeout,input_cap:options.inputCap,record_cap:options.recordCap,
  manifest_sha256:createHash("sha256").update(manifestData).digest("hex"),runtime_revision:runtime.sha256,runtime,totals,rows:results};
mkdirSync(dirname(options.output),{recursive:true});writeFileSync(options.output,JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify({gate:report.gate,totals}));
if(!options.diagnostic&&!passed) process.exitCode=1;
