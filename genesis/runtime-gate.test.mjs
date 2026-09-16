import assert from "node:assert/strict";
import {mkdtempSync,writeFileSync,readFileSync,mkdirSync} from "node:fs";
import {tmpdir} from "node:os";
import {join,resolve} from "node:path";
import {spawnSync} from "node:child_process";
import {createHash} from "node:crypto";
import {fileURLToPath} from "node:url";
import {CAPABILITIES,PRODUCTION_ENV,checkExport} from "./production.mjs";

const root=resolve(fileURLToPath(new URL("..",import.meta.url)));
const main=join(root,"checkers/mathgraph/main.mjs"),qualify=join(root,"genesis/qualify-corpus.mjs");
const dir=mkdtempSync(join(tmpdir(),"lean-kernel-gate-"));
const good=readFileSync(join(root,"tests/sparse-name-index.ndjson"),"utf8");
const meta=JSON.stringify({meta:{format:{version:"3.1.0"}}});
const bad=[meta,JSON.stringify({in:1,str:{pre:0,str:"bad"}}),JSON.stringify({ie:0,sort:0}),
  JSON.stringify({ie:1,bvar:0}),JSON.stringify({ie:2,lam:{name:0,type:0,body:1,binderInfo:"default"}}),
  JSON.stringify({axiom:{name:1,type:2,levelParams:[],isUnsafe:false}})].join("\n");
const unsupported=meta+"\n"+JSON.stringify({quot:{}});
for(const [name,input,code] of [["good",good,0],["bad",bad,1],["unsupported",unsupported,2]]) {
  const path=join(dir,name+".ndjson");writeFileSync(path,input);
  const cli=spawnSync(process.execPath,[main,path],{encoding:"utf8"});
  assert.equal(cli.status,code,name+" CLI exit");
  assert.ok(CAPABILITIES.length>0);
  assert.equal(["ACCEPT","REJECT","UNKNOWN"][code],checkExport(input).status,name+" production parity");
}
function row(name,expected,input) {
  writeFileSync(join(dir,name),input);
  return {name,expected,bytes:Buffer.byteLength(input),sha256:createHash("sha256").update(input).digest("hex")};
}
const run=(manifest,...args)=>spawnSync(process.execPath,[qualify,"--manifest",manifest,"--output",join(dir,"report.json"),...args],{encoding:"utf8",timeout:10000});
const manifest=join(dir,"manifest.json");
writeFileSync(manifest,JSON.stringify([row("good.ndjson","ACCEPT",good),row("bad.ndjson","REJECT",bad)]));
let result=run(manifest);assert.equal(result.status,0,result.stderr);let report=JSON.parse(readFileSync(join(dir,"report.json")));
assert.deepEqual(report.totals,{correct:2,wrong:0,unknown:0,errors:0});
assert.match(report.manifest_sha256,/^[0-9a-f]{64}$/);assert.match(report.runtime.sha256,/^[0-9a-f]{64}$/);
assert.ok(report.runtime.files.some(file=>file.path==="production.mjs"));
assert.ok(report.rows.every(row=>row.runtime_sha256===report.runtime.sha256));
const large=good+"\n"+" ".repeat(2_100_000),largeRow=row("large.ndjson","ACCEPT",large);
writeFileSync(manifest,JSON.stringify([largeRow]));
const largeMain=spawnSync(process.execPath,[main,join(dir,"large.ndjson")],{encoding:"utf8"});
result=run(manifest);report=JSON.parse(readFileSync(join(dir,"report.json")));
assert.equal(largeMain.status,0,"packaged main accepts valid input above 2MB");
assert.equal(result.status,0,result.stderr);assert.equal(report.rows[0].status,"ACCEPT","worker agrees above 2MB");
const lowEnv={...process.env,[PRODUCTION_ENV.semanticBudget]:"1"};
const lowMain=spawnSync(process.execPath,[main,join(dir,"good.ndjson")],{encoding:"utf8",env:lowEnv});
writeFileSync(manifest,JSON.stringify([row("good.ndjson","ACCEPT",good)]));
result=run(manifest,"--budget","1");report=JSON.parse(readFileSync(join(dir,"report.json")));
assert.equal(lowMain.status,2,"packaged main honors semantic budget env");
assert.equal(result.status,1);assert.equal(report.rows[0].status,"UNKNOWN","worker honors runner budget override");
writeFileSync(manifest,JSON.stringify([row("wrong.ndjson","REJECT",good)]));
result=run(manifest);assert.equal(result.status,1);report=JSON.parse(readFileSync(join(dir,"report.json")));assert.equal(report.totals.wrong,1);
writeFileSync(manifest,JSON.stringify([row("unknown.ndjson","ACCEPT",unsupported)]));
result=run(manifest);assert.equal(result.status,1);report=JSON.parse(readFileSync(join(dir,"report.json")));assert.equal(report.totals.unknown,1);
result=run(manifest,"--diagnostic");assert.equal(result.status,0);report=JSON.parse(readFileSync(join(dir,"report.json")));assert.equal(report.gate,"DIAGNOSTIC");
writeFileSync(manifest,"[]");assert.notEqual(run(manifest).status,0,"empty manifest must fail");
writeFileSync(manifest,JSON.stringify([{name:"../escape.ndjson",expected:"ACCEPT",bytes:0,sha256:"0".repeat(64)}]));
assert.notEqual(run(manifest).status,0,"unsafe path must fail");
console.log("RUNTIME_GATE_PASS");
