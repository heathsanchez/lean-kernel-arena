import {readFileSync} from "node:fs";
import {checkExport} from "./kernel.mjs";
const args=process.argv.slice(2);
let capabilities=[];
if(args.length) {
  if(args.length!==2 || args[0]!=="--state") {
    console.error("usage: node check.mjs [--state retained.json] < export.ndjson");process.exit(3);
  }
  capabilities=JSON.parse(readFileSync(args[1],"utf8"));
  if(!Array.isArray(capabilities)||capabilities.some(x=>typeof x!=="string")) throw new Error("invalid state");
}
const chunks=[];let size=0;
for await(const chunk of process.stdin) {
  size+=chunk.length;
  if(size>2000000) {
    console.log(JSON.stringify({status:"UNKNOWN",reason:"input-budget"}));process.exit(2);
  }
  chunks.push(chunk);
}
const r=checkExport(Buffer.concat(chunks).toString("utf8"),capabilities);
console.log(JSON.stringify(r));
process.exit(r.status==="ACCEPT"?0:r.status==="REJECT"?1:2);
