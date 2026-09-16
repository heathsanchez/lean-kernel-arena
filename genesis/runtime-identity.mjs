import {readFileSync} from "node:fs";
import {createHash} from "node:crypto";
import {dirname,relative} from "node:path";
import {fileURLToPath,pathToFileURL} from "node:url";

function sha256(data) { return createHash("sha256").update(data).digest("hex"); }
function runtimeIdentity(entry=new URL("./production.mjs",import.meta.url)) {
  const root=dirname(fileURLToPath(entry)),pending=[entry],seen=new Set(),files=[];
  while(pending.length) {
    const url=pending.pop(),path=fileURLToPath(url);
    if(seen.has(path)) continue;
    seen.add(path);
    const data=readFileSync(path),source=data.toString("utf8");
    files.push({path:relative(root,path)||"production.mjs",bytes:data.length,sha256:sha256(data)});
    const pattern=/(?:import\s+(?:[^"']*?\s+from\s+)?|export\s+[^"']*?\s+from\s+)["'](\.[^"']+)["']/g;
    for(const match of source.matchAll(pattern)) pending.push(new URL(match[1],pathToFileURL(path)));
  }
  files.sort((a,b)=>a.path.localeCompare(b.path));
  return {sha256:sha256(files.map(file=>`${file.path}\0${file.bytes}\0${file.sha256}\n`).join("")),files};
}

export {sha256,runtimeIdentity};
