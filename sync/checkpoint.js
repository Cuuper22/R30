// Run in an async functions.exec wrapper with scope = ancestry, bounds, or shared.
// This is a no-force fast-forward integration of files owned by one scope.
// The initial immutable archive is the base for files not published individually.
const allowed = new Set(["ancestry", "bounds", "shared"]);
if (!allowed.has(scope)) throw Error("unknown checkpoint scope");
const repo = "Cuuper22/R30";
const dir = "rule30_target/sync";
const stat = await tools.mcp__codex_apps__github_get_repo({repository_full_name: repo});
if (stat.structuredContent?.id !== "1467162572" || stat.structuredContent?.visibility !== "public" || !stat.structuredContent?.permissions?.push)
  throw Error("refusing to sync: expected the confirmed public R30 repository with push access");
const local = await tools.exec_command({cmd:`python '${dir}/snapshot_worker.py' ${scope}`,max_output_tokens:100000});
if (local.exit_code !== 0) throw Error(local.output);
const shot = JSON.parse(local.output);
const basefile = `checkpoints/${scope}-latest.json`;
const stage = shot.staging;
if (!/^\/tmp\/r30-checkpoint-(ancestry|bounds|shared)-[a-z0-9_]+$/.test(stage)) throw Error("unsafe staging path");
const req = (r,k) => { const h = r.structuredContent?.[k]; if (!h) throw Error(JSON.stringify(r.structuredContent ?? r.content).slice(0,1000)); return h; };
const blob = async (d) => {
  const chunks = [];
  for (let i=0;i*262143<d.size;i++) {
    const r = await tools.exec_command({cmd:`dd if=${stage}/${d.sha} bs=262143 skip=${i} count=1 status=none | base64 -w0`,max_output_tokens:160000});
    const b = r.output.trim();
    if(r.exit_code || b.length!==4*Math.ceil(Math.min(262143,d.size-i*262143)/3) || !/^[A-Za-z0-9+/]+={0,2}$/.test(b))throw Error("invalid artifact bytes");
    chunks.push(b);
  }
  const sha = req(await tools.mcp__codex_apps__github_create_blob({repository_full_name:repo,encoding:"base64",content:chunks.join("")}),"sha");
  if (sha!==d.sha) throw Error("artifact verification failed");
  return sha;
};
let answer;
const seen=new Set();
try {
  for (let attempt=0;attempt<4;attempt++) {
    const head=req(await tools.mcp__codex_apps__github_fetch_commit({repo_full_name:repo,commit_sha:"main"}),"commit").sha;
    const prev=await tools.mcp__codex_apps__github_fetch_file({repository_full_name:repo,path:basefile,ref:head});
    if (prev.isError && !JSON.stringify(prev.structuredContent??prev.content).match(/404|NOT_FOUND|Not Found/i)) throw Error("cannot read checkpoint manifest");
    const old=prev.structuredContent?.content?JSON.parse(prev.structuredContent.content):{};
    const current={...old};
    const entries=[];
    const dirty=Object.entries(shot.files).filter(([p,d])=>(old[p]??d.base)!==d.sha);
    // No file deletion or force updates.
    for(let i=0;i<dirty.length;i+=3) await Promise.all(dirty.slice(i,i+3).map(async ([p,d])=>{
      if (!seen.has(d.sha)){await blob(d);seen.add(d.sha);}
      current[p]=d.sha; entries.push({path:p,mode:"100644",type:"blob",sha:d.sha});
    }));
    if(!entries.length){answer={scope,changed:0,head,excluded:shot.excluded};break;}
    entries.push({path:basefile,mode:"100644",type:"blob",content:JSON.stringify(current,null,2)+"\n"});
    const newTree=req(await tools.mcp__codex_apps__github_create_tree({repository_full_name:repo,base_tree_sha:head,tree_elements:entries}),"sha");
    const commit=req(await tools.mcp__codex_apps__github_create_commit({repository_full_name:repo,tree_sha:newTree,parent_sha:head,message:`Sync ${scope} Rule 30 checkpoint`}),"sha");
    const update=await tools.mcp__codex_apps__github_update_ref({repository_full_name:repo,branch_name:"main",sha:commit,expected_sha:head,force:false});
    if(update.structuredContent?.success){answer={scope,changed:dirty.length,commit,excluded:shot.excluded};break;}
    const newer=req(await tools.mcp__codex_apps__github_fetch_commit({repo_full_name:repo,commit_sha:"main"}),"commit").sha;
    if(newer===head)throw Error(JSON.stringify(update.structuredContent??update.content).slice(0,1000));
  }
  if(!answer)throw Error("main changed repeatedly; checkpoint remains in the local workspace for retry");
  text(answer);
} finally {
  await tools.exec_command({cmd:`rm -r -- '${stage}'`});
}
