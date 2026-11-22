"""Capture only opted-in Rule 30 research folders for an incremental checkpoint."""
import hashlib
import json
import re
import sys
import tempfile
from pathlib import Path

root = Path(__file__).resolve().parents[1]
scope = sys.argv[1]
scopes = {"ancestry": ("ancestry_ultra",), "bounds": ("bounds_ultra",), "shared": ("step4", "immutable")}
if scope not in scopes:
    raise SystemExit("unknown checkpoint scope")
temp = Path(tempfile.mkdtemp(prefix=f"r30-checkpoint-{scope}-"))
credential = re.compile(
    rb"-----BEGIN (?:OPENSSH |RSA |EC |DSA )?PRIVATE KEY-----|(?:ghp_|gho_|ghs_|github_pat_|sk-(?:proj-|ant-))[A-Za-z0-9_-]{18,}|(?:AKIA|ASIA)[A-Z0-9]{16}|(?:Authorization:\s*Bearer\s+)[A-Za-z0-9_.-]{20,}",
    re.I,
)
blocked = {".git", ".codex", ".agents", ".aws", ".ssh", ".env"}
baseline = Path("/tmp/r30_sync_snapshot")
files, excluded = {}, []
def capture(p, rel):
    k = rel.as_posix()
    if (set(rel.parts) & blocked or p.is_symlink() or not p.is_file()
        or re.search(r"(^|[._-])(credential|secrets?|auth\.json)([._-]|$)", p.name, re.I)):
        return
    try:
        raw = p.read_bytes()
    except FileNotFoundError:
        return
    if credential.search(raw):
        excluded.append(k)
        return
    h = hashlib.sha1(f"blob {len(raw)}\0".encode() + raw).hexdigest()
    old = baseline / rel
    base = None
    if old.is_file():
        x = old.read_bytes()
        base = hashlib.sha1(f"blob {len(x)}\0".encode()+x).hexdigest()
    if len(raw) > 2400000:
        if h != base:
            excluded.append(k + " (needs archive sharding)")
        return
    (temp / h).write_bytes(raw)
    files[k] = {"sha": h, "base": base, "size": len(raw)}
for d in scopes[scope]:
    for f in (root / d).rglob("*"):
        capture(f, f.relative_to(root))
if scope != "shared":
    for f in Path("/tmp").iterdir():
        if f.name.startswith("r30" + ("a" if scope == "ancestry" else "b") + "_") and f.suffix in {".log", ".txt", ".npy", ".json", ".csv"}:
            capture(f, Path("runtime-evidence") / f.name)
print(json.dumps({"staging": str(temp), "files": files, "excluded": excluded}))
