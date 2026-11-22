"""Compile the one live draft against unchanged Statement/Audit and imports.
Both exit codes matter. A zero checker exit is NOT a zero-sorry proof:
read the printed axiom lists. Cache the four current build artifacts.
"""
from pathlib import Path
import tempfile,subprocess,os,shutil
here=Path(__file__).resolve().parent
immutable=here.parent/'immutable'
toolbin=here.parent/'toolchain/lean-4.35.0-linux/bin'
env=os.environ.copy()
if toolbin.is_dir():env['PATH']=f"{toolbin}:{env['PATH']}"
with tempfile.TemporaryDirectory(prefix='rule30-draft-') as td:
 p=Path(td);stack=['Statement','Solution','Audit'];mods={}
 while stack:
  m=stack.pop()
  if m in mods:continue
  src=(here if m=='Solution' else immutable)/(m+'.lean');(p/src.name).symlink_to(src);mods[m]=src
  stack.extend(z for line in src.read_text().splitlines() if line.startswith('import ') for z in line[7:].split() if (immutable/(z+'.lean')).exists())
 (p/'lakefile.toml').write_text('name = "openproblem"\n\n'+'\n'.join('[[lean_lib]]\nname = "'+m+'"\n' for m in mods))
 (p/'lean-toolchain').symlink_to(immutable/'lean-toolchain')
 for cmd in [['lake','build','Solution','Audit'],['lake','env','leanchecker','Solution']]:
  subprocess.run(cmd,cwd=p,env=env,check=True)
  print(' '.join(cmd)+': exit 0',flush=True)
 d=here/'.lake/build/lib/lean';d.mkdir(parents=True,exist_ok=True)
 for m in ('Solution','Audit'):
  for ext in ('olean','ilean'):shutil.copyfile(p/'.lake/build/lib/lean'/f'{m}.{ext}',d/f'{m}.{ext}')
