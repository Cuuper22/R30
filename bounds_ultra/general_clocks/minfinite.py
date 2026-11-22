"""If the exact lowest possible marked-west support grows uniformly, this
would exclude every finite west for a fixed host. Compare the true minimum
across all four distinct graphs, not an estimate from their entropy."""
import subprocess,json,sys
from pathlib import Path
root=Path(__file__).resolve().parent
subprocess.run(['g++','-std=c++20','-O3',str(root/'minfinite.cpp'),'-o','/tmp/r30_genp_minfinite'],check=True)
for p,n,k in [('01',25,63),('011',18,42),('0011',18,31),('00101',18,25)]:
 d=json.loads(next(root.glob('dfa_%s_n%d_*.json'%(p,n))).read_text());G=d['adjacency']
 data=' '.join(map(str,(p,k,len(G),len(G[0]))))+'\n'+'\n'.join(' '.join(map(str,r))for r in G)+'\n'
 f=root/('minwest_'+p+'.txt')
 with f.open('w')as out:subprocess.run(['/tmp/r30_genp_minfinite'],input=data,text=True,stdout=out,check=True)
 print(f.read_text().splitlines()[-1],flush=True)
