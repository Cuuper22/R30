"""The right-host entropy is an upper model. Test whether a genuine clamped
finite east already forces the marked-island bound to fail, or admits a
long low-complexity word that defeats inferring an island from positive
host entropy. Compare literal observed factors, without frequency guess."""
from pathlib import Path
import json
import r30fast,numpy as np
def test(p,n,zs,N=8192):
 m,H,S=r30fast.general_p_hosts(p,n=n,rule=30,return_states=True);read={}
 for h in H:
  if h.size>1:
   for s in np.frombuffer(S[h.comp_id],dtype=np.uint64):read[int(s)]=(h.size,h.absorbing)
 mask=(1<<n)-1;P=len(p)
 for r in (0,1,11):
  v=r;atoms=[];host0=0;hst=None;states=[]
  for i in range(N):
   h=read.get(mask&v)
   if h!=hst:host0=i;hst=h
   l=0
   for c in p:
    if c=='0':l=2*l+(v&1)
    v=(2*v+int(c))^(v|(v>>1))
   atoms.append(l)
  aq=atoms[host0+1:];counts=[len(set(tuple(aq[i:i+k])for i in range(len(aq)-k+1)))for k in (4,8,16,24,32,64)];zz=[]
  for z in zs:
   best=(0,0);zzs=tuple(z)
   for j in range(len(z)):
    run=0
    for i,b in enumerate(aq):
     run=(run+1)if b==zzs[(i+j)%len(z)]else 0
     if run>best[0]:best=(run,i-run+1+host0+1)
   zz.append(best)
  print(p,'width',n,'strict east seed',r,'terminal host/entered at strobe',hst,host0,'factors 4,8,16,24,32,64',counts,'longest selected periodic matching strobes/start',zz,flush=True)
if __name__=='__main__':
 for p,z in [('01',[(0,1,0,0,0)]),('011',[(0,1,1)]),('0011',[(1,),(3,),(1,1,1,1,1,3,3)]),('00101',[(0,)])]:test(p,18,z)
