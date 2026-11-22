"""Check whether finite right tapes surviving the q-variable E25 host 24899
are really in a robust q-periodic subbasin at a larger actual width.
A closed periodic SCC gives a genuine finite-east attractor and must be
discounted in the finite-west obstruction; a surviving q-variable actual
tape is retained for the shared-origin test."""
from symbolic_q221_lift import *
def run(n=31,sz0=203375):
 S=gethost(n-1,sz0);V=np.sort(np.concatenate((S,S+(1<<(n-1)))));a,b,h=edges(V,n);G,C,sz=cc(a,b,len(V));qq=set(variable(V,G,C,sz));sets=[]
 for j in np.flatnonzero(sz>1):
  k=int(sz[j]);entr=(C[a]==j);inside=entr&(C[b]==j);nint=int(np.sum(inside));its=set(map(int,V[C==j]));sets.append((k,its));print('scc',k,'q-variable',j in qq,'missing full physical exits',k*4-nint,flush=True)
 M=(1<<n)-1;d25=set(map(int,gethost(25,24899)))
 for r0 in(0x1727,0x5a0e,0x1388,0xa07,0xc48,16398,64423):
  r=r0;qv=[];hits=[];last=None
  for i in range(8000):
   lab=next((k for k,cs in sets if (r&M)in cs),0) if r%2**25 in d25 else -1
   if lab!=last:hits.append((i,lab));last=lab
   qv.append(r&1);y=(2*r)^(r|r>>1);r=(2*y+1)^(y|y>>1)
   if lab==-1 and i<7990:break
  if len(qv)>1000:
   z=qv[-700:];p=next((p for p in range(1,300)if z[p:]==z[:-p]),None)
  else:p=None
  print(hex(r0),'ticks',i,'E31 host transitions',hits[:3],hits[-3:],'q last700 period',p,flush=True)
if __name__=='__main__':run()
