"""Does the true east grammar sharpen the largest possible rate of short
defects enough to compare with the finite-west deficit? Exact recurrent
cycle mean on the fixed 105-state output DFA, not another right width."""
import json
from pathlib import Path
from fractions import Fraction
import numpy as np
def run():
 S=json.loads(Path(__file__).with_name('symbolic_58203_sofic.json').read_text());r=S['reject'];T=S['shortlong'];g=[(i,v,1-j)for i,t in enumerate(T) if i!=r for j,v in enumerate(t)if v!=r];A,B,F=map(np.array,zip(*g));N=len(T)-1;D=np.zeros((N+1,N),int)
 assert r==N
 for j in range(1,N+1):
  D[j].fill(-100000);np.maximum.at(D[j],B,D[j-1,A]+F)
 v=max(min(Fraction(int(D[N,i]-D[j,i]),N-j)for j in range(N))for i in range(N))
 P=np.zeros(N,int)
 for _ in range(N):np.maximum.at(P,B,P[A]+v.denominator*F-v.numerator)
 assert np.all(v.denominator*F<=v.numerator+P[B]-P[A]);print('max short proportion',v,'potential range',max(P)-min(P),'max pulse/strobe',1/(5-2*v),'max short/strobe',v/(5-2*v))
 st={T[i][0] for i in range(N)}-{r};u=st;seen={};K=[]
 for n in range(500):
  z=tuple(sorted(u))
  if z in seen:print('between shorts: subset period begins',seen[z],n,'admitted long counts before recurrence',K);break
  seen[z]=n
  if any(T[i][0]!=r for i in u):K.append(n)
  u={T[i][1]for i in u}-{r}
if __name__=='__main__':run()
