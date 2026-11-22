"""Compare the P=2 landmark host with the period-blind temporal DFA
computations at width18. Expand the prior certified tile readout into
its physical white-q chronology, and count DISTINCT q words."""
import json
from pathlib import Path
from collections import defaultdict
from math import log2
import numpy as np
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import eigs
def go():
 s=json.loads((Path(__file__).parents[1]/'barrier2/symbolic_58203_sofic.json').read_text());T=s['shortlong'];N=s['reject'];assert N==len(T)-1;E=defaultdict(list);v=N
 for i in range(N):
  for j,w in enumerate(('010','01000')):
   t=T[i][j]
   if t==N:continue
   start=i
   for k,a in enumerate(w):
    end=t if k+1==len(w) else v
    if end==v:v+=1
    E[start].append((int(a),end));start=end
 # All starts accepted, arbitrary q-factor at any white phase.
 X=[tuple(range(v))];M={X[0]:0};A=[]
 for S in X:
  tr=[]
  for ch in (0,1):
   U=tuple(sorted({t for i in S for c,t in E[i] if c==ch}))
   if U and U not in M:M[U]=len(X);X.append(U)
   tr.append(M[U] if U else -1)
  A.append(tr)
 wave={0:1};fc=[]
 for i in range(31):
  D=defaultdict(int)
  for x,u in wave.items():
   for y in A[x]:
    if y>=0:D[y]+=u
  wave=D;fc.append(sum(D.values()))
 ii,jj=zip(*[(i,j)for i,o in enumerate(A)for j in o if j>=0]);G=coo_matrix((np.ones(len(ii)),(ii,jj)),shape=(len(A),len(A))).tocsr();e=float(np.real(eigs(G,k=1,which='LR',return_eigenvectors=False)[0]))
 print('01 width25 58203 DFA',len(A),'31 counts',fc,'PF',e,'bits/strobe',log2(e),'bits/physical tick',log2(e)/2)
 Path(__file__).with_name('dfa_01_n25_58203.json').write_text(json.dumps(dict(p='01',host=58203,n=25,complete=True,alphabet=2,factors=fc,adjacency=A)))
if __name__=='__main__':go()
