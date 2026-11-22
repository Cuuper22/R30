"""A universal strict bound for the *spatial* entropy of mature right
prefixes, by an adaptive past-center decoder. Compute the exact finite
grammar and compare all required true R30/R90 mature spatial counts.
This is independent of temporal white-mask deficit."""
from collections import deque
import numpy as np
from pathlib import Path
def trans(S,z,rule):
 out=0
 for h in range(4):
  if S>>h&1:
   a=h>>1;b=h&1;r=(b<<1)|(z^((a|b)if rule==30 else a));out|=1<<r
 return out
def autom(rule):
 st=[15];ID={15:0};edges=[]
 for S in st:
  dest=[]
  if S==0:dest=[15] # one prescribed independent center bit
  else:
   for b in (0,1):
    s=trans(S,b,rule);dest.append(0 if s.bit_count()==1 else s)
  L=[]
  for v in dest:
   if v not in ID:ID[v]=len(st);st.append(v)
   L.append(ID[v])
  edges.append(L)
 M=np.zeros((len(st),len(st)),dtype=int)
 for i,r in enumerate(edges):
  for j in r:M[i,j]+=1
 return st,edges,M
def run(rule):
 st,edges,M=autom(rule);wr=np.linalg.eigvals(M).real;rho=max(wr);print('rule',rule,'states',st,'edges',edges,'rho',rho,'h_spatial_upper',np.log2(rho))
 import sympy
 print('characteristic polynomial',sympy.factor(sympy.Matrix(M).charpoly().as_expr()))
 w=[1]*len(st);counts=[1]
 for n in range(1,101):
  w=[sum(w[t]for t in z)for z in edges];counts.append(w[0])
 print('universal M_n upper n=8,12,16,18,20,22,30,40,100',[counts[n]for n in (8,12,16,18,20,22,30,40,100)])
 return counts
if __name__=='__main__':
 C=run(30);B=run(90);assert all(B[n]==1<<n for n in range(101))
 for s in Path(__file__).with_name('spatial.txt').read_text().splitlines():
  z=s.split();p=z[1];n=int(z[2]);v=int(z[6]);assert v<=C[n]
 print('all required 24 Rule30 width/pattern counts within bound, matched Rule90 full at each width')
