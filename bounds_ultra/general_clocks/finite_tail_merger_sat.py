"""A finite prefix plus an explicitly periodic *infinite* initial tail in
each donor. Find genuine full-ray mergers preserving a prescribed past
center under both histories, with opposite white reads immediately before
equality. This is a two-history fiber problem, not a singleton-onset SAT scan.
Replay every SAT answer on canonical eventually periodic rays.
"""
from pathlib import Path
import subprocess,itertools,sys
from infinite_east_fibers import canon,bit,F
SOL=str(Path(__file__).resolve().parents[2]/'toolchain/lean-4.35.0-linux/bin/cadical')
def sat(p,ph,K,d,m,low,sec=18):
 C=list(int(p[(ph-K+1+j)%len(p)])for j in range(K));C.append(int(p[(ph+1)%len(p)]));V={};cla=[]
 def v(a,t,x):
  if x==0:return bool(C[t])
  start=d+t+1
  if x>=start:x=start+(x-start)%m
  key=(a,t,x)
  if key not in V:V[key]=len(V)+1
  return V[key]
 def n(x):return not x if type(x)==bool else -x
 def cl(L):
  if any(type(i)==bool and i for i in L):return
  s=set(i for i in L if type(i)!=bool)
  if any(-i in s for i in s):return
  cla.append(' '.join(map(str,s))+' 0\n')
 def eq(x,y):cl([n(x),y]);cl([x,n(y)])
 for a in(0,1):
  for t in range(K):
   for x in range(1,d+t+m+2):
    k,l,h,z=v(a,t,x-1),v(a,t,x),v(a,t,x+1),v(a,t+1,x)
    for A,B,H in itertools.product((0,1),repeat=3):
     want=A^(B|H);cl([n(k)if A else k,n(l)if B else l,n(h)if H else h,z if want else n(z)])
 for x in range(1,d+K+m+1):
  eq(v(0,K,x),v(1,K,x))
  if low is not None and x<=20:cl([v(0,K,x)if low>>(x-1)&1 else n(v(0,K,x))])
  # immediately different old donors share neither a black nor a pair of
  # common whites anywhere to the right (east pair would decode both equal).
  cl([n(v(0,K-1,x)),n(v(1,K-1,x))])
  cl([v(0,K-1,x),v(1,K-1,x),v(0,K-1,x+1),v(1,K-1,x+1)])
 cl([v(0,K-1,1)]);cl([n(v(1,K-1,1))])
 s='p cnf %d %d\n'%(len(V),len(cla))+''.join(cla)
 try:r=subprocess.run([SOL,'-q'],input=s,stdout=subprocess.PIPE,text=True,timeout=sec)
 except subprocess.TimeoutExpired:return 'unknown'
 if r.returncode==20:return 'UNSAT for d,m only'
 assert r.returncode==10,r.stdout[:50]
 X={int(j)for l in r.stdout.splitlines()if l.startswith('v ')for j in l[2:].split()if int(j)>0}
 A=[canon(tuple(int(v(a,0,x)in X) for x in range(1,d+1)),tuple(int(v(a,0,x)in X)for x in range(d+1,d+m+1)))for a in(0,1)]
 C0=A.copy();head=[]
 for t in range(K):
  head.append(tuple(bit(z) for z in A));A=[F(z,30,C[t])for z in A]
 assert head[-1]==(1,0) and A[0]==A[1]
 return 'SAT initial rays/true shared landing',[(hex(sum(b<<j for j,b in enumerate(B))),len(B),''.join(map(str,R)))for B,R in C0],(len(A[0][0]),''.join(map(str,A[0][1])))
if __name__=='__main__':
 p,ph,k,d,m,low=sys.argv[1:7];print(p,ph,k,d,m,low,sat(p,int(ph),int(k),int(d),int(m),int(low,16)if low!='-'else None,int(sys.argv[7])if len(sys.argv)>7 else 18),flush=True)
