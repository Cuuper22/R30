"""A true stationary-phase history with opposite possible predecessor inputs
requires an entire non-synchronizing spatial ray (not just ambiguous E34).
Impose its exact finite-tail automaton plus future H. If a bounded horizon
kills it, extract an all-width backwards clock implication. Otherwise give
a genuine finite target realizing the ambiguous cut, and isolate which
future interval evades it."""
from symbolic_q221_lift import *
from probe import C
import subprocess
def trans(y,s):
 a,b=s&1,s>>1;return 2*a+(y^(a|b))
def pair(y,s):return trans(y,s&3)+4*trans(y,s>>2)
def solve(n,d,h,ph=0,lim=70):
 S=gethost(n,d);inputs=('\n'.join(map(str,map(int,S)))+'\n').encode()
 z=subprocess.run(['/tmp/r30b_nonmergehost',str(n),str(h),str(ph)],input=inputs,capture_output=True,check=True)
 try:r=subprocess.run([C,'-q'],input=z.stdout,capture_output=True,timeout=lim)
 except subprocess.TimeoutExpired:return 'UNKNOWN'
 if r.returncode==20:return None
 assert r.returncode==10;K={int(s)for w in r.stdout.splitlines()if w.startswith(b'v ')for s in w[2:].split()if int(s)>0};a=sum((int(p)in K)<<i for i,p in enumerate(z.stderr.split()));H=n+2*h;N={12:''};V=[12]
 for s in V:
  for y in(0,1):
   k=pair(y,s)
   if k not in N:N[k]=N[s]+str(y);V.append(k)
 def read(s):
  for j in reversed(range(H)):s=pair((a>>j)&1,s)
  return s
 # Prior finite/ones c are the low bits of the corresponding final states.
 ta=next(z for s,z in N.items()if read(s)&5==(ph+(4*(1-ph))))
 A=a+(int(ta,2)<<H if ta else 0);m=(1<<n)-1;R=A;D=set(map(int,S))
 for j in range(h+1):
  assert R&m in D
  y=(2*R)^(R|R>>1);R=(2*y+1)^(y|y>>1)
 return hex(A),ta
if __name__=='__main__':
 for h in map(int,sys.argv[1:]):
  for p in(0,1):print('82754 finite target past bit',p,'continuous future strobes',h,solve(34,82754,h,p),flush=True)
