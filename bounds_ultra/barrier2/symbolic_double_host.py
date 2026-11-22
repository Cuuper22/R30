"""Test the joint *eventual-right SCC* criterion at both genuine B reads
against one marked original source, beyond E24 image membership. A SAT
case supplies a full-duration joint regression; an UNSAT joint case is
split into its distinct actual ancestry implications, not folded into an
all-age claim. T is limited to previously selected symbolic core ages."""
from symbolic_q221_lift import *
from probe import C
from subprocess import run,TimeoutExpired
import os
from concurrent.futures import ThreadPoolExecutor
from functools import lru_cache
@lru_cache(None)
def hosts(name,d,sub):
 from p2_b_recur_host import mature
 ss=[]
 for n,h in((25,58203),(25,24899)):
  if str(h)not in name:continue
  src=Path('/tmp/r30a_bhost_%d_%d.npy'%(n,h))
  if src.exists():S=np.load(src)
  else:
   Z=mature(n);a,b,_=edges(Z,n);G,K,sz=cc(a,b,len(Z));S=Z[K==next(g for g in variable(Z,G,K,sz)if sz[g]==h)]
  if sub>=0:S=S[(S&31)==sub]
  ss.extend(int(s)&((1<<d)-1)for s in S)
 return sorted(set(ss))
def solve(T,u,side,d=25,h='58203/24899',r=30,sub=26,tag=0,k=0,time=100):
 ss=hosts(h,d,sub);ssb=('\n'.join(map(str,ss))+'\n').encode();env=dict(os.environ,PAIR_TAG=str(tag),PAIR_TAGK=str(k))
 a=run(['/tmp/r30b_doublehost',*map(str,(r,T,u,6,side,d,sub))],input=ssb,capture_output=True,check=True,env=env)
 try:b=run([C,'-q'],input=a.stdout,capture_output=True,timeout=time)
 except TimeoutExpired:return 'UNKNOWN'
 if b.returncode==20:return None
 assert b.returncode==10;V={int(s)for w in b.stdout.splitlines()if w.startswith(b'v ')for s in w[2:].split()if int(s)>0};e=sum((p in V)<<j for j,p in enumerate(map(int,a.stderr.split())));z=2*e+1;obs=[];L=set(ss)
 for t in range(u+7):
  if t>=T:assert z>>t&1==(1^((t-u)&1))
  for j in range(2):
   if side>>j&1:
    if t==u-1+6*j:
     assert z>>t&1==0;E=z>>(t+1);assert (E%2**d)in L and(sub<0 or E%32==sub);obs.append(hex(E%2**25))
    if t==u+6*j:assert z>>(t+1)&15==11 and z>>(t-3)&3==1
  z=(4*z)^((z|2*z)if r==30 else z)
 return hex(e),obs
def test(a):
 z=solve(*a);print(a,z,flush=True)
if __name__=='__main__':
 tasks=[(T,u,s,25,'58203/24899',r)for T,u in[(60,60),(120,120)]for s in(1,2,3)for r in(90,30)]
 with ThreadPoolExecutor(3)as ex:list(ex.map(test,tasks))
