"""Check the EXACT free-past, west-marked finite-predecessor condition on
the existing terminal horizons. If many candidates survive the entire
source history use their missing genuine eastern ancestry; otherwise
record the high-rim rejection and build a uniform correlated criterion."""
from pathlib import Path
import subprocess,json,sys
from collections import Counter
path=Path(__file__).resolve().parents[1]/'bounds_ultra/general_clocks'
cs=Path('/tmp/r30_anc_host_w.cpp')
s=(path/'minfinite.cpp').read_text()
i=s.index(' if(i){Min &b=');j=s.index(' if(i==K)return;',i)
s=s[:i]+''' if(i==K){std::cout<<hex(decode(H,i*P))<<"\\n";return;}
'''+s[j:]
i=s.index(' for(int i=1;i<=K;i++){auto& a=D[i]');s=s[:i]+'}\n'
cs.write_text(s);exe='/tmp/r30_anc_host_w'
subprocess.run(['g++','-std=c++20','-O3',str(cs),'-o',exe],check=True)
def rev(x,k):return int(format(x,'0%db'%k)[::-1],2)
def step(a,b):return a//2^(a|2*a|b)
def nxt(S):
 z=set()
 for a,b in S:
  y=step(a,b)
  if b:z.add((y,1-a%2))
  else:z.add((y,0));z.add((y,1))
 return z
def horizons(p,n,k):
 G=json.loads(next(path.glob('dfa_%s_n%d_*.json'%(p,n))).read_text())['adjacency']
 data=' '.join(map(str,(p,k,len(G),len(G[0]))))+'\n'+'\n'.join(' '.join(map(str,r))for r in G)+'\n'
 return [int(z,16)for z in subprocess.run([exe],input=data,capture_output=True,text=True,check=True).stdout.split()]
def invfinite(w,a,b):
 while w:a,b=b,(w&1)^(a|b);w//=2
 return (a,b)==(0,0)
def analyze(lanes=(8,16,24,32,48,64)):
 Lmax=max(lanes);front={(0,1)};R={}
 for t in range(1,Lmax+1):
  front=nxt(front)
  if t in lanes:
   # Store the whole rim at its first complete age. Beyond that, the
   # steep western edge propagates autonomously independently of input.
   mask=(1<<t)-1;B={rev(w,t)for w,c in front};S={}
   for j in range(t,128):
    S[j]={rev(b,t)for b in B};B={(4*b^(2*b|b))&mask for b in B}
   R[t]=S
 for p,n,k in [('01',25,63),('011',18,42),('0011',18,31),('00101',18,25)]:
  Z=horizons(p,n,k);W=Z;w=min(W)
  print(p,'existing terminal horizon',len(p)*k,'m(k) inverse finite count',sum(invfinite(w,s//2,s%2)for s in range(4)), 'distinct west residues',len(W),flush=True)
  for L in lanes:
   W=[v for v in W if (j:=v.bit_length())<L or v>>(j-L)in R[L][j]]
   print('remaining finite width<=H with exact marked-west high depth',L,len(W),flush=True)
   if not W:break
  # A full forward comparison at the implied age would be needed only
  # for survivors of every rim projection above.
  if W:
   B=set(W);S={(0,1)};hits=[]
   for age in range(max(x.bit_length()for x in W)+1):
    hits.extend(z for z in B if z.bit_length()==age and (z,int(p[0]))in S)
    S=nxt(S)
   print('exact full-west-source hits',hits,flush=True)
if __name__=='__main__':analyze()
