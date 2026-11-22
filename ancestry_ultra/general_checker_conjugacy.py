"""Test the temporal conjugacy on all three mixed drives and independent
R90.  If the spatial west checker basin has a bounded locking time, use
it to classify J(integers) and try replacing the checker with mixed
period backgrounds; otherwise retain the first failing exterior path."""
from general_characteristic_d4 import field

def right(x,r,N):
 z=out=0
 for n in range(N):
  z=((z<<1)|((x>>n)&1))^((z if r==30 else 0)|z>>1)
  out|=(z&1)<<n
 return out

def J(x,r,N):
 m=(1<<N)-1;v=x&m;w=right(x,r,N);j=0
 for d in range(N):
  j|=(v&1<<d)
  v,w=(v^(((v<<1)if r==30 else 0)|(w<<2)))&m,v
 return j

def G(x,r,N):
 return (x^(((x<<1)if r==30 else 0)|(x<<2)))&((1<<N)-1)

def zero_white(r,m=4):
 M=(1<<m)-1;S=set(range(1<<m));st=[len(S)]
 def step(v,c,b):return ((2*v|c)^((v if r==30 else 0)|v>>1|b<<(m-1)))&M
 for t in range(5):
  S={step(step(v,0,a),1,b) for v in S if not v&1 for a in range(2) for b in range(2)}
  st.append(len(S))
 return st

def phase(p,k):return sum(int(p[i%len(p)])<<i for i in range(k))
def chk(j,c,N):return max([d for d in range(N)if(j>>d&1)!=(c^(d&1))]or[-1])+1

def main():
 print('clamped width4 00,10,20,... physical map survivors after each zero-white strobe',zero_white(30),zero_white(90))
 assert zero_white(30)[-1]==0 and zero_white(90)[-1]==16
 for ph in [0,1]:
  A={(a,b)for a in range(2)for b in range(2)};row=[]
  for k in range(5):
   A={(((ph+k)%2)^(a|b),a)for a,b in A};row.append(len(A))
  print('inverse checker scanner uncertainty, first background phase',ph,row)
  assert len(A)==1
 for p in ('01','011','00101'):
  for r in(30,90):
   at=field(r,p,500);C=sum(at(t,0)<<t for t in range(501))
   # J reads right-vacuum-initialized fields. R30 singleton must return
   # the one-point spatial seed. The R90 sample genuinely requires a
   # different east half: its J is NOT falsely expected to recover it.
   j=J(C,r,501);h=right(C,r,501)
   if r==30:assert j==1
   assert J(h,r,501)==G(j,r,501)
   print('actual same-pattern control rule,w,500-tick J nonzero digits',r,p,j.bit_count())
  # Exact causal finite shadow: mixed w to K, then either constant.
  # 8K+12 is a proved sufficient west-vacuum scan depth for this check.
  K=49;N=8*K+20;A=phase(p,K);B=A-(1<<K)
  ck=[chk(J(x,30,N),int(x<0),N)for x in(A,B)]
  assert max(ck)<=8*K
  print('finite mixed-prefix opposite checker completions',p,K,ck)
  # For actual singleton, the finite temporal prefix has left seed
  # exactly 00...001 through K. Outside, both checker phases occur.
  at=field(30,None,500);A=sum(at(t,0)<<t for t in range(K))
  for x in (A,A-2**K):
   j=J(x,30,N);assert j%(1<<K)==1 and chk(j,int(x<0),N)<=8*K
 # The actual R90 singleton has temporal u=1 and J90(1)=1, not checker.
 assert J(1,90,501)==1
 print('R90 true singleton finite temporal profile J(1) has 500 further west zeros')
if __name__=='__main__':main()
