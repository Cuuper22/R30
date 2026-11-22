"""Period-blind test: can one genuine marked R90 orbit realize each
clamped center clock from a finite west, even when its own q has zero
entropy? Build the uniquely implied eventually periodic *spatial* east
source, simulate the true unconstrained CA and compare the white reads."""
from math import gcd
def mul(a,b):
 v=0
 while b:
  if b&1:v^=a
  a<<=1;b>>=1
 return v
def pw(a,b):
 c=1
 while b:
  if b&1:c=mul(c,a)
  a=mul(a,a);b>>=1
 return c
def divmodp(a,b):
 q=0
 while a.bit_length()>=b.bit_length():
  s=a.bit_length()-b.bit_length();a^=b<<s;q^=1<<s
 return q,a
def gc(a,b):
 while b:a,b=b,divmodp(a,b)[1]
 return a
def series(num,den,N):
 out=0;assert den&1
 for j in range(N):
  if num>>j&1:out|=1<<j;num^=den<<j
 return out
def r90(pat,N=500):
 P=len(pat);q=sum(int(c)<<j for j,c in enumerate(pat));den=1+(1<<P);num=den^(q<<1)
 # C=1+z*q(z)/(1+z^P), S=C(x/(1+x²)); homogenize the denominator.
 k=max(num,den).bit_length()-1
 def sub(a):return __import__('functools').reduce(int.__xor__,(pw(5,k-i)<<i for i in range(k+1)if a>>i&1),0)
 a,b=sub(num),sub(den);g=gc(a,b);a=divmodp(a,g)[0];b=divmodp(b,g)[0]
 x=series(a,b,N+4);off=N+4;v=x<<off;C=[1]+[int(pat[t%P]) for t in range(N+4)];R=[]
 for t in range(N+1):
  assert (v>>off)&1==C[t]
  r=(v>>(off+1))&1;expect=C[t+1];j=2
  while j-1<=t:expect^=C[t-(j-1)];j*=2
  assert r==expect;R.append(r);v=2*v^(v>>1)
 # period of denominator reciprocal; quotient affects only finite prefix.
 deg=b.bit_length()-1;per=1;mod=divmodp(2,b)[1]
 if b!=1:
  while mod!=1:mod=divmodp(mod<<1,b)[1];per+=1
 print('R90 P',pat,'unclamped checked',len(R),'finite-west original mark; east GF2 num/den',hex(a),hex(b),'eventual spatial period',per,'first 20 x1 physical', ''.join(map(str,R[:20])),flush=True)
 return C,R
if __name__=='__main__':
 for pat in ('01','011','00101','0011'):r90(pat)
