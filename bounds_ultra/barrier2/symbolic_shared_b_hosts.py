"""Does the actual recurrent B host distinguish the pair of genuine rooted
s1 counterexamples that survive the earlier local equations? If it does,
use the specific missing host condition for shared-source elimination; if
it does not, retain the example as a two-sided regression, not a proof."""
from symbolic_q221_lift import *
from p2_initialized_transfer import history
def run():
 H=[(n,d,set(map(int,gethost(n,d))))for n,d in((25,58203),(25,24899),(34,82754),(25,221))]
 for L,B,G in [(1+2*0x11430f5a714d7a08f7,120,126),(0xdac55ede839754582093c573b2267b893d9a1b46d8c2ccfc22e6692017748834ce533655d28b409e6c2217a26f340778187eaeb34407e8f89290f37800000001,362,368),(1+2*0xac3605e22228962223feca10f58e41e65,122,128)]:
  z=1;A=history(L,G+8)
  for t in range(B-3,G+4):
   y=A[t];c=y>>t&1;r=y>>(t+1)
   if not c:
    print(B,'white',t,'q',r&1,'host',[d for n,d,ss in H if (r%2**n)in ss],flush=True)
if __name__=='__main__':run()
