"""Two-sided marked D4 reader, either time checkerboard. Test endpoint
compatibility on every occurrence of 01,011,00101 through row 500;
independently generate actual infinite-space R90 with exactly each tail.
The toolkit control independently enumerates each rule's own mature set.
"""
import os,sys
from pathlib import Path

def field(rule,pat=None,N=500):
    # Left is blank, origin is 1; for R90 construct actual right ancestors
    # by triangular inversion of (S+S^-1)^t, extending forever by this rule.
    v=1
    if rule==90:
        for t in range(1,2*N+7):
            j=t;b=0
            while j>=0:
                k=2*j-t
                if k>=0:b^=(v>>k)&1
                if not j:break
                j=(j-1)&t
            v|=(b^int(pat[(t-1)%len(pat)]))<<t
    O=N+6;z=v<<O;rr=[]
    for n in range(N+1):
        rr.append(z);z=(2*z)^((z|z>>1)if rule==30 else z>>1)
    at=lambda t,x:rr[t]>>(O+x)&1
    if rule==90:assert all(at(t,0)==int(pat[(t-1)%len(pat)])for t in range(1,N+1))
    return at

def factor(z,old,bp):
    u,v=old&1,old>>1;k=bp|u
    return ((1 if k^v else -1)*z+(3 if k else 2*v))%4

def case(rule,pat,N=500):
    at=field(rule,pat,N);P=len(pat);bits=tuple(map(int,pat));C=lambda n:at(n,0)
    ticks=good=wordgood=wordcount=blackgood=blackcount=0
    for i in range(1,(N-4)//2+1):
      for s in(0,1):
        # j=-1 encodes the true sharp west rim: 0 in the even grouping,
        # 2 (antipodal) in the odd grouping. bprev comes from that old pair.
        z=2*s;anti=z^2;bp=s;wmatch=True
        for j in range(i+1):
            t=i+j+s; x=j-i
            w=at(t,x)+2*at(t+1,x)
            z=factor(z,w,bp);anti=factor(anti,w,bp);bp=w>>1
            assert anti==z^2
            true=at(t+1,x-1)+2*at(t+2,x-1);wmatch&=z==true
        ticks+=1;good+=wmatch;t=2*i+s
        # Marked west endpoint from the independent east data and center.
        # For each possible black/white phase derive the allowed D4 state.
        if all(C(t+k)==bits[k%P] for k in range(P)):
            wordcount+=1
            E=(C(t+2)^(C(t+1)|at(t+1,1)))+2*(C(t+3)^(C(t+2)|at(t+2,1)))
            wordgood+=z==E
            if C(t+2):
                blackcount+=1;blackgood+=(z>>1)==(1^C(t+3))
    print('rule,pattern,full paired readers/full words,matched pattern east terminal tests,readouts at anchored black upper bit',rule,pat,(good,ticks),(wordgood,wordcount),(blackgood,blackcount))
    if rule==30:assert good==ticks and wordgood==wordcount and blackgood==blackcount
    else:assert good<ticks and wordgood<wordcount

def toolkit():
    sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'r30fast'))
    import r30fast
    for p in ('01','011','00101'):
        for rule in(30,90):
            m,h=r30fast.general_p_hosts(p,n=12,rule=rule,return_states=False)
            print('independent same-pattern toolkit control',p,rule,'mature',m,'q variable counts',sum(x.q_variable for x in h))
if __name__=='__main__':
    for p in('01','011','00101'):
        for rule in(30,90):case(rule,p)
    if '--toolkit' in sys.argv:toolkit()
