// Test the SHORTEST NONCONSTANT recurring word in the exact host DFA:
// can its periodic far-west crystal separate the two opposite-parity B
// packet rotations? Unequal rotations disprove a grammar-only bounded
// separation. Equal rotations or a capped iteration do not prove the
// finite-west result. Brent uses constant memory and no spatial lift.
#include<cstdio>
#include<cstdint>
#include<cstdlib>
#include<string>
#include<numeric>
#include<map>
#include<tuple>
using U=uint64_t;struct Pair{U a,b;bool operator==(const Pair&z)const{return a==z.a&&b==z.b;}};
U mask;int T; Pair step(Pair x){return {x.b,((x.b>>1)|((x.b&1)<<(T-1)))^(x.a|x.b)};}
int main(int ac,char**av){std::string w=ac>1?av[1]:"3555";int limit=ac>2?atoi(av[2]):80000000;U c=0,r=0;T=0;for(char a:w){r|=1ull<<(T+3);T+=2*(a-'0');}if(T>=63)return 1;for(int t=0;t<T;t+=2)c|=1ull<<t;mask=(1ull<<T)-1;
Pair init={c,((c>>1)|((c&1)<<(T-1)))^(c|r)};int pow=1,P=1,N=1;Pair l=init,h=step(init);
while(!(l==h)&&N<limit){if(pow==P){l=h;pow*=2;P=0;}h=step(h);P++;N++;}
if(!(l==h)){printf("word %s no Brent confirmation by %d\n",w.c_str(),N);return 0;}int s=0;l=init;h=init;for(int i=0;i<P;i++)h=step(h);while(!(l==h)){l=step(l);h=step(h);s++;}
auto rot=[&](U z,int k){k%=T;return k?(z>>k|(z<<(T-k)))&mask:z;};U OR=0,AND=mask;for(int j=0;j<P;j++){U z=rot(l.b,(j+s)%T);OR|=z;AND&=z;l=step(l);}auto o=OR,a=AND;for(int i=1;i<T/std::gcd(T,P);i++){OR|=rot(o,(P%T)*i);AND&=rot(a,(P%T)*i);}
printf("word %s temporal %d spatial transient %d spatial period %d normalized white/black masks %llx/%llx\n",w.c_str(),T,s,P,(unsigned long long)(OR^mask),(unsigned long long)AND);
// Starting at an actual black B and its black x=-1 neighbor, follow the
// two distinct normalized-parity packets. Their resolved medium is the
// whole temporally periodic prescribed west, not a torus assumption at wall.
for(int parity=0;parity<2;parity++){
 long long j=0,q=parity,tick=0;int ph=0;Pair z=init;std::map<std::pair<int,int>,std::pair<long long,long long>>seen;
 while(true){if(j>=s&&(j-s)%P==0){auto key=std::make_pair(ph,int(q-j));if(seen.count(key)){auto [oj,ot]=seen[key];auto dt=tick-ot,dj=j-oj,gg=std::gcd(dt,dj);
 printf("initial B parity %d: physical west travel/time %lld/%lld (cycle travel/time %lld/%lld)\n",parity,dj/gg,dt/gg,dj,dt);break;}
 seen[key]={j,tick};}
 auto nz=step(z);if(j==q){if(nz.b>>ph&1)q+=2;else {q++;tick++;ph++;if(ph==T)ph=0;}}z=nz;j++;
 }
}

}
