// Can an admissible isolated-3 west decoder have BOTH of the normalized
// white rails needed to capture its old B particles forever, without a
// finite west? Such a periodic temporal certificate would decisively
// rule out capture alone. Otherwise retain exact no-rail periodic cases,
// never infer a theorem from the capped or bounded period search.
#include<cinttypes>
#include<cstdio>
#include<cstdint>
#include<utility>
#include<vector>
#include<string>
#include<algorithm>
#include<unordered_map>
#include<numeric>
using U=uint64_t;using P=std::pair<U,U>;
struct H{size_t operator()(P const&v) const{return v.first^(v.second*0x9e3779b97f4a7c15ull);} };
void go(std::string s,int cap){int T=0;for(char h:s)T+=2*(h-'0');if(T>62)return;U m=(1ull<<T)-1,c=0,r=0;int t=0;
for(char h:s){r|=1ull<<(t+3);t+=2*(h-'0');}for(int k=0;k<T;k+=2)c|=1ull<<k;
auto rot=[&](U x,int n){n%=T;return n?((x>>n)|(x<<(T-n)))&m:x;};
U a=c,b=rot(c,1)^(c|r);std::unordered_map<P,int,H>I;std::vector<U>V;int n=0;
while(!I.count({a,b})&&n<cap){I[{a,b}]=n++;V.push_back(b);U z=rot(b,1)^(a|b);a=b;b=z;}
if(n==cap){printf("word %s physical %d no spatial cycle within %d\n",s.c_str(),T,cap);return;}
int off=I[{a,b}],p=n-off;U ever=0,always=m;
for(int j=0;j<p;j++){auto z=rot(V[off+j],(off+j)%T);ever|=z;always&=z;}
for(int k=1;k<T/std::gcd(T,p);k++){ever|=rot(ever,p%T);always&=rot(always,p%T);}
printf("word %s physical %d spatial transient %d period %d normalized permanent white %" PRIx64 " black %" PRIx64 "\n",s.c_str(),T,off,p,m^ever,always);
}
int main(){for(int n=1;n<=7;n++)for(int a=0;a<(1<<n);a++){std::string s;
for(int j=0;j<n;j++)s+=a>>j&1?'3':'5';if((s+s).find("33")!=std::string::npos)continue;
bool ok=1;for(int i=1;i<n;i++)if(s.substr(i)+s.substr(0,i)<=s)ok=0;if(ok)go(s,210000);}
}
