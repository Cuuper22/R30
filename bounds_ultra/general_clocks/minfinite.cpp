// Of all distinct accepted white-label prefixes of a given physical length,
// find the smallest nonnegative physical strict-west prefix that induces one.
// This minimizes the actual ordinary support, not the density or number of
// graph paths. Truncated 128 bits suffice for the length<=127 declared below.
#include<cstdint>
#include<cstdio>
#include<cstdlib>
#include<algorithm>
#include<string>
#include<vector>
#include<iostream>
#include<sstream>
using U=__uint128_t;
struct Min {U w=~U(0); std::string labels; unsigned long long count=0; int rim=-1,age=-1;std::string rq;};
int P,K,V,B;std::string p;U C;std::vector<std::vector<int>>T;std::vector<unsigned>h;std::vector<Min>D;U root[128];
U decode(U b,int m){U r=0,a=C;for(int j=0;j<m;j++){r|=(b&1)<<j;U z=(b>>1)^(b|a);a=b;b=z;}return r;}
int size(U x){int n=0;while(x){n++;x>>=1;}return n;}
std::string hex(U x){std::string s="";do{s="0123456789abcdef"[int(x&15)]+s;x>>=4;}while(x);return s;}
void go(int i,int v,U H,std::string&w){
 if(i){Min &b=D[i];U z=decode(H,i*P);b.count++;int age=size(z),rim=age-size(z^root[age]); if(rim>b.rim){b.rim=rim;b.age=age;b.rq=w;}if(z<b.w){b.w=z;b.labels=w;}}
 if(i==K)return;for(int y=0;y<B;y++)if(T[v][y]>=0){w.push_back('0'+y);go(i+1,T[v][y],H|(U(h[y])<<(i*P)),w);w.pop_back();}
}
int main(){std::cin>>p>>K>>V>>B;P=p.size();if(K*P>127)return 2;T.assign(V,std::vector<int>(B));
 for(auto&r:T)for(auto&x:r)std::cin>>x;C=0;for(int j=0;j<128;j++)C|=U(p[j%P]-'0')<<j;
 h.resize(B);for(int y=0;y<B;y++){int k=std::count(p.begin(),p.end(),'0');for(int j=0;j<P;j++){int z=p[j]=='0'?(y>>--k&1):0;h[y]|=(int(p[(j+1)%P]-'0')^(int(p[j]-'0')|z))<<j;}}
 U Z=1;for(int t=0;t<128;t++){U W=0;for(int k=0;k<t;k++)W|=((Z>>k)&1)<<(t-1-k);root[t]=W;Z=(4*Z)^(2*Z|Z);}D.resize(K+1);std::string w;go(0,0,0,w);
 for(int i=1;i<=K;i++){auto& a=D[i];if(i>=2&&a.w<D[i-1].w)return 3;
  U x=a.w;int t=0;for(char c:a.labels){int z=c-'0';for(int j=0;j<P;j++,t++){
    if(int(x&1)!=int(h[z]>>j&1))return 4;x=(x>>1)^(x|((x<<1)|((C>>(t%P))&1)));}}
  std::cout<<p<<' '<<i<<' '<<P*i<<' '<<a.count<<' '<<size(a.w)<<' '<<hex(a.w)<<' '<<a.labels<<' '<<a.rim<<' '<<a.age<<' '<<a.rq<<'\n';}
}
