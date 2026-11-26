// Independent exhaustive search for exponent 7. C++17, GCC/Clang __int128.
// Usage: independent_sieve ladder.txt p_min p_max [max_odd_prime_exclusive]
// A finite cap on odd primes is for testing only. Default tests every odd l < p.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>
using U=__uint128_t; using V=uint64_t;
U num(const std::string& s){U n=0;for(char c:s){if(c<'0'||c>'9')throw std::runtime_error("integer parse");n=n*10+c-'0';}return n;}
std::string str(U n){std::string s;do{s.push_back('0'+n%10);n/=10;}while(n);std::reverse(s.begin(),s.end());return s;}
V root(U n){V a=0,b=V(1)<<63;while(b-a>1){V c=a+(b-a)/2;if(U(c)*c<=n)a=c;else b=c;}return a;}
std::vector<int> primes(int n){std::vector<int> v;for(int p=2;p<=n;p++){bool ok=true;for(int l:v){if(l*l>p)break;if(p%l==0){ok=false;break;}}if(ok)v.push_back(p);}return v;}
int inv(int a,int p){for(int b=1;b<p;b++)if(a*b%p==1)return b;throw std::runtime_error("inverse");}
struct Rule{int p;std::vector<uint8_t> qr,good;std::vector<int> residues;};
struct Group{V modulus,advance;std::vector<V> mask;};
Group group(const std::vector<Rule>& rules,const std::vector<int>& ix,size_t begin,size_t end,V stride){
  std::vector<std::vector<V>> tables; V m=1;
  for(size_t j=begin;j<end;j++){auto &r=rules[ix[j]];m*=r.p;std::vector<V> a(r.p);for(int t=0;t<r.p;t++)for(int b=0;b<64;b++)if(r.good[(t+(stride%r.p)*b)%r.p])a[t]|=V(1)<<b;tables.push_back(std::move(a));}
  Group g{m,V(U(64)*stride%m),std::vector<V>(m,~V(0))};
  for(V t=0;t<m;t++)for(size_t j=begin;j<end;j++)g.mask[t]&=tables[j-begin][t%rules[ix[j]].p];return g;
}
int main(int argc,char** argv){try{
  if(argc<4||argc>5)throw std::runtime_error("usage: ladder.txt p_min p_max [odd_cap]");
  int lo=std::stoi(argv[2]),hi=std::stoi(argv[3]),cap=argc==5?std::stoi(argv[4]):1000000;
  if(lo<2||hi<lo||hi>4297)throw std::runtime_error("prime bounds");
  std::ifstream in(argv[1]);std::string s; if(!(in>>s))throw std::runtime_error("ladder missing");U base=num(s);if(!base)throw std::runtime_error("zero bound");
  std::vector<std::pair<int,U>> ladder;int X;while(in>>X){if(!(in>>s))throw std::runtime_error("bad ladder");ladder.emplace_back(X,num(s));}if(!in.eof())throw std::runtime_error("bad ladder");
  auto ps=primes(hi); V total=0;int count=0;
  for(int p:ps){if(p<lo)continue;++count;U S=4;for(int i=0;i<7;i++)S*=p;U Q=base;for(auto [x,q]:ladder)if(x<=p)Q=std::max(Q,q);
    std::vector<Rule> rules;for(int l:ps){if(l>=p||l>=cap)break;if(l==2)continue;Rule r{l,std::vector<uint8_t>(l),std::vector<uint8_t>(l),{}};for(int a=1;a<l;a++)r.qr[a*a%l]=1;int z=S%l;for(int a=0;a<l;a++){int d=(a*a%l+l-z)%l;if(d&&!r.qr[d]){r.good[a]=1;r.residues.push_back(a);}}rules.push_back(std::move(r));}
    V ymax=root(S/Q),survivors=0,roots=0,wheel_residues=0,blocks=0,exact=0;
    for(V y=1;y<=ymax;y++){
      U yy=U(y)*y;V xmax=root(S-Q*yy);V M=8*V(yy);U modtarget=(S%M+M-U(p==2?7:3)*yy)%M;
      std::vector<V> a;for(V x=0;x<M&&x<=xmax;x++)if(U(x)*x%M==modtarget)a.push_back(x);roots+=a.size();if(a.empty())continue;
      std::vector<int> ix,defer;for(size_t j=0;j<rules.size();j++)(y%rules[j].p?ix:defer).push_back(j);
      // Direct CRT lifting in x, beginning with the exact q mod 8 and y^2 congruences.
      V stride=M;size_t k=0;
      while(k<ix.size()&&k<9){auto &r=rules[ix[k]];if(U(stride)*r.p>std::max<V>(xmax/64,1)||U(a.size())*r.residues.size()>2000000)break;
        int u=inv(stride%r.p,r.p);std::vector<V> next;next.reserve(a.size()*r.residues.size());
        for(V z:a)for(int t:r.residues){V j=(V((t+r.p-z%r.p)%r.p)*u)%r.p;U x=U(z)+U(stride)*j;if(x<=xmax)next.push_back(V(x));}
        stride*=r.p;a.swap(next);++k;if(a.empty())break;}
      if(a.empty())continue;wheel_residues+=a.size();
      // Combine remaining small-prime conditions into paired periodic masks on x.
      std::vector<Group> gs;size_t j=k;while(j<ix.size()&&j<k+12&&rules[ix[j]].p<96){size_t e=j+1;if(e<ix.size()&&e<k+12&&rules[ix[e]].p<96)++e;gs.push_back(group(rules,ix,j,e,stride));j=e;}
      for(V z:a){if(z>xmax)continue;V N=(xmax-z)/stride+1;std::vector<V> phase;for(auto &g:gs)phase.push_back(z%g.modulus);
        for(V t=0;t<N;t+=64){V mask=~V(0);for(size_t h=0;h<gs.size();h++){auto &g=gs[h];mask&=g.mask[phase[h]];phase[h]+=g.advance;if(phase[h]>=g.modulus)phase[h]-=g.modulus;}++blocks;
          if(N-t<64)mask&=(V(1)<<(N-t))-1;
          while(mask){int bit=__builtin_ctzll(mask);mask&=mask-1;V x=z+stride*(t+bit);bool ok=true;
            for(size_t h=j;h<ix.size();h++){auto &r=rules[ix[h]];if(!r.good[x%r.p]){ok=false;break;}}if(!ok)continue;++exact;
            U n=S-U(x)*x;if(n%yy)throw std::runtime_error("CRT invariant");U q=n/yy;if(q<Q||q%8!=(p==2?7:3))throw std::runtime_error("q invariant");
            for(int h:defer){auto &r=rules[h];int d=(r.p-int(q%r.p))%r.p;if(!d||r.qr[d]){ok=false;break;}}if(!ok)continue;
            ++survivors;std::cout<<"SURVIVOR "<<p<<' '<<y<<' '<<x<<' '<<str(q)<<'\n';
          }
        }
      }
    }
    total+=survivors;std::cout<<"P "<<p<<" Qlo "<<str(Q)<<" ymax "<<ymax<<" roots "<<roots<<" wheel_residues "<<wheel_residues<<" blocks "<<blocks<<" exact "<<exact<<" survivors "<<survivors<<std::endl;
  }
  std::cout<<"DONE primes "<<count<<" survivors "<<total<<std::endl;return 0;
}catch(const std::exception& e){std::cerr<<e.what()<<'\n';return 1;}}
