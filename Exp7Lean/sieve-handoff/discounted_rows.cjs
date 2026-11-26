// Independent fixed-point verifier. Node.js >=18; run from repository root.
function verify(raw) {
  // All interval endpoints are signed integers in units of 10^-30.
  const S=10n**30n, I=n=>[BigInt(n)*S,BigInt(n)*S];
  const fl=(a,b)=>{if(b<=0n)throw Error("nonpositive denominator");return a>=0n?a/b:-((-a+b-1n)/b)};
  const ce=(a,b)=>-fl(-a,b);
  const rat=(a,b)=>[fl(BigInt(a)*S,BigInt(b)),ce(BigInt(a)*S,BigInt(b))];
  const add=(a,b)=>[a[0]+b[0],a[1]+b[1]], sub=(a,b)=>[a[0]-b[1],a[1]-b[0]];
  const min=a=>a.reduce((x,y)=>x<y?x:y), max=a=>a.reduce((x,y)=>x>y?x:y);
  const mul=(a,b)=>{const z=[a[0]*b[0],a[0]*b[1],a[1]*b[0],a[1]*b[1]];return [fl(min(z),S),ce(max(z),S)]};
  const div=(a,b)=>{if(b[0]<=0n)throw Error("division across zero");const l=[],h=[];for(const x of a)for(const y of b){l.push(fl(x*S,y));h.push(ce(x*S,y))}return [min(l),max(h)]};
  const one=I(1),zero=I(0);
  const isqrt=n=>{if(n<0n)throw Error("negative sqrt");if(n<2n)return n;let a=1n<<BigInt(Math.ceil(n.toString(2).length/2));while(true){let b=(a+n/a)/2n;if(b>=a)return a;a=b}};
  const sqrt=a=>[isqrt(a[0]*S),isqrt(a[1]*S)+1n];
  // For 1 <= x <= 2, log x = 2 sum z^(2k+1)/(2k+1), z=(x-1)/(x+1).
  // 50 terms: omitted tail < 2*(1/3)^101/(101*(1-1/9)) < 10^-30.
  function logUnit(x){const z=div(sub(x,one),add(x,one)),z2=mul(z,z);let t=z,sum=zero;for(let k=0;k<50;k++){sum=add(sum,div(t,I(2*k+1)));t=mul(t,z2)}return add(mul(I(2),sum),[-1n,1n])}
  const log2=logUnit(I(2));
  function logEndpoint(x){let k=0;let a=[x,x];while(a[0]>=2n*S){a=div(a,I(2));k++}while(a[1]<S){a=mul(a,I(2));k--}return add(logUnit(a),mul(I(k),log2))}
  const log=a=>[logEndpoint(a[0])[0],logEndpoint(a[1])[1]];
  const logs=new Map(), ln=n=>{let k=String(n);if(!logs.has(k))logs.set(k,log(I(n)));return logs.get(k)};
  // exp(x) for 0 <= x <= 1/10, 30 terms, omitted tail < 10^-60.
  function expSmall(x){if(x[0]<0n||x[1]>S/10n)throw Error("exp range");let t=one,sum=one;for(let k=1;k<=30;k++){t=div(mul(t,x),I(k));sum=add(sum,t)}return add(sum,[0n,1n])}
  const pi=[3141592653589793238462643383279n,3141592653589793238462643383280n];
  const gamma=[577215664901532860606512090082n,577215664901532860606512090083n];
  const constant=add(sub(add(log(pi),gamma),div(pi,I(2))),mul(I(3),log2));
  const c=JSON.parse(raw.replace(/"(Q|QLOW|QTOP|Qstar|newQ)"\s*:\s*(\d+)/g,'"$1":"$2"'));
  const assert=(x,m)=>{if(!x)throw Error(m)};
  assert(BigInt(c.QLOW)===31n*10n**19n&&BigInt(c.QTOP)===10n**32n,"domain");
  const primes=[];for(let p=2;p<7000;p++){if(primes.every(l=>l*l>p||p%l))primes.push(p)}
  function rowCheck(row){
    const X=row.X,m=row.v.length;assert(m===64&&Number.isInteger(X)&&X>2&&X<7000,"row shape");
    const v=row.v.map(BigInt),norm=v.reduce((s,t)=>s+t*t,0n);assert(norm>0n,"zero vector");
    const corr=Array.from({length:m+1},(_,j)=>rat(v.slice(0,m-j).reduce((s,t,k)=>s+t*v[k+j],0n),norm));
    const w=div(ln(X),I(m)),powers=Array.from({length:m+1},(_,k)=>BigInt(X)**BigInt(k));
    function f(n){const N=BigInt(n)**BigInt(m);let k=0;while(k+1<m&&powers[k+1]<=N)k++;
      assert(powers[k]<=N&&N<powers[k+1],"cell");return add(corr[k],mul(sub(div(ln(n),w),I(k)),sub(corr[k+1],corr[k])))}
    let total=zero, penalties=[];for(const p of primes){if(p>=X)break;let d=zero;for(let n=p,s=-1;n<X;n*=p,s=-s){const term=div(mul(mul(I(2*s),ln(p)),f(n)),sqrt(I(n)));total=add(total,term);if(s===-1)d=add(d,mul(I(2),term));}penalties.push([p,d[1]]);}
    // Upper bound J: on first cell a(u)<=1/u. Subsequent subcells
    // use decreasing a(u) times the exact average of nonnegative 1-f.
    const pieces=16,step=div(w,I(pieces)),b=div(one,expSmall(div(step,I(2))));
    const b2=mul(b,b),b3=mul(b2,b),b4=mul(b2,b2);
    let z3=one,z4=one,J=sub(one,corr[1]);
    for(let i=1;i<m*pieces;i++){z3=mul(z3,b3);z4=mul(z4,b4);if(i<pieces)continue;
      const j=Math.floor(i/pieces),k=i%pieces;
      const mean=add(corr[j],mul(rat(2*k+1,2*pieces),sub(corr[j+1],corr[j])));
      const a=div(mul(I(2),z3),sub(one,z4));J=add(J,mul(mul(step,a),sub(one,mean)))}
    J=add(J,div(I(4),mul(mul(mul(I(3),I(X)),sqrt(I(X))),sub(one,rat(1n,BigInt(X)**2n)))));
    const margin=add(sub(sub(total,J),ln(BigInt(row.Q))),constant);
    assert(margin[0]>0n,"nonpositive margin X="+X);
    return {margin:margin[0],penalties};
  }

  const rows=[...c.bootstrap,...c.ladder], base=BigInt(c.QLOW), top=BigInt(c.QTOP);
  assert(rows.length===175&&c.B===100000,"extended certificate domain");
  const ps=primes.filter(p=>p>=3&&p<=4297);
  const oldBound=(p,b)=>rows.reduce((a,r)=>r.X<=p&&BigInt(r.Q)>a?BigInt(r.Q):a,b);
  const best=ps.map(p=>({p,bound:100000n,row:-1,k:0,penalty:"0"}));
  const unit=log(rat(16,15))[0]; assert(unit>0n,"log ratio");
  const cache=new Map();
  function discounted(Q,k){const key=k.toString();let f=cache.get(key);if(!f){f=[15n**k,16n**k];cache.set(key,f)}return Q*f[0]/f[1]}
  let minmargin=null;
  for(let j=0;j<rows.length;j++){
    const row=rows[j],{margin,penalties}=rowCheck(row);
    minmargin=minmargin===null?margin:min([margin,minmargin]);
    let t=penalties.length-1,tail=0n;const Q=BigInt(row.Q);
    for(let i=ps.length-1;i>=0;i--){
      const p=ps[i];
      while(t>=0&&penalties[t][0]>p){tail+=max([0n,penalties[t][1]]);t--}
      // At p itself, the character is known +1, so its signed penalty can be used.
      let penalty=tail;
      if(t>=0&&penalties[t][0]===p)penalty+=penalties[t][1];
      const k=ce(max([0n,penalty-margin]),unit);
      const bound=discounted(Q,k);
      if(bound>best[i].bound)best[i]={p,bound,row:j,k:Number(k),penalty:penalty.toString()};
      if(t>=0&&penalties[t][0]===p){tail+=max([0n,penalties[t][1]]);t--}
    }
  }
  const out=best.map(r=>({...r,bound:r.bound.toString()}));
  function stats(mode){let count=0,oldActive=0,newActive=0,oldY=0n,newY=0n,oldWork=0n,newWork=0n,maxratio=0;
    const b=mode==="high"?base:100000n;
    for(const r of best){const p=r.p;if(mode==="high"?p<701:p>=2760)continue;count++;
      const old=oldBound(p,b),nw=max([old,r.bound]),S=4n*BigInt(p)**7n;
      const y0=mode==="low"&&old>=base?0n:isqrt(S/old),y1=mode==="low"&&nw>=base?0n:isqrt(S/nw);
      if(y0>0n)oldActive++;if(y1>0n)newActive++;oldY+=y0;newY+=y1;oldWork+=isqrt(S)*y0;newWork+=isqrt(S)*y1;maxratio=Math.max(maxratio,Number(nw)/Number(old));
    }return {count,oldActive,newActive,eliminated:oldActive-newActive,oldY:oldY.toString(),newY:newY.toString(),oldWork:oldWork.toString(),newWork:newWork.toString(),maxratio}}
  return {schema:"discounted-row-v1",ratio:"16/15",minimumRowMarginFixedPoint:minmargin.toString(),scale:S.toString(),rowCount:rows.length,high:stats("high"),low:stats("low"),bounds:out};
}

const fs=require('node:fs');
console.log(JSON.stringify(verify(fs.readFileSync(process.argv[2] || 'lowrange/certificate_full.json','utf8')),null,2));
