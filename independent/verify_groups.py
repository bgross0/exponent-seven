from math import isqrt, gcd
from sympy import primerange, kronecker_symbol
from collections import Counter
# Independent form enumeration and generator checks on the 33 published fields.
qs=[71,151,223,251,463,467,487,587,811,827,859,1163,1171,1483,1523,1627,1787,1987,2011,2083,2179,2251,2467,2707,3019,3067,3187,3907,4603,5107,5923,63499,118843]
counts=Counter()
for q in qs:
    forms=[]
    for a in range(1,isqrt(q//3)+1):
        for b in range(-a,a+1):
            if (b*b+q)%(4*a):continue
            c=(b*b+q)//(4*a)
            if c<a or ((abs(b)==a or c==a) and b<0) or gcd(gcd(a,b),c)!=1:continue
            forms.append((a,b,c))
    h=len(forms); assert h in (7,49);counts[h]+=1
    if h==49:
        # Reduced forms have a <= sqrt(q/3) and their ideal classes generate.
        # Only split prime factors are needed; inert prime ideals are principal.
        assert q%8==3
        for p in primerange(3,isqrt(q//3)+1):
            if kronecker_symbol(-q,p)!=1:continue
            S=4*p**7
            for y in range(1,isqrt(S//q)+1):
                if y%p==0:continue
                n=S-q*y*y;x=isqrt(n)
                if x*x==n and (x-y)%2==0:
                    print(f'generator q={q} p={p} x={x} y={y}',flush=True);break
            else:raise AssertionError((q,p))
    print(f'field q={q} h={h} exponent=7',flush=True)
assert counts=={7:31,49:2};print('PASS: 31 C7, 2 C7 x C7')
