"""Run from the directory containing compiled independent_sieve (Python + sympy)."""
import math, subprocess, tempfile, sympy as sp, pathlib
cases=[(2,1,1000),(3,1,1000),(5,100,1000),(7,1000,1000),(11,10000,7),(13,100000,13),(17,1000000,11),(19,1000000,19),(31,10**8,17),(43,10**10,19),(61,10**11,23)]
with tempfile.TemporaryDirectory() as tmp:
    path=pathlib.Path(tmp)/'bound.txt'
    for p,Q,cap in cases:
        path.write_text(f'{Q}\n')
        result=subprocess.check_output(['./independent_sieve',str(path),str(p),str(p),str(cap)],text=True)
        found={tuple(map(int,l.split()[1:])) for l in result.splitlines() if l.startswith('SURVIVOR ')}
        expected=set(); S=4*p**7; ls=list(sp.primerange(3,min(p,cap)))
        for y in range(1,math.isqrt(S//Q)+1):
            for x in range(math.isqrt(S-Q*y*y)+1):
                n=S-x*x
                if n%(y*y):continue
                q=n//(y*y)
                if q%8!=(7 if p==2 else 3):continue
                if all(pow((-q)%l,(l-1)//2,l)==l-1 for l in ls):expected.add((p,y,x,q))
        assert expected==found,(p,len(expected),len(found),expected-found,found-expected)
        print(f'p={p} Q={Q} cap={cap}: {len(found)} survivors; exact agreement',flush=True)
    # ARSX Table A.7, filtered to prime fundamental discriminants.
    values=[71,151,223,251,284,343,463,467,487,587,604,811,827,859,892,1163,1171,1372,1483,1523,1627,1787,1852,1948,1987,2011,2083,2179,2251,2467,2707,3019,3067,3187,3907,4603,5107,5923,63499,118843]
    fields=[q for q in values if sp.isprime(q) and q%4==3];assert len(fields)==33
    for q in fields:
        p=next(p for p in sp.primerange(2,1000) if sp.kronecker_symbol(-q,p)==1)
        path.write_text(str(q)+'\n')
        out=subprocess.check_output(['./independent_sieve',str(path),str(p),str(p)],text=True)
        solutions=[tuple(map(int,l.split()[1:])) for l in out.splitlines() if l.startswith('SURVIVOR ') and int(l.split()[-1])==q]
        assert solutions,(q,p)
        print(q,p,solutions[0][1],solutions[0][2],flush=True)
    print('PASS: all 33 known field controls')
