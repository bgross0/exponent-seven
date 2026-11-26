"""Validate independent full-run output; usage: python independent/validate_run.py ladder.txt shards/*.log"""
import sys, math, pathlib, re, hashlib, json
ladder=pathlib.Path(sys.argv[1]); rows=ladder.read_text().splitlines(); base=int(rows[0]); pairs=[tuple(map(int,r.split())) for r in rows[1:]]
assert base==31*10**19
prime=lambda p:p>=2 and all(p%d for d in range(2,math.isqrt(p)+1))
expected={p for p in range(701,4298) if prime(p)}; assert len(expected)==465
pat=re.compile(r'^P (\d+) Qlo (\d+) ymax (\d+) roots (\d+) wheel_residues (\d+) blocks (\d+) exact (\d+) survivors (\d+)$')
records={}; receipts=[]
for f in sys.argv[2:]:
    path=pathlib.Path(f); raw=path.read_bytes(); lines=raw.decode().splitlines(); count=0
    for line in lines[:-1]:
        m=pat.fullmatch(line); assert m,(f,line)
        p,Q,y,r,w,b,e,s=map(int,m.groups()); assert p in expected and p not in records,(p,f)
        assert Q==max([base]+[q for x,q in pairs if x<=p]),(p,Q)
        assert y==math.isqrt(4*p**7//Q) and s==0,(p,y,s)
        records[p]=(r,w,b,e,s); count+=1
    assert lines[-1]==f'DONE primes {count} survivors 0',(f,lines[-1]); receipts.append({'file':path.name,'prime_count':count,'sha256':hashlib.sha256(raw).hexdigest()})
assert set(records)==expected,(len(records),sorted(expected-set(records)))
report={'status':'PASS','prime_count':len(records),'range':[min(records),max(records)],'survivors':sum(v[-1] for v in records.values()),'total_roots':sum(v[0] for v in records.values()),'total_wheel_residues':sum(v[1] for v in records.values()),'total_blocks':sum(v[2] for v in records.values()),'total_exact':sum(v[3] for v in records.values()),'ladder_sha256':hashlib.sha256(ladder.read_bytes()).hexdigest(),'source_sha256':hashlib.sha256(pathlib.Path(__file__).with_name('independent_sieve.cpp').read_bytes()).hexdigest(),'receipts':receipts}
print(json.dumps(report,indent=2))
