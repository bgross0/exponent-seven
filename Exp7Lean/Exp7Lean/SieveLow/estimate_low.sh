#!/bin/bash
# Plans (no Lean): runs `gen_low.py P --stats` for all 401 primes (or $PRIMES) and collects the
# summary lines in logs/estimate.txt:
#   STAT p Y0 ymax sieves tab leaves bits exceptions survivors est_kernel_s est_elab_s generator_s
# The generator redoes the whole search in Python, so this is also an independent check of the
# list of survivors (the run stops with an assertion if a prime disagrees).
#   Exp7Lean/SieveLow/estimate_low.sh [JOBS]      (run from the workspace root)
JOBS=${1:-1}
D=Exp7Lean/SieveLow
mkdir -p $D/logs
if [ -n "$PRIMES" ]; then echo $PRIMES | tr ' ' '\n'
else python3 -c "print('\n'.join(str(p) for p in range(3, 2760) if all(p % d for d in range(2, int(p ** 0.5) + 1))))"
fi | xargs -P "$JOBS" -I{} bash -c "python3 $D/gen_low.py {} --stats 2>&1 | grep '^STAT\|Error\|error' || echo 'FAIL {}'" > $D/logs/estimate.txt
awk '$1=="STAT" {n++; k+=$11; e+=$12; g+=$13; s+=$10} END {printf "primes %d  survivors %d  kernel %.0f s  elaboration %.0f s  generator %.0f s\n", n, s, k, e, g}' $D/logs/estimate.txt
echo "failed: $(grep -c FAIL $D/logs/estimate.txt)"
