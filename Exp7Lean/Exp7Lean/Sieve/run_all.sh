#!/bin/bash
# Generate and compile the per-prime certificates P<p>.lean for the primes 701 <= p <= 4297.
#
#   Exp7Lean/Sieve/run_all.sh [JOBS] [MAXSEC] [GENARGS...]      (run from the workspace root)
#
# JOBS    number of primes compiled at the same time (default 1; each is one Lean process, run
#         through bin/leanq, which enforces the machine-wide limit)
# MAXSEC  do not start new primes after this many seconds (default 0: no limit)
# GENARGS passed to gen.py (e.g. --budget 4e8)
# PRIMES  (environment) do only these primes, in this order
#
# Primes are taken in increasing order of estimated cost (estimate.py, cached in
# Exp7Lean/Sieve/logs/estimate.txt).  Each file is compiled directly with `lean -o` (a `lake build`
# per prime costs 20-30 s of lake start-up each time), the .olean being put where `lake env lean`
# finds it; a later `lake build` will want to recompile the files.  A prime whose .olean exists is
# skipped, so the script can be stopped and restarted.  CPU time, elapsed time and peak memory of
# each prime are appended to Exp7Lean/Sieve/logs/times.txt; the output of a failed run is kept in
# logs/P<p>.log (a failure of `decide` would mean that a block survived the sieve: regenerate that
# prime with a larger --lmax, at most 397).  When all 465 are done:
#   python3 Exp7Lean/Sieve/gen_all.py && bin/leanq Exp7Lean/Sieve/All.lean
JOBS=${1:-1}
MAXSEC=${2:-0}
shift 2 2>/dev/null
GENARGS="$@"
LEANQ=${LEANQ:-/home/zlab/GitHub/exp7-agents/bin/leanq}
D=Exp7Lean/Sieve
O=.lake/build/lib/lean/Exp7Lean/Sieve
mkdir -p $D/logs $O
[ -s $D/logs/estimate.txt ] || python3 $D/estimate.py > $D/logs/estimate.txt
START=$(date +%s)
one() {
  p=$1
  [ -f $O/P$p.olean ] && return 0
  if [ "$MAXSEC" -gt 0 ] && [ $(( $(date +%s) - START )) -gt "$MAXSEC" ]; then return 0; fi
  [ -f $D/P$p.lean ] || python3 $D/gen.py $p $GENARGS > /dev/null || { echo "$p GENFAIL" >> $D/logs/times.txt; return 1; }
  /usr/bin/time -f "%U %e %M" -o $D/logs/P$p.time $LEANQ $D/P$p.lean -o $O/P$p.olean.tmp -i $O/P$p.ilean.tmp > $D/logs/P$p.log 2>&1
  rc=$?
  if [ $rc -eq 0 ] && grep -q "'Exp7.search_$p' depends on axioms: \[propext, Classical.choice, Quot.sound\]" $D/logs/P$p.log \
       && ! grep -q "error\|sorry" $D/logs/P$p.log; then
    mv $O/P$p.olean.tmp $O/P$p.olean; mv $O/P$p.ilean.tmp $O/P$p.ilean
    echo "$p OK user_s elapsed_s maxrss_kb: $(tail -n 1 $D/logs/P$p.time)" >> $D/logs/times.txt
    command rm -f $D/logs/P$p.log $D/logs/P$p.time
  else
    command rm -f $O/P$p.olean.tmp $O/P$p.ilean.tmp
    echo "$p FAIL rc=$rc" >> $D/logs/times.txt
  fi
}
export -f one
export MAXSEC START GENARGS LEANQ D O
if [ -n "$PRIMES" ]; then echo $PRIMES | tr ' ' '\n'; else grep -v TOTAL $D/logs/estimate.txt | sort -k11 -g | awk '{print $1}'; fi |
  xargs -P "$JOBS" -I{} bash -c 'one {}'
echo "done: $(ls $O | grep -c '^P[0-9]*\.olean$') of 465"
