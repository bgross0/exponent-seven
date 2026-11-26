#!/bin/bash
# Generate and compile the per-prime certificates P<p>.lean of the low-range search, for the 401
# primes 3 <= p < 2760 (Exp7.SearchLow).
#
#   Exp7Lean/SieveLow/run_low.sh [JOBS] [MAXSEC] [GENARGS...]      (run from the workspace root)
#
# JOBS    number of primes done at the same time (default 1; each is one Lean process, run through
#         bin/leanq, which enforces the machine-wide limit; a Lean process uses about 5 GB)
# MAXSEC  do not start new primes after this many seconds (default 0: no limit)
# GENARGS passed to gen_low.py (e.g. --budget 4e8)
# PRIMES  (environment) do only these primes, in this order (default: all 401, increasing)
# KEEP    (environment) KEEP=0 deletes P<p>.lean after a successful compilation (the files take
#         about 200 MB in total; they can be regenerated, the generator is deterministic)
#
# For each prime: gen_low.py writes P<p>.lean (it redoes the whole search in Python, checks its
# survivors against Witness/SurvivorData.lean and, if present, against the log of the C search);
# the file is compiled with `lean -o`, the .olean being put where `lake env lean` finds it (a later
# `lake build` will want to recompile the files).  A prime whose .olean exists is skipped, so the
# script can be stopped and restarted.  CPU time, elapsed time and peak memory of each prime are
# appended to Exp7Lean/SieveLow/logs/times.txt, with the summary line of the generator; the output
# of a failed run is kept in logs/P<p>.log.  A prime is accepted only if Lean exits with 0, prints
#   'Exp7.searchLow_<p>' depends on axioms: [propext, Classical.choice, Quot.sound]
# and no error or sorry.  When all 401 are done:
#   python3 Exp7Lean/SieveLow/gen_low_all.py && bin/leanq Exp7Lean/SieveLow/All.lean
# proves `theorem Exp7.searchLow : Exp7.SearchLow`.
JOBS=${1:-1}
MAXSEC=${2:-0}
[ $# -gt 0 ] && shift
[ $# -gt 0 ] && shift
GENARGS="$@"
LEANQ=${LEANQ:-/home/zlab/GitHub/exp7-agents/bin/leanq}
KEEP=${KEEP:-1}
D=Exp7Lean/SieveLow
O=.lake/build/lib/lean/Exp7Lean/SieveLow
mkdir -p $D/logs $O
[ -f $O/Assembly.olean ] || $LEANQ --build Exp7Lean.SieveLow.Assembly || exit 1
START=$(date +%s)
one() {
  p=$1
  [ -f $O/P$p.olean ] && return 0
  if [ "$MAXSEC" -gt 0 ] && [ $(( $(date +%s) - START )) -gt "$MAXSEC" ]; then return 0; fi
  if [ ! -f $D/P$p.lean ] || [ ! -f $D/logs/P$p.gen ]; then
    python3 $D/gen_low.py $p $GENARGS > $D/logs/P$p.gen 2>&1 ||
      { echo "$p GENFAIL (see logs/P$p.gen)" >> $D/logs/times.txt; return 1; }
  fi
  /usr/bin/time -f "%U %e %M" -o $D/logs/P$p.time \
    $LEANQ $D/P$p.lean -o $O/P$p.olean.tmp -i $O/P$p.ilean.tmp > $D/logs/P$p.log 2>&1
  rc=$?
  if [ $rc -eq 0 ] &&
     grep -q "'Exp7.searchLow_$p' depends on axioms: \[propext, Classical.choice, Quot.sound\]" $D/logs/P$p.log &&
     ! grep -q "error\|sorry" $D/logs/P$p.log; then
    mv $O/P$p.olean.tmp $O/P$p.olean; mv $O/P$p.ilean.tmp $O/P$p.ilean
    echo "$p OK user_s elapsed_s maxrss_kb: $(tail -n 1 $D/logs/P$p.time) | $(grep '^STAT' $D/logs/P$p.gen)" >> $D/logs/times.txt
    command rm -f $D/logs/P$p.log $D/logs/P$p.time
    [ "$KEEP" = 0 ] && command rm -f $D/P$p.lean
  else
    command rm -f $O/P$p.olean.tmp $O/P$p.ilean.tmp
    echo "$p FAIL rc=$rc (see logs/P$p.log)" >> $D/logs/times.txt
  fi
}
export -f one
export MAXSEC START GENARGS LEANQ KEEP D O
if [ -n "$PRIMES" ]; then echo $PRIMES | tr ' ' '\n'
else python3 -c "print('\n'.join(str(p) for p in range(3, 2760) if all(p % d for d in range(2, int(p ** 0.5) + 1))))"
fi | xargs -P "$JOBS" -I{} bash -c 'one {}'
echo "done: $(ls $O | grep -c '^P[0-9]*\.olean$') of 401"
