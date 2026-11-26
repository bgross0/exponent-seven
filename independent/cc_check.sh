#!/bin/sh
# Internal consistency at realistic scale: CRT enumeration vs testing every k,
# on p in [701,760] with the l-condition truncated to l < 60 (so survivors exist).
cd "$(dirname "$0")"
./search7i --pmin 701 --pmax 760 --lmax 60 --threads 12 --quiet > cc_auto.txt
./search7i --pmin 701 --pmax 760 --lmax 60 --threads 12 --quiet --no-wheel > cc_nowheel.txt
wc -l cc_auto.txt cc_nowheel.txt
if cmp -s cc_auto.txt cc_nowheel.txt; then echo "cc_check: IDENTICAL"; else echo "cc_check: DIFFERENT"; fi
