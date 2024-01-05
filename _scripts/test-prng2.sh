#!/usr/bin/env bash

OUT=./out.txt
echo '# test-prng2.sh' >$OUT

for n in 10000 100000 1000000 10000000; do
  echo quint run --invariant=safety --max-samples=$n ./specs/prng2.qnt >>$OUT
  quint run --invariant=safety --max-samples=$n ./specs/prng2.qnt >>$OUT
  echo quint run --invariant=missingOutput --max-samples=$n ./specs/prng2.qnt >>$OUT
  quint run --invariant=missingOutput --max-samples=$n ./specs/prng2.qnt >>$OUT
done
