#!/bin/bash
# Summarize fate census TSVs in ~/collatz/results
cd ~/collatz/results || exit 1
for f in discoveries_*.log; do
  echo "=== $f ==="
  cat "$f"
done
for f in fate_*.tsv; do
  echo "=== $f ==="
  awk 'NR>1 {c1+=$3;c2+=$4;c3+=$5;c4+=$6;c5+=$7;c6+=$8;over+=$11;cap+=$12;t+=$3+$4+$5+$6+$7+$8+$9+$10+$11+$12}
       END {printf "N=%d  c1=%.6f c2=%.6f c3=%.6f c4=%d c5=%d c6=%d overflow=%.6f cap=%d\n", t, c1/t, c2/t, c3/t, c4, c5, c6, over/t, cap}' "$f"
  echo "  first/last block class shares:"
  awk 'NR==2 {tt=$3+$4+$5+$11; printf "  first base=%s: %.5f %.5f %.5f over=%.5f\n", $1,$3/tt,$4/tt,$5/tt,$11/tt}
       NR>1 {l1=$1;l3=$3;l4=$4;l5=$5;l11=$11}
       END {tt=l3+l4+l5+l11; if (tt>0) printf "  last  base=%s: %.5f %.5f %.5f over=%.5f\n", l1,l3/tt,l4/tt,l5/tt,l11/tt}' "$f"
done
