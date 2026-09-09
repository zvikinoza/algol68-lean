#!/bin/bash
# Re-run only the programs that did not pass in a previous difftest report, writing a new report
# in which the passing lines of the old report are kept.  Usage: rerun-failures.sh OLD NEW ROOT
OLD=$1; NEW=$2; ROOT=$3
ROOTDIR=$(cd "$(dirname "$0")" && pwd)
grep '^PASS' "$OLD" > "$NEW"
grep -v '^PASS' "$OLD" | awk '{print $2}' | while read -r name; do
  d=$(find "$ROOT" -maxdepth 3 -type d -name "$name" | head -1)
  echo "$d"
done > "$NEW.list"
"$ROOTDIR/difftest.sh" "$NEW.list" "$ROOT" "$NEW.delta"
cat "$NEW.delta" >> "$NEW"
rm -f "$NEW.list" "$NEW.delta"
echo "pass=$(grep -c '^PASS' "$NEW") total=$(wc -l < "$NEW")"
