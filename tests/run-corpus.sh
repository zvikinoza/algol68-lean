#!/bin/bash
# Run the differential test over the golden corpus produced by fetch-corpus.sh.
# Usage: run-corpus.sh [golden-list] [report-file]
ROOT=$(cd "$(dirname "$0")" && pwd)
LIST=${1:-$ROOT/corpus/golden.txt}
REPORT=${2:-$ROOT/corpus/report.txt}
"$ROOT/difftest.sh" "$LIST" "$ROOT/corpus" "$REPORT"
"$ROOT/classify.sh" "$REPORT"
