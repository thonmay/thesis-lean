#!/usr/bin/env bash
# Fail unless the definitions block of Challenge.lean is byte-identical to the
# one in ThesisLean/ChallengeDefs.lean (the module Solution.lean imports).
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
challenge="$root/Challenge.lean"
defs="$root/ThesisLean/ChallengeDefs.lean"

extract() {
  awk '/^-- BEGIN DEFS$/{on=1} on{print} /^-- END DEFS$/{on=0}' "$1"
}

for f in "$challenge" "$defs"; do
  if [[ -z "$(extract "$f")" ]]; then
    echo "error: no BEGIN DEFS/END DEFS block in $f" >&2
    exit 1
  fi
done

if ! diff <(extract "$challenge") <(extract "$defs"); then
  echo "error: Challenge.lean definitions differ from ThesisLean/ChallengeDefs.lean" >&2
  exit 1
fi
echo "Challenge.lean definitions match ThesisLean/ChallengeDefs.lean"
