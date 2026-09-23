#!/usr/bin/env bash
# Fail unless AxiomAudit.lean audits exactly the comparator.json theorems and
# every one of them depends only on the permitted axioms.
set -euo pipefail

root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$root"

audited="$(awk '/^-- BEGIN AUDIT$/{on=1;next} /^-- END AUDIT$/{on=0} on{print $3}' AxiomAudit.lean | sort)"
listed="$(python3 -c 'import json; print("\n".join(json.load(open("comparator.json"))["theorem_names"]))' | sort)"
if [[ "$audited" != "$listed" ]]; then
  echo "error: AxiomAudit.lean names differ from comparator.json theorem_names" >&2
  diff <(echo "$audited") <(echo "$listed") >&2 || true
  exit 1
fi

permitted="$(python3 -c 'import json; print(" ".join(json.load(open("comparator.json"))["permitted_axioms"]))')"
output="$(lake env lean AxiomAudit.lean)"
echo "$output"

count="$(grep -c "depends on axioms\|does not depend on any axioms" <<<"$output" || true)"
expected="$(wc -l <<<"$listed" | tr -d ' ')"
if [[ "$count" != "$expected" ]]; then
  echo "error: expected $expected axiom reports, got $count" >&2
  exit 1
fi

bad=0
while IFS= read -r axiom; do
  [[ -z "$axiom" ]] && continue
  if [[ " $permitted " != *" $axiom "* ]]; then
    echo "error: non-permitted axiom $axiom" >&2
    bad=1
  fi
done < <(grep -o "depends on axioms: \[.*\]" <<<"$output" | sed -E 's/.*\[(.*)\]/\1/' | tr ',' '\n' | tr -d ' ')
exit "$bad"
