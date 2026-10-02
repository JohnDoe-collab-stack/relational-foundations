#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

if command -v lake >/dev/null 2>&1; then
  lake_command=(lake)
elif [[ -x "$HOME/.elan/bin/lake" ]]; then
  lake_command=("$HOME/.elan/bin/lake")
elif [[ -n "${USERPROFILE:-}" ]] && command -v cygpath >/dev/null 2>&1 &&
    [[ -x "$(cygpath -u "$USERPROFILE")/.elan/bin/lake.exe" ]]; then
  lake_command=("$(cygpath -u "$USERPROFILE")/.elan/bin/lake.exe")
else
  echo 'lake was not found in PATH or in the default elan installation' >&2
  exit 1
fi

# One shared inventory; classification records what a fixture actually tests.
manifest="scripts/expected-failures.tsv"
declare -A expected category
fixtures=()
while IFS=$'\t' read -r fixture kind diagnostic extra; do
  fixture="${fixture%$'\r'}"; kind="${kind%$'\r'}"; diagnostic="${diagnostic%$'\r'}"
  [[ -z "$fixture" || "${fixture:0:1}" == '#' ]] && continue
  [[ -z "${extra:-}" && -n "$diagnostic" ]] || { echo 'invalid expected-failure inventory row' >&2; exit 1; }
  [[ "$fixture" == Tests/ExpectedFailure/*.lean.fail && "$fixture" != *'..'* ]] || { echo "invalid fixture path: $fixture" >&2; exit 1; }
  [[ -z "${expected[$fixture]+x}" ]] || { echo "duplicate fixture: $fixture" >&2; exit 1; }
  [[ " privacy dependent-type semantic-type termination " == *" $kind "* ]] || { echo "unknown fixture category: $kind" >&2; exit 1; }
  [[ -f "$fixture" ]] || { echo "orphan fixture entry: $fixture" >&2; exit 1; }
  fixtures+=("$fixture"); expected[$fixture]="$diagnostic"; category[$fixture]="$kind"
done < "$manifest"
mapfile -t actual < <(find Tests/ExpectedFailure -type f -name '*.lean.fail' | LC_ALL=C sort)
[[ ${#fixtures[@]} -gt 0 ]] || { echo 'empty expected-failure inventory' >&2; exit 1; }
for fixture in "${actual[@]}"; do
  [[ -n "${expected[$fixture]+x}" ]] || { echo "uninventoried fixture: $fixture" >&2; exit 1; }
done
[[ ${#actual[@]} -eq ${#fixtures[@]} ]] || { echo 'fixture inventory mismatch' >&2; exit 1; }
for fixture in "${fixtures[@]}"; do
  set +e
  output="$("${lake_command[@]}" env lean "$fixture" 2>&1)"
  status=$?
  set -e
  [[ "$status" != 0 ]] || { echo "$fixture: unexpectedly compiled" >&2; exit 1; }
  # Signals and conventional timeout codes are not compiler rejections.
  [[ "$status" -lt 124 ]] || { echo "$fixture: interrupted or timed out ($status)" >&2; exit 1; }
  if [[ "$output" != *"${expected[$fixture]}"* ]]; then
    echo "$fixture: failed for an unexpected reason" >&2
    echo "$output" >&2
    exit 1
  fi
  printf 'EXPECTED_FAILURE_OK\t%s\t%s\n' "${category[$fixture]}" "$fixture"
done
printf 'Verified expected failures: %s fixtures, each executed once; privacy, dependent-type, semantic-type and termination remain distinct.\n' "${#fixtures[@]}"
