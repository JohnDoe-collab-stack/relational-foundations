#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
manifest="scripts/stratification.tsv"

lean_imports() {
  awk '
    BEGIN { block = 0; in_string = 0; escaped = 0; awaiting = 0 }
    {
      source = $0 "\n"
      clean = ""
      line_comment = 0
      for (i = 1; i <= length(source); i++) {
        current = substr(source, i, 1)
        nextc = (i < length(source) ? substr(source, i + 1, 1) : "")
        if (line_comment) {
          if (current == "\n") clean = clean "\n"
          else clean = clean " "
        } else if (block > 0) {
          if (current == "/" && nextc == "-") {
            clean = clean "  "; block++; i++
          } else if (current == "-" && nextc == "/") {
            clean = clean "  "; block--; i++
          } else {
            clean = clean (current == "\n" ? "\n" : " ")
          }
        } else if (in_string) {
          clean = clean current
          if (escaped) escaped = 0
          else if (current == "\\") escaped = 1
          else if (current == "\"") in_string = 0
        } else if (current == "-" && nextc == "-") {
          clean = clean "  "; line_comment = 1; i++
        } else if (current == "/" && nextc == "-") {
          clean = clean "  "; block = 1; i++
        } else {
          clean = clean current
          if (current == "\"") in_string = 1
        }
      }
      sub(/\n$/, "", clean)
      trimmed = clean
      sub(/^[ \t\r]+/, "", trimmed)
      sub(/[ \t\r]+$/, "", trimmed)
      if (awaiting && trimmed == "") next
      if (awaiting) {
        if (match(trimmed, /^[A-Z][A-Za-z0-9_'\''.]*/)) print substr(trimmed, RSTART, RLENGTH)
        awaiting = 0
      }
      if (match(clean, /^[ \t]*import[ \t]*/)) {
        rest = substr(clean, RLENGTH + 1)
        sub(/^[ \t]+/, "", rest)
        if (rest == "" || rest == "\r") awaiting = 1
        else if (match(rest, /^[A-Z][A-Za-z0-9_'\''.]*/)) print substr(rest, RSTART, RLENGTH)
      }
    }
    END { if (block != 0) exit 3 }
  ' "$1"
}

if [[ "${1:-}" == "--self-test" ]]; then
  fixture="$(mktemp)"
  trap 'rm -f "$fixture"' EXIT
  printf '%s\n' \
    '/- import Forbidden.Direct /- import Forbidden.Nested -/ -/' \
    '-- import Forbidden.Line' \
    'import' \
    '  Allowed.Split' \
    '/- comment -/' \
    'import Allowed.Direct -- import Forbidden.Trailing' > "$fixture"
  mapfile -t actual < <(lean_imports "$fixture")
  [[ "${actual[*]}" == 'Allowed.Split Allowed.Direct' ]] || {
    echo "stratification parser self-test failed: ${actual[*]}" >&2
    exit 1
  }
  exit 0
fi

declare -A stratum status responsibility file_for imports
line_number=0
while IFS=$'\t' read -r module layer migration role extra; do
  line_number=$((line_number + 1))
  module="${module%$'\r'}"; layer="${layer%$'\r'}"; migration="${migration%$'\r'}"; role="${role%$'\r'}"
  [[ -z "$module" || "${module:0:1}" == '#' ]] && continue
  [[ -z "${extra:-}" && -n "$role" ]] || { echo "$manifest:$line_number: expected four tab-separated fields" >&2; exit 1; }
  [[ -z "${stratum[$module]+x}" ]] || { echo "$manifest:$line_number: duplicate module $module" >&2; exit 1; }
  [[ " U F G S B E M R X P K D Q N A0 A1 A2 A3 A4 A5 A6 A7 A8 A9 " == *" $layer "* ]] || { echo "$manifest:$line_number: unknown stratum $layer" >&2; exit 1; }
  [[ "$migration" == enforced ]] || { echo "$manifest:$line_number: every production module must be enforced, found $migration" >&2; exit 1; }
  stratum[$module]="$layer"; status[$module]="$migration"; responsibility[$module]="$role"
done < "$manifest"

mapfile -t tracked_production_files < <(git ls-files --cached --others --exclude-standard -- '*.lean' | grep -v '^Tests/' | sort)
production_files=()
for relative in "${tracked_production_files[@]}"; do
  [[ -f "$relative" ]] || continue
  production_files+=("$relative")
done
for relative in "${production_files[@]}"; do
  module="${relative%.lean}"; module="${module//\//.}"; module="${module//\\/.}"
  file_for[$module]="$relative"
  mapfile -t direct < <(lean_imports "$relative")
  imports[$module]="$(printf '%s\n' "${direct[@]:-}")"
done

missing=(); stale=()
for module in "${!file_for[@]}"; do [[ -n "${stratum[$module]+x}" ]] || missing+=("$module"); done
for module in "${!stratum[@]}"; do [[ -n "${file_for[$module]+x}" ]] || stale+=("$module"); done
[[ ${#missing[@]} -eq 0 ]] || { echo "unclassified production modules: ${missing[*]}" >&2; exit 1; }
[[ ${#stale[@]} -eq 0 ]] || { echo "manifest modules without source: ${stale[*]}" >&2; exit 1; }

allowed_dependency() {
  case "$1" in
    U) [[ "$2" == U ]] ;;
    F) [[ " U F " == *" $2 "* ]] ;;
    G) [[ " U G " == *" $2 "* ]] ;;
    S) [[ " U G S " == *" $2 "* ]] ;;
    B) [[ " U F G S B " == *" $2 "* ]] ;;
    E) [[ " U G S B E " == *" $2 "* ]] ;;
    M) [[ " U G S B E M " == *" $2 "* ]] ;;
    R) [[ " U F G S B E R " == *" $2 "* ]] ;;
    X) [[ " U G S R X " == *" $2 "* ]] ;;
    P) [[ " U G S E R X P " == *" $2 "* ]] ;;
    K) [[ " U K " == *" $2 "* ]] ;;
    D) [[ " U G S E R X P K D " == *" $2 "* ]] ;;
    Q) [[ " U F G S B E M R X P K D Q " == *" $2 "* ]] ;;
    N) [[ " U G S B E M R X P K D Q N " == *" $2 "* ]] ;;
    A0) [[ " U F G S B E M R X P K D Q N " == *" $2 "* ]] ;;
    A1) [[ " U F G S B E M R X P K D Q N A0 " == *" $2 "* ]] ;;
    A2) [[ " U F G S B E M R X P K D Q N A0 A1 " == *" $2 "* ]] ;;
    A3) [[ " U F G S B E M R X P K D Q N A0 A1 A2 " == *" $2 "* ]] ;;
    A4) [[ " U F G S B E M R X P K D Q N A0 A1 A2 A3 " == *" $2 "* ]] ;;
    A5) [[ " U F G S B E M R X P K D Q N A0 A1 A2 A3 A4 " == *" $2 "* ]] ;;
    A6) [[ " U F G S B E M R X P K D Q N A0 A1 A2 A3 A4 A5 " == *" $2 "* ]] ;;
    A7) [[ " U F G S B E M R X P K D Q N A0 A1 A2 A3 A4 A5 A6 " == *" $2 "* ]] ;;
    A8) [[ " U F G S B E M R X P K D Q N A0 A1 A2 A3 A4 A5 A6 A7 " == *" $2 "* ]] ;;
    A9) [[ " U F G S B E M R X P K D Q N A0 A1 A2 A3 A4 A5 A6 A7 A8 " == *" $2 "* ]] ;;
    *) return 1 ;;
  esac
}

for root in "${!stratum[@]}"; do
  queue=("$root"); head=0
  declare -A seen_path=(["$root"]="$root")
  while (( head < ${#queue[@]} )); do
    current="${queue[$head]}"; head=$((head + 1))
    while IFS= read -r dependency; do
      [[ -n "$dependency" && -n "${stratum[$dependency]+x}" ]] || continue
      path="${seen_path[$current]} -> $dependency"
      allowed_dependency "${stratum[$current]}" "${stratum[$dependency]}" || {
        echo "forbidden stratification path (${stratum[$current]} -> ${stratum[$dependency]}): $path" >&2
        exit 1
      }
      if [[ -z "${seen_path[$dependency]+x}" ]]; then seen_path[$dependency]="$path"; queue+=("$dependency"); fi
    done <<< "${imports[$current]}"
  done
  unset seen_path
done

public_roots=(SegmentedResidualRole AbstractSegmentedTurning ExactTypeTransport StrongPerimetralTurning RelationalPerimeter)
declare -A reachable=()
queue=(); head=0
for root in "${public_roots[@]}"; do
  [[ -n "${stratum[$root]+x}" ]] || { echo "missing public root in manifest: $root" >&2; exit 1; }
  reachable[$root]=1; queue+=("$root")
done
while (( head < ${#queue[@]} )); do
  current="${queue[$head]}"; head=$((head + 1))
  while IFS= read -r dependency; do
    [[ -n "$dependency" && -n "${stratum[$dependency]+x}" ]] || continue
    if [[ -z "${reachable[$dependency]+x}" ]]; then reachable[$dependency]=1; queue+=("$dependency"); fi
  done <<< "${imports[$current]}"
done
orphans=()
for module in "${!stratum[@]}"; do [[ -n "${reachable[$module]+x}" ]] || orphans+=("$module"); done
[[ ${#orphans[@]} -eq 0 ]] || { echo "production modules unreachable from public Lake roots: ${orphans[*]}" >&2; exit 1; }

echo "Verified stratification inventory: ${#stratum[@]} production modules, all enforced, no orphan."
