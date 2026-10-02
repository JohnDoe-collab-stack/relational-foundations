#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

check_graph() {
  local source_root="$1"
  local manifest="$2"
  shift 2
  local -a files=("$@")
  local root_module=""
  local kind module
  local -A forbidden=()
  while read -r kind module; do
    [[ -z "${kind:-}" || "$kind" == \#* ]] && continue
    case "$kind" in
      root) root_module="$module" ;;
      forbidden) forbidden["$module"]=1 ;;
      *) echo "$manifest: unknown boundary entry '$kind'" >&2; return 2 ;;
    esac
  done < "$manifest"
  if [[ -z "$root_module" ]]; then
    echo "$manifest: missing root entry" >&2
    return 2
  fi

  local -A local_module=()
  local -A imports=()
  local file relative module_name line targets target
  for file in "${files[@]}"; do
    relative="${file#"$source_root"/}"
    module_name="${relative%.lean}"
    module_name="${module_name//\//.}"
    module_name="${module_name//\\/.}"
    local_module["$module_name"]=1
    imports["$module_name"]=""
    while IFS= read -r line || [[ -n "$line" ]]; do
      line="${line%$'\r'}"
      if [[ "$line" =~ ^[[:space:]]*import[[:space:]]+(.+)$ ]]; then
        targets="${BASH_REMATCH[1]%%--*}"
        for target in $targets; do
          imports["$module_name"]+=" $target"
        done
      fi
    done < "$file"
  done

  if [[ -z "${local_module[$root_module]:-}" ]]; then
    echo "$manifest: root module '$root_module' has no local source" >&2
    return 2
  fi

  local -a queue=("$root_module")
  local cursor=0 current dependency
  local -A visited=(["$root_module"]=1)
  local -A path=(["$root_module"]="$root_module")
  while (( cursor < ${#queue[@]} )); do
    current="${queue[$cursor]}"
    ((cursor += 1))
    for dependency in ${imports[$current]:-}; do
      [[ -z "${local_module[$dependency]:-}" ]] && continue
      if [[ -n "${forbidden[$dependency]:-}" ]]; then
        echo "forbidden import path: ${path[$current]} -> $dependency" >&2
        return 1
      fi
      if [[ -z "${visited[$dependency]:-}" ]]; then
        visited["$dependency"]=1
        path["$dependency"]="${path[$current]} -> $dependency"
        queue+=("$dependency")
      fi
    done
  done
}

if [[ "${1:-}" == "--self-test" ]]; then
  fixture="$(mktemp -d)"
  trap 'rm -rf -- "$fixture"' EXIT
  printf 'import Middle\n' > "$fixture/Root.lean"
  printf 'import Forbidden\n' > "$fixture/Middle.lean"
  printf '/- fixture -/\n' > "$fixture/Forbidden.lean"
  printf 'root Root\nforbidden Forbidden\n' > "$fixture/boundaries.txt"
  mapfile -t fixture_files < <(find "$fixture" -maxdepth 1 -type f -name '*.lean' -print | sort)
  set +e
  fixture_output="$(check_graph "$fixture" "$fixture/boundaries.txt" "${fixture_files[@]}" 2>&1)"
  fixture_status=$?
  set -e
  expected='forbidden import path: Root -> Middle -> Forbidden'
  if [[ "$fixture_status" != 1 || "$fixture_output" != "$expected" ]]; then
    echo "indirect import-boundary self-test failed" >&2
    echo "$fixture_output" >&2
    exit 1
  fi

  printf 'import Forbidden\n' > "$fixture/Root.lean"
  set +e
  fixture_output="$(check_graph "$fixture" "$fixture/boundaries.txt" "${fixture_files[@]}" 2>&1)"
  fixture_status=$?
  set -e
  expected='forbidden import path: Root -> Forbidden'
  if [[ "$fixture_status" != 1 || "$fixture_output" != "$expected" ]]; then
    echo "direct import-boundary self-test failed" >&2
    echo "$fixture_output" >&2
    exit 1
  fi
  exit 0
fi

cd "$repo_root"
manifest_argument="${1:-scripts/import-boundaries.txt}"
if [[ "$manifest_argument" = /* ]]; then
  manifest_path="$manifest_argument"
else
  manifest_path="$repo_root/$manifest_argument"
fi
mapfile -t tracked_lean < <(git ls-files --cached --others --exclude-standard -- '*.lean' | sort)
files=()
for file in "${tracked_lean[@]}"; do
  [[ -f "$repo_root/$file" ]] || continue
  files+=("$repo_root/$file")
done
check_graph "$repo_root" "$manifest_path" "${files[@]}"
