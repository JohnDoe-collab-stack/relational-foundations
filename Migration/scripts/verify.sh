#!/usr/bin/env bash
set -euo pipefail
project_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
exec pwsh -NoProfile -File "$project_root/scripts/verify-migration.ps1" "$@"
