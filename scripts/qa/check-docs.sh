#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$repo_root"

required_human=(
  README.adoc
  QUICK_STATUS.md
  GETTING_STARTED.md
  SPECIFICATION.md
  docs/README.md
  docs/wiki/Home.md
  docs/maintenance/MAINTENANCE-CHECKLIST.md
  docs/practice/SOFTWARE-DEVELOPMENT-APPROACH.adoc
)

required_machine=(
  .machine_readable/anchors/ANCHOR.a2ml
  .machine_readable/policies/MAINTENANCE-AXES.a2ml
  .machine_readable/policies/MAINTENANCE-CHECKLIST.a2ml
  .machine_readable/policies/SOFTWARE-DEVELOPMENT-APPROACH.a2ml
  .machine_readable/STATE.scm
  .machine_readable/META.scm
  .machine_readable/ECOSYSTEM.scm
  .machine_read/AUTHORITY_STACK.scm
  .machine_read/LLM_SUPERINTENDENT.scm
  .machine_readable/contractiles/trust/Trustfile.a2ml
  .machine_readable/contractiles/lust/Intentfile
)

for f in "${required_human[@]}"; do
  [[ -f "$f" ]] || { echo "missing human-readable doc: $f" >&2; exit 1; }
done

for f in "${required_machine[@]}"; do
  [[ -f "$f" ]] || { echo "missing machine-readable doc: $f" >&2; exit 1; }
done

if rg -n '\{\{PROJECT\}\}|\{\{project\}\}' src/abi docs/interop >/dev/null; then
  echo "template placeholders remain in ABI/interop docs" >&2
  exit 1
fi

# Validate AsciiDoc local link targets in README.
while IFS= read -r link; do
  path="${link#link:}"
  path="${path%%[*}"
  [[ "$path" =~ ^https?:// ]] && continue
  [[ "$path" =~ ^mailto: ]] && continue
  [[ -e "$path" ]] || { echo "broken README link target: $path" >&2; exit 1; }
done < <(grep -o 'link:[^[]*\[' README.adoc || true)

# Validate wiki markdown links that target local files.
while IFS='|' read -r file target; do
  [[ "$target" =~ ^https?:// ]] && continue
  [[ "$target" =~ ^mailto: ]] && continue
  [[ "$target" =~ ^# ]] && continue
  [[ "$target" =~ ^/ ]] && continue
  dir="$(dirname "$file")"
  resolved="$dir/$target"
  resolved="${resolved%%#*}"
  [[ -e "$resolved" ]] || { echo "broken wiki link: $file -> $target" >&2; exit 1; }
done < <(
  rg -n --no-heading '\[[^]]+\]\(([^)]+)\)' docs/wiki/*.md |
    sed -E 's#^([^:]+):[0-9]+:.*\]\(([^)]+)\).*#\1|\2#'
)

echo "documentation checks passed"
