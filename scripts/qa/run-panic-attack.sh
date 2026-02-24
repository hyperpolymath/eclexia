#!/usr/bin/env bash
set -euo pipefail

if [ "$#" -ge 1 ]; then
  out_file="$1"
else
  out_file="$(mktemp /tmp/eclexia-panic-attack.XXXXXX.json)"
fi

panic_attack_bin=""

if command -v panic-attack >/dev/null 2>&1; then
  panic_attack_bin="$(command -v panic-attack)"
elif [ -x "/var/mnt/eclipse/repos/panic-attacker/target/release/panic-attack" ]; then
  panic_attack_bin="/var/mnt/eclipse/repos/panic-attacker/target/release/panic-attack"
elif [ -x "../panic-attacker/target/release/panic-attack" ]; then
  panic_attack_bin="../panic-attacker/target/release/panic-attack"
fi

if [ -z "$panic_attack_bin" ]; then
  echo "panic-attack is not installed or not on PATH" >&2
  echo "build it in /var/mnt/eclipse/repos/panic-attacker first" >&2
  exit 2
fi

"$panic_attack_bin" assail . --output "$out_file"

echo "panic-attack report written to $out_file"
