#!/usr/bin/env bash

tests_dir="$(realpath -s "$(dirname "$0")")"
cd "$tests_dir/batteries"

output=$(mktemp)
info_prefix="warning: ./././."

lake clean
# TODO: Figure out how to keep the printed lines on a single line.
lake build | tee "$output" | egrep '^\[[0-9]+/[0-9]+\]' # | tr '\n' '\r'

success_count="$(cat "$output" | grep 'egg succeeded' | wc -l | awk '{$1=$1};1')"
failures="$(cat "$output" | grep 'egg failed' | cut -c ${#info_prefix}-)"
fail_count="$(echo "$failures" | wc -l | awk '{$1=$1};1')"
unsupported="$(cat "$output" | grep "declaration uses 'sorry'" | cut -c ${#info_prefix}-)"
unsupported_count="$(echo "$unsupported" | wc -l | awk '{$1=$1};1')"

echo "✅ $success_count    🟡 $unsupported_count    ❌ $fail_count"

echo "$failures"    | while read fail; do echo "❌ $fail"; done
echo "$unsupported" | while read unsupp; do echo "🟡 $unsupp"; done
