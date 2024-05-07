#!/usr/bin/env bash

tests_dir="$(realpath -s "$(dirname "$0")")"
cd "$tests_dir/batteries"

output=$(mktemp)

lake clean
# TODO: Figure out how to keep the printed lines on a single line.
lake build | tee "$output" | egrep '^\[[0-9]+/[0-9]+\]' # | tr '\n' '\r'

success_count="$(cat "$output" | grep 'egg succeeded' | wc -l | awk '{$1=$1};1')"

prefix="warning: ./././."
failures="$(cat "$output" | grep -e 'egg failed' -e "declaration uses 'sorry'" | cut -c ${#prefix}-)"
fail_count="$(echo "$failures" | wc -l | awk '{$1=$1};1')"

echo "✅ $success_count    ❌ $fail_count"
echo "$failures"
