#!/usr/bin/env bash

lean_dir="$(realpath -s "$(dirname "$0")")"
cd "$lean_dir"
find Egg -type f | grep -v -e 'Tests' -e '.DS_Store' -e 'Egg/Lean.lean' | tr "/" "." | sed 's/^/import /' | sed 's/\.lean$//' > "Egg.lean"