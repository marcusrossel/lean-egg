#!/usr/bin/env bash

batteries_dir="$(realpath -s "$(dirname "$0")")"
batteries_repo_dir="$batteries_dir/batteries"

# Sets a variable corresponding to the `--main` flag.
use_main_branch=false
for arg in "$@"
do
    if [[ "$arg" == "--main" ]]; then
        use_main_branch=true
    fi
done

# Fetches the Lean version used by egg (or uses `main` if the corresponding flag is given). 
if [[ "$use_main_branch" == true ]]; then
    lean_version="main"
else
    lean_toolchain_file="$batteries_dir/../../../../lean-toolchain"
    lean_toolchain="$(cat "$lean_toolchain_file")"
    lean_version="${lean_toolchain#*:}"
fi

# Clones the previously determined version of batteries.
cd "$batteries_dir"
git clone -b "$lean_version" --single-branch --depth 1 "https://github.com/leanprover-community/batteries.git" || { exit 1; }
cd "$batteries_repo_dir" || { exit 1; }
git switch -c egg-tests || { exit 1; }
git remote set-url origin "https://github.com/marcusrossel/batteries.git" || { exit 1; }

# Adds egg as a dependency to the `lakefile.toml`.
lakefile="$batteries_repo_dir/lakefile.toml"
toml_dep="\n[[require]]\nname = \"egg\"\npath = \"../../../../..\""
echo -e "$toml_dep" >> "$lakefile"

# Moves `SimpOnlyOverride.lean` to its intended destination.
simp_only_override="$batteries_dir/SimpOnlyOverride.lean"
simp_only_override_dst="$batteries_repo_dir/Batteries/Test/Egg"
mkdir "$simp_only_override_dst"
cp "$simp_only_override" "$simp_only_override_dst"

# Adds an import statement for the simp only override to each `.lean` file,
# except a few select ones.
import_statement="import Batteries.Test.Egg.SimpOnlyOverride"
cd "$batteries_repo_dir"
targets="$(find Batteries -type f | grep -v -e 'SimpOnlyOverride.lean$' -e '.DS_Store')" || { exit 1; }

while IFS= read -r file; do
    echo "$import_statement"$'\n'$"$(cat $file)" > "$file"
done <<< "$targets"

# Preparation for `lake build`.
cd "$batteries_repo_dir"
lake update