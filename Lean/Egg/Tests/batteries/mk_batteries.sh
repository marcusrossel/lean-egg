#!/usr/bin/env bash

batteries_dir="$(realpath -s "$(dirname "$0")")"
batteries_repo_dir="$batteries_dir/batteries"

# Fetches the Lean version used by egg and clones the corresponding version of batteries.
lean_toolchain_file="$batteries_dir/../../../../lean-toolchain"
lean_toolchain="$(cat "$lean_toolchain_file")"
lean_version="${lean_toolchain#*:}"
cd "$batteries_dir"
git clone -b "bump-$lean_version" "https://github.com/leanprover-community/batteries.git"
cd "$batteries_repo_dir"
git remote set-url origin "https://github.com/marcusrossel/batteries.git"

# TODO: Starting with the next version of batteries, use this toml-based dependency code instead of the lakefile.lean-based one below.
# Adds egg as a dependency to the `lakefile.toml`.
# lakefile="$batteries_repo_dir/lakefile.toml"
# toml_dep="\n[[require]]\nname = \"egg\"\npath = \"../../../../..\""
# echo -e "$toml_dep" >> "$lakefile"

# Adds egg as a dependency to the `lakefile.lean`.
lakefile="$batteries_repo_dir/lakefile.lean"
dep="require egg from \"../../../../..\""
echo -e "$dep" >> "$lakefile"

# Moves `SimpOnlyOverride.lean` to its intended destination.
simp_only_override="$batteries_dir/SimpOnlyOverride.lean"
simp_only_override_dst="$batteries_repo_dir/Batteries/Test/Egg"
mkdir "$simp_only_override_dst"
cp "$simp_only_override" "$simp_only_override_dst"

# Adds an import statement for the simp only override to each `.lean` file,
# except a few select ones.
import_statement="import Batteries.Test.Egg.SimpOnlyOverride"
cd "$batteries_repo_dir"
targets="$(find Batteries -type f | grep -v -e 'SimpOnlyOverride.lean$' -e '.DS_Store')"

while IFS= read -r file; do
    echo -e "$import_statement\n$(cat $file)" > "$file"
done <<< "$targets"

# Preparation for `lake build`.
cd "$batteries_repo_dir"
lake update