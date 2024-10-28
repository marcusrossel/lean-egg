#!/usr/bin/env bash

mathlib_dir="$(realpath -s "$(dirname "$0")")"
mathlib_repo_dir="$mathlib_dir/mathlib4"

# Sets a variable corresponding to the `--main` flag.
use_main_branch=false
for arg in "$@"
do
    if [[ "$arg" == "--main" ]]; then
        use_main_branch=true
    fi
done

# Fetches the Lean version used by egg (or uses `master` if the corresponding flag is given). 
if [[ "$use_main_branch" == true ]]; then
    lean_version="master"
else
    lean_toolchain_file="$mathlib_dir/../../../../lean-toolchain"
    lean_toolchain="$(cat "$lean_toolchain_file")"
    lean_version="${lean_toolchain#*:}"
fi

# Clones the previously determined version of mathlib.
cd "$mathlib_dir"
git clone -b "$lean_version" --single-branch --depth 1 "https://github.com/leanprover-community/mathlib4.git" || { exit 1; }
cd "$mathlib_repo_dir" || { exit 1; }
git switch -c egg-tests || { exit 1; }
git remote set-url origin "https://github.com/marcusrossel/mathlib4.git" || { exit 1; }

# Adds egg as a dependency to the `lakefile.lean`.
lakefile="$mathlib_repo_dir/lakefile.lean"
dep="\nrequire egg from \"../../../../..\""
echo -e "$dep" >> "$lakefile"

# Sets `linter.style.header` to `false` in `lakefile.lean`.
header_option_true='⟨`linter.style.header, true⟩'
header_option_false='⟨`linter.style.header, false⟩'
sed -i -e "s/$header_option_true/$header_option_false/" "$lakefile"

# Moves `SimpOnlyOverride.lean` to its intended destination.
simp_only_override="$mathlib_dir/SimpOnlyOverride.lean"
simp_only_override_dst="$mathlib_repo_dir/Mathlib/Testing/Egg"
mkdir "$simp_only_override_dst"
cp "$simp_only_override" "$simp_only_override_dst"

# Adds an import statement for the simp only override to each `.lean` file,
# except a few select ones.
import_statement="import Mathlib.Testing.Egg.SimpOnlyOverride"
cd "$mathlib_repo_dir"
targets="$(find Mathlib -type f | grep -v -e 'SimpOnlyOverride.lean$' -e '.DS_Store')" || { exit 1; }

while IFS= read -r file; do
    echo "$import_statement"$'\n'$"$(cat $file)" > "$file"
done <<< "$targets"

# Preparation for `lake build`.
cd "$mathlib_repo_dir"
lake update