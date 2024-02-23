#!/bin/bash

tests_dir="$(realpath -s "$(dirname "$0")")"
pkg_dir="${tests_dir}/../../.."
module_prefix="Egg.Tests."

cd "$pkg_dir"

for file in "$tests_dir"/*; do
    if [[ -f "$file" ]]; then
        if [[ "$file" == *".lean" ]]; then
            file_name=$(basename "$file" ".lean")
            module_name="${module_prefix}${file_name}"
            
            echo -n "Testing ${file_name} ..."
            lake build $module_name >/dev/null 2>&1

            if [[ $? -eq 0 ]]; then
                if grep -q "sorry" "$file"; then
                    echo -e "\r🟡 ${file_name}          "
                else
                    echo -e "\r✅ ${file_name}          "
                fi
            else
                echo -e "\r❌ ${file_name}          "
            fi
        fi
    fi
done