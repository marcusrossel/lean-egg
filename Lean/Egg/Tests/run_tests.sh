#!/usr/bin/env bash

tests_dir="$(realpath -s "$(dirname "$0")")"
pkg_dir="${tests_dir}/../../.."
module_prefix="Egg.Tests."
expected_fail="WIP"

cd "$pkg_dir"

status=0

for file in "$tests_dir"/*; do
    if [[ -f "$file" ]]; then
        if [[ "$file" == *".lean" ]]; then
            file_name=$(basename "$file" ".lean")
            module_name="${module_prefix}${file_name}"
            
            echo -n "Testing ${file_name} ..."
            lake build $module_name >/dev/null 2>&1

            if [[ $? -eq 0 ]]; then
                if grep -q "sorry" "$file"; then
                    echo -e "\r🟡 ${file_name}            "
                else
                    echo -e "\r✅ ${file_name}            "
                fi
            else
		expected=0
                for name in $expected_fail; do
                  if [ "$name" = "$file_name" ]; then
		    expected=1
		    echo -e "\r❌ ${file_name} (expected)"
                    break
                  fi
                done
		if [[ $expected -eq 0 ]]; then
		        echo -e "\r❌ ${file_name}           "
			status=1
		fi
            fi
        fi
    fi
done

exit $status
