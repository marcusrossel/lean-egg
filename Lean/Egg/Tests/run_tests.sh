#!/usr/bin/env bash

tests_dir="$(realpath -s "$(dirname "$0")")"
pkg_dir="$tests_dir/../../.."
module_prefix="Egg.Tests."
skip_prefix="WIP"

ci_mode=false
for arg in "$@"
do
    if [ "$arg" == "--ci" ]
    then
        ci_mode=true
        break
    fi
done

cd "$pkg_dir"
exit_code=0

for file in "$tests_dir"/*; do
    if [[ -f "$file" ]]; then
        if [[ "$file" == *".lean" ]]; then
            file_name=$(basename "$file" ".lean")

            if [[ "$file_name" == "$skip_prefix"* ]]; then
                continue
            fi

            if [[ "$ci_mode" == true ]]; then 
                : 
            else
                echo -n "Testing $file_name ..."
            fi
            
            module_name="$module_prefix$file_name"
            output=$(lake build $module_name 2>&1)

            if [[ $? -eq 0 ]]; then
                if grep -q "sorry" "$file"; then
                    echo -e "\r🟡 $file_name            "
                else
                    echo -e "\r✅ $file_name            "
                fi
            else
		        exit_code=1
                echo -e "\r❌ $file_name           "

                if [[ "$ci_mode" == true ]]; then 
                    echo "$output" | while IFS= read -r line; do
                        echo "  ${line}"
                    done
                fi
		    fi
        fi
    fi
done

exit $exit_code
