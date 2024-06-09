#!/usr/bin/env bash

tests_dir="$(realpath -s "$(dirname "$0")")"
pkg_dir="$tests_dir/../../.."
module_prefix="Egg.Tests."
skip_prefix="WIP"

ci_mode=false
test_egg=false
test_batteries=false
test_mathlib=false
for arg in "$@"
do
    if [[ "$arg" == "--ci" ]]; then
        ci_mode=true
    elif [[ "$arg" == "--egg" ]]; then
        test_egg=true
    elif [[ "$arg" == "--batteries" ]]; then
        test_batteries=true
    elif [[ "$arg" == "--mathlib" ]]; then
        test_mathlib=true
    fi
done

cd "$pkg_dir"
exit_code=0

if [[ "$test_egg" == true ]]; then
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

                left_quote='«'
                right_quote='»'
                module_name="$module_prefix$left_quote$file_name$right_quote"
                output=$(lake build "$module_name" 2>&1)

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
fi

if [[ "$exit_code" -ne 0 ]]; then
    exit $exit_code
fi

test_lib () {
    cd "$tests_dir/$test_lib_name"
    local output=$(mktemp)
    local info_prefix="warning: ./././."

    lake clean
    # TODO: Figure out how to keep the printed lines on a single line.
    lake build | tee "$output" | egrep '^. \[[0-9]+/[0-9]+\]' # | tr '\n' '\r'

    local success_count="$(cat "$output" | grep 'egg succeeded' | wc -l | awk '{$1=$1};1')"
    local failures="$(cat "$output" | grep 'egg failed' | cut -c ${#info_prefix}-)"
    local fail_count="$(echo "$failures" | wc -l | awk '{$1=$1};1')"
    local unsupported="$(cat "$output" | grep "declaration uses 'sorry'" | cut -c ${#info_prefix}-)"
    local unsupported_count="$(echo "$unsupported" | wc -l | awk '{$1=$1};1')"

    echo "✅ $success_count    🟡 $unsupported_count    ❌ $fail_count"

    echo "$failures"    | while read fail; do echo "❌ $fail"; done
    echo "$unsupported" | while read unsupp; do echo "🟡 $unsupp"; done
}

if [[ "$test_batteries" == true ]]; then
    test_lib_name="batteries"
    test_lib
fi

if [[ "$test_mathlib" == true ]]; then
    test_lib_name="mathlib4"
    test_lib
fi
