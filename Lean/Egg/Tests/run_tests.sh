#!/usr/bin/env bash

tests_dir="$(realpath -s "$(dirname "$0")")"
pkg_dir="$tests_dir/../../.."
module_prefix="Egg.Tests."
skip_prefix="WIP"

ci_mode=false
profile_mode=false
test_egg=false
test_batteries=false
test_mathlib=false
for arg in "$@"
do
    if [[ "$arg" == "--ci" ]]; then
        ci_mode=true
    elif [[ "$arg" == "--profile" ]]; then
        profile_mode=true
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

summarize_lib_tests() {
    local warning_prefix="warning: ././././Batteries/"
    local success_prefix="egg succeeded"
    local plain_fail_prefix="egg failed: egg failed to prove the goal"

    if [[ "$profile_mode" == true ]]; then 
        success_prefix="$success_prefix "
        plain_fail_prefix="$plain_fail_prefix "

        local successes="$(cat "$test_lib_output" | grep -o "$success_prefix(.*)" | cut -c ${#success_prefix}-)"
        local plain_failures="$(cat "$test_lib_output" | grep -o "$plain_fail_prefix(.*) (.*)" | cut -c ${#plain_fail_prefix}-)"
    else
        local successes="$(cat "$test_lib_output" | grep "$success_prefix")"
        local plain_failures="$(cat "$test_lib_output" | grep "$plain_fail_prefix" | cut -c ${#warning_prefix}-)"
    fi

    local errors="$(cat "$test_lib_output" | grep 'egg failed:' | grep -v 'egg failed: egg failed to prove the goal' | cut -c ${#warning_prefix}-)"
    local unsupported="$(cat "$test_lib_output" | grep "declaration uses 'sorry'" | cut -c ${#warning_prefix}-)"

    local success_count="$(echo "$successes" | wc -l | awk '{$1=$1};1')"
    local plain_fail_count="$(echo "$plain_failures" | wc -l | awk '{$1=$1};1')"
    local errors_count="$(echo "$errors" | wc -l | awk '{$1=$1};1')"
    local unsupported_count="$(echo "$unsupported" | wc -l | awk '{$1=$1};1')"

    echo "✅ $success_count    ❌ $plain_fail_count    🟪 $errors_count    🟡 $unsupported_count"

    if [[ "$profile_mode" == true ]]; then 
        echo "$successes"      | while read success; do echo "✅ $success"; done
    fi

    echo "$plain_failures" | while read fail; do echo "❌ $fail"; done
    echo "$errors"         | while read error; do echo "🟪 $error"; done
    echo "$unsupported"    | while read unsupp; do echo "🟡 $unsupp"; done
}

test_lib() {
    cd "$tests_dir/$test_lib_name"
    test_lib_output=$(mktemp)

    lake clean
    # TODO: Figure out how to keep the printed lines on a single line.
    lake build | tee "$test_lib_output" | egrep '^. \[[0-9]+/[0-9]+\]' # | tr '\n' '\r'   
}

if [[ "$test_batteries" == true ]]; then
    test_lib_name="batteries"
    trap summarize_lib_tests EXIT
    test_lib
fi

if [[ "$test_mathlib" == true ]]; then
    test_lib_name="mathlib4"
    trap summarize_lib_tests EXIT
    test_lib
fi
