#!/usr/bin/env bash

# Check for --noclean flag
if [[ "$1" != "--noclean" ]]; then
    echo -n "Clean building..."
    (cd ../../.. && lake clean && lake build)
    (cd Math && lake clean && lake exec cache get && lake build)
fi

echo -e "\rSource,Total Time (ms),Eqsat Time (ms),Proof Time (ms),Iterations,E-Nodes,E-Classes,Explanation Length"

for file in *.lean; do
    name="${file%.lean}"
    module="Egg.Benchmarks.«${name}»"
    (cd ../../.. && lake build "$module")
done

cd Math/Math

for file in *.lean; do
    name="${file%.lean}"
    module="Math.«${name}»"
    (cd .. && lake build "$module")
done
