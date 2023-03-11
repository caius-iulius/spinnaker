#!/bin/sh

for file in examples/*.spk
do
    echo "########### Running test: $file"
    cabal run spinnaker -- --file $file --verbose | awk '/Unoptimized program size:/,0'
    echo "----"
    time bun run out.js
    echo "###########"
    echo ""
done
rm out.js
echo "Tests complete"
