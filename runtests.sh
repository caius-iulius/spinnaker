#!/bin/sh

for file in examples/*.spk
do
    echo "########### Running test: $file"
    cabal run spinnaker -- $file -v | awk '/Unoptimized program size:/,0'
    cat spinnaker.js out.js > out_stitched.js
    echo "----"
    time node out_stitched.js
    echo "###########"
    echo ""
done
rm out.js out_stitched.js
echo "Tests complete"
