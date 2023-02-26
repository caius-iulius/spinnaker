#!/bin/sh

for file in examples/*.spk
do
    echo "########### Running test: $file"
    cabal run spinnaker -- $file -v | awk '/Unoptimized program size:/,0'
    echo "###########"
    echo ""
done
echo "Tests complete"
