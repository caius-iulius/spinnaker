#!/bin/sh

for i in "$@"    # same as your "for i"
do
    echo "########### Running test: $i"
    ./run $i -v | awk '/Unoptimized program size:/,0'
    echo "###########"
    echo ""
done
echo "Tests complete"
