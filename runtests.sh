#!/bin/sh
backend="scm"
interpreter="gambitc -i"

out_file="out.$backend"
timings_file=$(mktemp)

for file in examples/*.spk
do
    echo "########### Running test: $file"
    cabal run spinnaker -- --file $file --verbose --backend=$backend | awk '/Unoptimized program size:/,0'
    echo "----"
    { time $(echo $interpreter $out_file); } 2>> $timings_file
    echo "###########"
    echo ""
done
echo "Tests complete. Total time spent in execution: "
awk -F'[ms]' '/real/ {print $2}' $timings_file | awk 'gsub(/,/,".") {sum += $0} END {print sum}'
rm $timings_file
rm $out_file
