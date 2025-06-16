#!/usr/bin/env bash

SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )

cd $1
for f in $(find . -type f -wholename "*/reaction_times.csv");
do
  echo "$f";
  gnuplot -e "filename='$f'" $SCRIPT_DIR/probability.gnu 
done