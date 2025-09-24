#!/usr/bin/env bash
unset GTK_PATH;
SCRIPT_DIR=$( cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd )

cd $1
for f in $(find . -type f -wholename "*reaction_time_hist.csv");
do
  echo "$f";
  gnuplot -e "filename='$f'" $SCRIPT_DIR/probability.gnu 
done