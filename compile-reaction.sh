for f in $(find . -type f -wholename "*/reaction_times.csv");
do
  echo "$f";
  gnuplot -e "filename='$f'" probability.gnu 
done