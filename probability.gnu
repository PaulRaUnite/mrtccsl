
clear
reset
set border 3
set datafile separator ','

set output sprintf("%s.svg", filename)
set terminal svg size 1000,500 enhanced font "Helvetica,20" background rgb "white"
set datafile missing NaN
set datafile columnheaders

# Each bar is half the (visual) width of its x-range.
set boxwidth 0.5 relative
set style data histograms
set style histogram rowstacked
set style fill solid 1.0

# set ylabel "probability"

print(filename);
stats filename name "D" nooutput

# set nokey
unset border
set xtics auto

plot for [j=3:D_columns] filename using j title sprintf("missed %i", j-3);