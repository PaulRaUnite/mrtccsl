clear
reset
set border 3
set datafile separator ','

set output sprintf("%s.pdf", filename)
set terminal pdf
set datafile missing NaN
set datafile columnheaders

# Add a vertical dotted line at x=0 to show centre (mean) of distribution.
set yzeroaxis

# Each bar is half the (visual) width of its x-range.
set boxwidth 0.9 relative
set style data histograms
set style histogram rowstacked
set style fill solid 1.0

set ylabel "probability"

print(filename)
stats filename name "D" nooutput;

set nokey
set xtics 1

plot for [j=2:D_columns] filename using j:xtic(1);
