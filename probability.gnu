clear
reset
set border 3
set datafile separator ','

set output 'probability.pdf'
set terminal pdf
set datafile missing NaN
set datafile columnheaders

# Add a vertical dotted line at x=0 to show centre (mean) of distribution.
set yzeroaxis

# Each bar is half the (visual) width of its x-range.
set style data histogram
set style histogram rowstacked
set boxwidth 0.1 absolute
set style fill solid 1.0 noborder

bin_width = 0.1;

bin_number(x) = floor(x/bin_width)

rounded(x) = bin_width * ( bin_number(x) + 0.5 )

set ylabel "probability"

files = system("ls -1 ./data/*/*.csv")
print files ;
# array titles = ["C2 with 2 cores", "C2 with 16 cores", "C4 with 2 cores", "C4 with 16 cores", "C5 with 2 cores", "C5 with 16 cores"]
do for [i=1:words(files)] {
    file = word(files, i);
    stats file using 1 name "D" nooutput;
    
    do for [j=2:D_columns] {
        set title file noenhanced ;
        set xlabel sprintf("reaction time %s", D_column_header[j]);
        plot file using (($1<=3)?rounded(column(j)):NaN):(1.0/D_records) smooth frequency with boxes title "missed 3" , \
            '' using (($1<=2)?rounded(column(j)):NaN):(1.0/D_records) smooth frequency with boxes title "missed 2" , \
            '' using (($1<=1)?rounded(column(j)):NaN):(1.0/D_records) smooth frequency with boxes title "missed 1" , \
            '' using (($1<=0)?rounded(column(j)):NaN):(1.0/D_records) smooth frequency with boxes title "missed 0" , \
            '' using (rounded(column(j))):(0.1/D_records) smooth kdensity bandwidth 1 lw 2 lc rgb "black" title "distribution";
    }
}