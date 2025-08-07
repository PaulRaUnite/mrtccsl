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
set style data histogram
set style histogram rowstacked
set boxwidth 0.1 absolute
set style fill solid 1.0 noborder

bin_width = 0.1;

bin_number(x) = floor(x/bin_width)

rounded(x) = bin_width * ( bin_number(x) + 0.5 )

set ylabel "probability"

print(filename)
stats filename using 1 name "D" nooutput;

set nokey

do for [j=2:D_columns] {
    # set title filename noenhanced ;
    # set xlabel sprintf("reaction time %s", D_column_header[j]);
    set xlabel sprintf("reaction time");
    plot filename using (($1<=3)?rounded(column(j)):NaN):(1.0/D_records) smooth frequency with boxes title "missed 3" , \
        '' using (($1<=2)?rounded(column(j)):NaN):(1.0/D_records) smooth frequency with boxes title "missed 2" , \
        '' using (($1<=1)?rounded(column(j)):NaN):(1.0/D_records) smooth frequency with boxes title "missed 1" , \
        '' using (($1<=0)?rounded(column(j)):NaN):(1.0/D_records) smooth frequency with boxes title "missed 0" ;
}