clear
reset
set border 3
set datafile separator ','

set output 'probability.pdf'
set terminal pdf
set datafile missing NaN

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

files = "c2_normal_2cores c2_normal_16cores c3_normal_2cores c3_normal_16cores c4_normal_2cores c4_normal_16cores"
# array titles = ["C2 with 2 cores", "C2 with 16 cores", "C4 with 2 cores", "C4 with 16 cores", "C5 with 2 cores", "C5 with 16 cores"]
do for [i=1:words(files)] {
    file = word(files, i);
    stats sprintf('./data/%s_reaction_times.csv', file) using 2 name "D" nooutput;
    # set title titles[i];
    plot sprintf('./data/%s_reaction_times.csv', file) using (($1<=3)?rounded($2):NaN):(1.0/D_records) smooth frequency with boxes title "useless 3" , \
        '' using (($1<=2)?rounded($2):NaN):(1.0/D_records) smooth frequency with boxes title "useless 2" , \
        '' using (($1<=1)?rounded($2):NaN):(1.0/D_records) smooth frequency with boxes title "useless 1" , \
        '' using (($1<=0)?rounded($2):NaN):(1.0/D_records) smooth frequency with boxes title "useless 0" , \
        '' using (rounded($2)):(0.1/D_records) smooth kdensity bandwidth 1 lw 2 lc rgb "black" title "distribution";

}