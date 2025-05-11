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


do for [case in "certain1 uncertain1 uncertain2 simpy_uniform_nores simpy_uniform_1res simpy_normal_nores simpy_normal_1res"] {
    stats sprintf('./data/%s_reaction_times.csv', case) using 2 name "D" nooutput;
    set title case;
    plot for [i=3:0:-1] sprintf('./data/%s_reaction_times.csv', case) using (($1<=i)?rounded($2):NaN):(1.0/D_records) smooth frequency with boxes title "missed ".i
}