
perf record --call-graph dwarf -- ./_build/default/bin/sim_halsoa.exe -c 1 -t 100 -s 1000 -h 1000 ./data/
perf script -f -F +pid > test.perf
rm -rf ./data