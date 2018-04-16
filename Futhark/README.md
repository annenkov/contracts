Here are some experiments executed on a Mac Book Pro with (1) an AMD
Radeon Pro 460 GPU and (2) an Intel HD Graphics 530 1536M chip-integrated GPU.:

````
bash-3.2$ futhark-bench --compiler=futhark-c PriceNew.fut
Compiling PriceNew.fut...
Results for PriceNew.fut:
dataset OptionPricing-data/new1.in:  979756.70us (avg. of 10 runs; RSD: 0.01)
bash-3.2$ futhark-bench -p -dAMD --compiler=futhark-opencl PriceNew.fut
Compiling PriceNew.fut...
Results for PriceNew.fut:
dataset OptionPricing-data/new1.in:   12316.00us (avg. of 10 runs; RSD: 0.01)
bash-3.2$ futhark-bench --compiler=futhark-opencl PriceNew.fut
Compiling PriceNew.fut...
Results for PriceNew.fut:
dataset OptionPricing-data/new1.in:   20806.70us (avg. of 10 runs; RSD: 0.18)
bash-3.2$
````

Here are some manual runs:

````
bash-3.2$ make clean all
rm -rf *~ *.c *.exe *.out
futhark-opencl -o PriceNew.opencl.exe PriceNew.fut
cat OptionPricing-data/new1.in | ./PriceNew.opencl.exe -t /dev/stderr -r 5 > PriceNew.opencl.out
28949
25974
23158
21386
20038
Result:
[83.560638f32]
futhark-c -o PriceNew.exe PriceNew.fut
cat OptionPricing-data/new1.in | ./PriceNew.exe -t /dev/stderr -r 5 > PriceNew.out
990357
985117
984900
972327
977360
Result:
[83.560783f32]
rm PriceNew.opencl.exe PriceNew.exe
bash-3.2$ cat OptionPricing-data/new1.in | ./PriceNew.opencl.exe -t /dev/stderr -r 5 -d AMD
8753
8989
12138
11971
12334
[83.560692f32]
````
