
all: PriceNew.opencl.out PriceNew.out

%.out: %.exe
	cat OptionPricing-data/new1.in | ./$< -t /dev/stderr -r 5 > $@
	@echo Result:
	@cat $@

%.opencl.exe: %.fut
	futhark-opencl -o $@ $<

%.exe: %.fut
	futhark-c -o $@ $<

.PHONY: clean
clean:
	rm -rf *~ *.c *.exe *.out
