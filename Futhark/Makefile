
all: Small.opencl.res Medium.opencl.res New.opencl.res Small.c.res Medium.c.res New.c.res

#all: PriceNew.opencl.out PriceNew.out PriceNew.opencl.exe PriceNew.exe PriceSmall.opencl.exe PriceSmall.exe PriceMedium.opencl.exe PriceMedium.exe

%.opencl.res: Price%.fut
	futhark-bench --compiler=futhark-opencl -p -dAMD $< > $@

%.c.res: Price%.fut
	futhark-bench --compiler=futhark-c $< > $@

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
