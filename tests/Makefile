TARGET_MHZ=36

all: inst_decoder.time.log funrv32_reg.time.log main_mem.time.log main_alu.time.log

%.json: ../funrv32.v %_test.v
	yosys -p 'synth_ice40 -json $@ -top ${@:.json=_top}' $^ | tee ${@:.json=.syn.log}

%.asc: %.json
	nextpnr-ice40 --freq $(TARGET_MHZ) --up5k --asc $@ --json $^ | tee ${@:.asc=.pnr.log}

%.time.log: %.asc
	icetime -m -c $(TARGET_MHZ) -d up5k -t $^ | tee $@

# funrv32_reg.json: ../funrv32.v funrv32_reg_test.v
# 	yosys -p 'synth_ice40 -json $@ -top funrv32_reg_top' $^ | tee funrv32_reg.syn.log

# funrv32_reg.asc: funrv32_reg.json
# 	nextpnr-ice40 --up5k --asc $@ --json $^ | tee funrv32_reg.pnr.log

# funrv32_reg.time.log: funrv32_reg.asc
# 	icetime -d up5k -t $^ | tee funrv32_reg.time.log

counter: counter.v
	yosys -p 'synth_ice40 -json counter.json -top counter_top' counter.v | tee counter.syn.log
	nextpnr-ice40 --up5k --asc counter.asc --json counter.json | tee counter.pnr.log
	icetime -d up5k -t counter.asc | tee counter.time.log

clean:
	rm -f *.json *.asc *.log

.PHONY: counter clean
.SECONDARY:
