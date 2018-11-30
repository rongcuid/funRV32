all: ram_cache.time.log

ram_cache.json: ../funrv32.v ram_cache_test.v
	yosys -p 'synth_ice40 -json $@ -top ram_cache_top' $^ | tee ram_cache.syn.log

ram_cache.asc: ram_cache.json
	nextpnr-ice40 --up5k --asc $@ --json $^ | tee ram_cache.pnr.log

ram_cache.time.log: ram_cache.asc
	icetime -d up5k -t $^ | tee ram_cache.time.log

funrv32_reg.json: ../funrv32.v funrv32_reg_test.v
	yosys -p 'synth_ice40 -json $@ -top funrv32_reg_top' $^ | tee funrv32_reg.syn.log

funrv32_reg.asc: funrv32_reg.json
	nextpnr-ice40 --up5k --asc $@ --json $^ | tee funrv32_reg.pnr.log

funrv32_reg.time.log: funrv32_reg.asc
	icetime -d up5k -t $^ | tee funrv32_reg.time.log


counter.json: counter.v
	yosys -p 'synth_ice40 -json $@ -top counter_top' $^ | tee counter.syn.log

counter.asc: counter.json
	nextpnr-ice40 --up5k --pcf $(@:asc=pcf) --asc $@ --json $^ | tee counter.pnr.log

counter.time.log: counter.asc
	icetime -d up5k -t $^ | tee counter.time.log

clean:
	rm -f *.json *.asc *.log
