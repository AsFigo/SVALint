run: 
	vlib.exe work
	vlog.exe -sv -mfcu  test_8.sv test_8_tb.sv -l comp_log.log
	vsim.exe -c tb_property -do "run -all;exit" -l run_log.log
