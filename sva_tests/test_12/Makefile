run: 
	vlib work
	vlog -sv -mfcu  test_12.sv test_12_tb.sv -l comp_log.log
	vsim -c cnt_tb -do "run -all;exit" -l run_log.log
