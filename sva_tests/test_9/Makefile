run: 
	vlib work
	vlog -sv -mfcu  test_9.sv test_9_tb.sv -l comp_log.log
	vsim -c tb_memory -do "run -all;exit" -l run_log.log
