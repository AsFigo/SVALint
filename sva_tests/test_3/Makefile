run: 
	vlib work
	vlog -sv -mfcu  test_3.sv test_3_tb.sv -l comp_log.log
	vsim -c tb_m -do "run -all;exit" -l run_log.log
