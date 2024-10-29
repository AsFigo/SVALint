
run: 
	vlib work
	vlog -sv -mfcu  test_7.sv test_7_tb.sv -l comp_log.log
	vsim -c tb_assoc_array -do "run -all;exit" -l run_log.log
