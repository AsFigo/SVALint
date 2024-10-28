run: 
	vlib work
	vlog -sv -mfcu  test_6.sv test_6_tb.sv -l comp_log.log
	vsim -c tb_fifo -do "run -all;exit" -l run_log.log
