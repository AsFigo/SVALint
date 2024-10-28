
run: 
	vlib work
	vlog -sv -mfcu  test_10.sv test_10_tb.sv -l comp_log.log
	vsim -c tb_req_ack -do "run -all;exit" -l run_log.log
