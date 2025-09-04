run: 
	vlib work
	vlog -sv -mfcu  test_8.sv test_8_tb.sv -l comp_log.log
	vsim -c tb_property -do "run -all;exit" -l run_log.log

run_pass:
	python ../../bin/svalint.py -t ./test_8_tb_p.sv

run_fail:
	python ../../bin/svalint.py -t ./test_8_tb_f.sv

clean:
	rm -rf work
	rm -f *.log
