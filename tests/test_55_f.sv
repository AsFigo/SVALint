module m;
  bit clk;
  bit cur_st;
  bit rst_n;

  parameter FAULT_SD       = 0;
  parameter WAIT_LDO1_POK  = 1;
  parameter int T_DELAY    = 100000; 

  
  property p_ppt;
    time t1;
    @(posedge clk) disable iff(!rst_n)
      $changed(cur_st) && (cur_st==FAULT_SD, t1=$time) 
      |=> cur_st==FAULT_SD until (($time - t1) > T_DELAY) ##0 cur_st==WAIT_LDO1_POK;
  endproperty : p_ppt

  
  a_ppt : assert property (p_ppt)
  else begin
	$error("Assertion failed: p_ppt violated");
  end
endmodule : m
