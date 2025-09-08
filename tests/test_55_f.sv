module m;
bit clk;
bit cur_st;
parameter FAULT_SD = 0;
parameter WAIT_LDO1_POK = 1;

/*
property ppt;
      realtime t1;
      @(posedge clk) 
        ($rose(cur_st==FAULT), t1=$realtime) |=>
     cur_st==FAULT [*] ##1 cur_st==WAIT ##0 $realtime-t1 > 100ms
endproperty : ppt
*/
property ppt;
  time t1;
  @(posedge clk) disable iff(!rst_n)
    $changed(cur_st) && (cur_st==FAULT_SD, t1=$time)
    |=> cur_st==FAULT_SD until (($time-t1)*1000000 == 100ms) ##0 cur_st==WAIT_LDO1_POK;
endproperty : ppt

endmodule : m

