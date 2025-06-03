module m;

  bit clk;
  bit sig_a, sig_b;

  // Define the time delay parameter
  parameter time DELAY_TIME = 1_100; // in nanoseconds (1.1us = 1,100ns)

  property check_sig_a_to_b_timed;
    time t_start;

    @(posedge clk)
    (sig_a, t_start = $realtime) |->
      ##1 sig_b [->1] ##0 ($realtime >= t_start + DELAY_TIME);
  endproperty

  // use an assertion
  assert property (check_sig_a_to_b_timed);

endmodule

