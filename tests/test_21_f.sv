module m;

bit clk;
bit sig_a, sig_b;

property check_sig_a_to_b_bad_timed;
  time t_start;
  @(posedge clk)
  (sig_a, t_start = $realtime) |->
    ##1 sig_b [->1] ##0 ($realtime >= t_start + 1.1us);
  endproperty
endmodule
