module m;

  bit clk;
  bit sig_a, sig_b;

  bad_label : cover property (sig_a ##1 sig_b); 


endmodule

