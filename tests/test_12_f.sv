module m;

  bit clk;
  bit sig_a;

  property p_chk;
    @(posedge clk) sig_a;
  endproperty

  // use an assertion
  // a1 : assert property (p_chk) else $error("fail");
  property p_chk1;
    @(posedge clk) sig_a;
  endproperty : p_chk1


endmodule

