module m;

  bit clk;
  bit sig_a;

  property p_chk;
    @(posedge clk) sig_a;
  endproperty

  // use an assertion
  a1 : assert property (p_chk) else $error("fail");
  a2 : assert property (p_chk);

endmodule

