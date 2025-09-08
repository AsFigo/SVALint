module m;

  bit clk;
  bit sig_a, sig_b;

  property p_chk;
    @(posedge clk) sig_a |=> sig_b;
  endproperty : p_chk

  // Bad as one-liner Fail action block is used in an assertion
  a1 : assert property (p_chk) else $error("fail");
  a2_good : assert property (p_chk) else
  begin : fail_ablk
    $error("fail");
  end : fail_ablk;

endmodule

