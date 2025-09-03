module m;

  bit clk;
  bit sig_a, sig_b;

  property p_chk;
    @(posedge clk) sig_a |=> sig_b;
  endproperty : p_chk

  a_p_chk : assert property (p_chk) 
  else begin : fa
    $error ("Good labelled SVA");
  end : fa;


endmodule

