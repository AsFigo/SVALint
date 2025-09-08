module m;

  bit clk;
  bit sig_a, sig_b;

  property chk;
    @(posedge clk) sig_a |=> sig_b;
  endproperty : chk

  a_chk : assert property (chk) 
  else begin : fa
    $error ("Bad labelled SVA property");
  end : fa;


endmodule

