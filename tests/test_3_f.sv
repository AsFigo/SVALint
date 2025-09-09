module m;

  bit clk;
  bit sig_a, sig_b;

  property p_chk;
    @(posedge clk) sig_a |=> sig_b;
  endproperty : p_chk

  bad_label : assume property (p_chk) 
  else begin : fa
    $error ("Bad labelled SVA");
  end : fa;


endmodule

