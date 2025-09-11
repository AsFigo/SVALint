module m;

  bit clk;
  bit sig_a, sig_b;

  property p_chk;
    @(posedge clk) sig_a |=> sig_b;
  endproperty : p_chk

  
  a_chk : assert property (p_chk) 
  else begin
	 $error("fail");
       end
  a_good : assert property (p_chk) else
  begin : fail_ablk
    $error("fail");
  end : fail_ablk;

endmodule


