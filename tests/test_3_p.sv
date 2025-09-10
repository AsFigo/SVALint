module m;

  bit clk;
  bit sig_a, sig_b;

  initial clk = 0;
  always #5 clk = ~clk;

  initial begin
  sig_a = 0; sig_b = 0;
  #12 sig_a = 1;   
  #10 sig_b = 1;   
  #20 $finish;
  end

  property p_chk;
    @(posedge clk) sig_a |=> sig_b;
  endproperty : p_chk

  m_chk_assume : assume property (m_chk)
  else begin : fa
    $error ("m_chk assumption violated");
  end : fa

endmodule

