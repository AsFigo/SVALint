module m;

  bit clk;
  bit sig_a;

  property p_chk;
    @(posedge clk) (sig_a |-> 1);
  endproperty : p_chk
  
  property p_chk1;
    @(posedge clk) (sig_a |-> 1);
  endproperty : p_chk1

  a_p_chk: assert property (p_chk)
    else
      begin
       $error("p_chk failed");
      end

  initial clk = 0;
  always #5 clk = ~clk;

  initial begin
    sig_a = 0;
    #12 sig_a = 1;
    #20 sig_a = 0;
    #40 $finish;
  end
endmodule
