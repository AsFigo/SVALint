module m;
  bit clk;
  bit sig_a;
  realtime t1;

  
  property p_chk;
    @(posedge clk)  1'b1 |-> sig_a;
  endproperty : p_chk

  
  a_chk : assert property (p_chk)
    else begin : fail_a_chk
      t1 = $realtime;  
      $error("Assertion failed: p_chk violated at time=%0t", t1);
    end

endmodule : m
