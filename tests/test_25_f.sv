module m;

  bit clk, a, b;
  property p_check;
    @(posedge clk) a |-> b;
  endproperty : p_check

  a_check : assert property (p_check)
    begin
      $display("Property p_check PASSED at time %0t", $time);
    end
    else begin
      $error("Property p_check FAILED at time %0t", $time);
    end
endmodule
