module counter_module;

  logic clk;
  logic reset_n;
  logic [7:0] counter;
  always #5 clk = ~clk;

  
  property p_counter_within_limit;
    @(posedge clk) disable iff (!reset_n) (counter <= 100);
  endproperty

  // Assertion using the property with a_ prefix for the name
  a_counter_limit_check: assert property (p_counter_within_limit)
    else $error("Assertion Failed: Counter exceeds the maximum allowed value!");

  
  initial begin
   
    clk = 0;
    reset_n = 0;
    counter = 8'd0;
    #10 reset_n = 1;
    #10 counter = 50;   
    #10 counter = 80;  
    #20 $finish;
  end
endmodule
