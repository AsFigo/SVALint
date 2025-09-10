module aa_popfront_sva_test;
  bit clk;
  int unsigned a;
  int fifo_q[$]; 

  property p_check_popfront;
    @(posedge clk)
      ($rose(a) |-> (fifo_q[0] == 8'h08));    
  endproperty : p_check_popfront

  a_check_popfront: assert property (p_check_popfront)
    else begin
      $error("Assertion p_check_popfront failed: first element != 8'h08");
    end

  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  initial begin
    fifo_q = {8'h08, 2, 3};  
    a = 0;
    #12 a = 1;   
    #20 $finish;
  end
endmodule
