module aa_fifo_cover_sva_test;
  bit clk;
  int unsigned a;
  int fifo_q[$];

  property p_check_last_element;
    @(posedge clk)
    ($rose(a) |-> (fifo_q[$] == 8'h08));
  endproperty : p_check_last_element

  // Naming with prefix c_
  c_check_last_element: cover property (p_check_last_element);

  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  initial begin
    fifo_q = {1, 2, 8'h08}; 
    a = 0;
    #12 a = 1;   // trigger cover
    #20 $finish;
  end
endmodule
