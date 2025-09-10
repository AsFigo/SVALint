module aa_fifo_cover_sva_test;
  bit clk;
  int unsigned a;
  int fifo_q[$];

  property p_check_pop_bk;
    @(posedge clk)
    ($rose(a) |-> (fifo_q[$] == 8'h08));
  endproperty : p_check_pop_bk

  a_check_pop_bk: assert property (p_check_pop_bk)
      else begin
       $error("Assertion p_check_pop_bk failed: last element != 8'h08");
      end
  
initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  initial begin
    fifo_q = {1, 2, 8'h08}; 
    a = 0;
    #12 a = 1;   
    #20 $finish;
  end
endmodule
