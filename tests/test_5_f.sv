module aa_pop_bk_sva_test;
  bit clk;
  int unsigned a;
  int fifo_q[$]; 

  // According to IEEE 1800-2017 §16.6, this should still evaluate correctly
  // even if the array changes before evaluation
  property p_check_pop_bk;
    @(posedge clk)
    ($rose(a) |-> (fifo_q.pop_back == 8'h08));    
  endproperty : p_check_pop_bk

  // bind to assertion
  a_check_pop_bk: assert property (check_pop_bk)
  else begin
    $error("fifo_q.pop_back failed during assertion evaluation");
  end;

endmodule
