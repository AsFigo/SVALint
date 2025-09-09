module aa_popfront_sva_test;
  bit clk;
  int unsigned a;
  int fifo_q[$]; 

  // According to IEEE 1800-2017 §16.6, this should still evaluate correctly
  // even if the array changes before evaluation
  property p_check_popfront;
    @(posedge clk)
    ($rose(a) |-> (fifo_q.pop_front == 8'h08));    
  endproperty : p_check_popfront

  // bind to assertion
  a_check_popfront: assert property (check_popfront)
  else begin
    $error("fifo_q.pop_front failed during assertion evaluation");
  end;

endmodule
