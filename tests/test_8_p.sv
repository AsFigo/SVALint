module aa_exists_sva_test;
  bit clk;
  bit rst_n;
  int unsigned addr;
  int unsigned data;
  int mem_aarray[int unsigned]; // associative array
  // lazy code below
  int unsigned mem_aarray_addr_exists;

  assign mem_aarray_addr_exists = mem_aarray.exists(addr);

  // property: sample .exists() at posedge clk
  // According to IEEE 1800-2017 §16.6, this should still evaluate correctly
  // even if the array changes before evaluation
  property p_check_exists;
    @(posedge clk)
      rst_n |-> mem_aarray_addr_exists;
  endproperty : p_check_exists

  // bind to assertion
  a_check_exists: assert property (check_exists)
  else begin
    $error("mem_aarray.exists(addr) failed during assertion evaluation");
  end;

endmodule
