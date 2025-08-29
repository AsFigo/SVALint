module aa_exists_sva_test;
  bit clk;
  bit rst_n;
  int unsigned addr;
  int unsigned data;
  int mem_aarray[int unsigned]; // associative array

  // clock generation
  initial begin
    clk = 0;
    forever #5 clk = ~clk;
  end

  // stimulus
  initial begin
    rst_n = 0;
    addr  = 1;
    #12 rst_n = 1;

    // cycle 1: insert an element
    mem_aarray[addr] = 123;

    // cycle 2: delete element to see if .exists() still works correctly
    #10 mem_aarray.delete(addr);

    // cycle 3: finish
    #20 $finish;
  end

  // property: sample .exists() at posedge clk
  // According to IEEE 1800-2017 §16.6, this should still evaluate correctly
  // even if the array changes before evaluation
  property check_exists;
    @(posedge clk)
      rst_n |-> mem_aarray.delete(addr);
  endproperty

  // bind to assertion
  a_check_exists: assert property (check_exists)
    else $error("mem_aarray.exists(addr) failed during assertion evaluation");

endmodule
