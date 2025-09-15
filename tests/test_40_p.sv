module m;

  bit clk;
  bit sig_a;

  property p_chk;
    @(posedge clk) 1'b1 |-> sig_a;
  endproperty : p_chk

  a_fail_actn_blk : assert property (p_chk)
   else begin : fail_a_fail_actn_blk
    $error("Assertion failed: p_chk violated");
   end
  a_fail_actn_blk1 : assert property (p_chk);
   else begin : fail_a_fail_actn_blk1
     $error("Assertion failed: p_chk violated ");
   end : fail_a_fail_actn_blk1

endmodule : m

