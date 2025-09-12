 module no2_within;
   bit go, a, w, y, b, clk;
   initial forever #3 clk = !clk;
   // No detection for 2 occurrence of 'a'
   a_1a_within_b: assert property(@ (posedge clk) $rose(go) |=>  (a[=1] within b[->1]));
   else begin : fail_a_1a_within_b
    $error("Assertion failed: 'within' operator used (a[=1] within b[->1])");
  end : fail_a_1a_within_b;
endmodule : no2_within;

