 module no2_within;
   bit go, a, w, y, b, clk;
   initial forever #3 clk = !clk;
   // No detection for 2 occurrence of 'a'
   ap_1a_within_b: assert property(@ (posedge clk) $rose(go) |=>  a[=1]);
endmodule : no2_within;

