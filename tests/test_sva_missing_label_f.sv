module m;
  bit clk, rst, a, b;

  assert property (@(posedge clk) a);
endmodule : m
