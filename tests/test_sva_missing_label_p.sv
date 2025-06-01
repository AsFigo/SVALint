module m;
  bit clk, rst, a, b;

  a_example : assert property (@(posedge clk) a);
endmodule : m
