module m;
  bit clk, rst, a, b;

  c_example : cover property (@(posedge clk) a && b);
  m_example : assume property (@(posedge clk) a |=> b);
endmodule : m
