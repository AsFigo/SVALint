module m;
  bit clk, rst, a, b;


  a_bad_pass_ablk : assert property (@(posedge clk) a)
begin
    $info ("a_bad_pass_ablk: Pass action block");
  end;
endmodule : m
