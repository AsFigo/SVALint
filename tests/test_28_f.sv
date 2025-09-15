module m;

  bit clk, req, ack;
// 
a_avoid1: assert property(@ (posedge clk)
   $rose(req) |-> ##[0:$] ack ) else
   begin : fa
     $error ("This can never fail, bad code");
   end: fa;
endmodule : m
