module m;

  bit clk, req, rdy, ack;
// 
// Example: rdy[->1] is equivalent to:
// (rdy) or (!rdy ##1 rdy) or
// (!rdy ##1 !rdy ##1 rdy) or (!rdy ##1 !rdy ##1 !rdy ... ##1 rdy)
// Once rdy==1, there cannot be another thread with rdy==1
// Application example:
// Instead of: 
a_avoid1: assert property(@ (posedge clk)
   $rose(req) ##[1:$] rdy |-> ##[1:2] ack );
   else begin : fail_ap_unbounded_range
    $error("Assertion failed: request must see rdy before ack within 2 cycles");
   end : fail_ap_unbounded_range;
   
endmodule : m
