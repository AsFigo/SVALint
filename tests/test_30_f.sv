module m;

  bit clk, req, rdy, ack;
// 
// Example: rdy[->1] is equivalent to:
// (rdy) or (!rdy ##1 rdy) or
// (!rdy ##1 !rdy ##1 rdy) or (!rdy ##1 !rdy ##1 !rdy ... ##1 rdy)
// Once rdy==1, there cannot be another thread with rdy==1
// Application example:
// Instead of: 
ap_avoid: assert property(@ (posedge clk) req ##1 req |-> rdy);
ap_avoid1: assert property(@ (posedge clk)
   $rose(req) ##[1:10] rdy |-> ##[1:2] ack );
endmodule : m
