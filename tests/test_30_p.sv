module m;

  bit clk, req, rdy, ack;

  a_avoid: assert property(@ (posedge clk) req ##1 req |-> rdy);
        else begin : fail_a_avoid
         $error("Assertion failed: req followed by req must lead to rdy");
        end : fail_a_avoid;
a_avoid1: assert property(@ (posedge clk)
   $rose(req) ##2 rdy |-> ##[1:2] ack );
   else begin : fail_a_avoid1
    $error("Assertion failed: req->rdy must be acked within 2 cycles");
  end : fail_a_avoid1;
endmodule : m

