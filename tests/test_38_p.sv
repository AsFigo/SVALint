module m;

  bit clk, req, rdy, ack;

  a_req_rdy_ack: assert property(@ (posedge clk)
    $rose(req) ##1 rdy[->1] |-> ##1 ack )
  else begin : fail_ap_req_rdy_ack
    $error("Assertion failed: req must see rdy in next cycle, then ack immediately after");
  end : fail_ap_req_rdy_ack;

endmodule : m
