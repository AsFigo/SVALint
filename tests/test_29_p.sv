module dmaxfrdone_pass;
  bit clk, req, rdy, ack;

  
  a_reqrdyack: assert property (@ (posedge clk)
    (req ##1 rdy) |-> ##[1:2] ack)
  else begin : fail_ablk
    $error("req followed by rdy must be acked within 2 cycles");
  end : fail_ablk;

endmodule : dmaxfrdone_pass
