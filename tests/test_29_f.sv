module dmaxfrdone;
  bit clk, req, rdy, ack;
  ap_reqrdyack: assert property(@ (posedge clk) 
  first_match(req ##[1:2] rdy) |->  ##[1:2] ack);
endmodule
