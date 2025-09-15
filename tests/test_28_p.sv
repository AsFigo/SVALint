module m_pass;

  bit clk, req, ack;

  parameter int MAX_WAIT = 10; // finite range instead of $ 

  p_req_ack: property (@(posedge clk)
     $rose(req) |-> ##[0:MAX_WAIT] ack );
     
  a_req_ack: assert property (p_req_ack)
  else begin : fa
     $error("ack did not arrive in finite range");
  end: fa;

endmodule : m_pass
