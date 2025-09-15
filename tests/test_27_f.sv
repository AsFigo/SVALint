module m;

  bit clk, req, rdy;
 
  property p_req_rdy;
    @(posedge clk)
      req ##[0:$] rdy |-> ##[1:5] 1; 
  endproperty : p_req_rdy

  a_req_rdy : assert property (p_req_rdy);
   else begin
	   $error("failed")
   end
  
  initial clk = 0;
  always #5 clk = ~clk;

  initial begin
    req = 0; rdy = 0;
    #12 req = 1;
    #20 req = 0;
   
    #100 $finish;
  end
endmodule :m

