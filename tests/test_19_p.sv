module m;

  bit clk;
  bit rstn;
  bit RVALID, RID, RREADY, RLAST;
  bit [31:0] RDATA;
  bit [ 2:0] RRESP;

  // split into smaller properties for readability and debug
  property p_r_ch_id;
    @(posedge clk) disable iff (!rstn)
      $rose(RVALID) |-> $stable(RID) throughout RREADY [->1];
  endproperty : p_r_ch_id

  property p_r_ch_data;
    @(posedge clk) disable iff (!rstn)
      $rose(RVALID) |-> $stable(RDATA) throughout RREADY [->1];
  endproperty : p_r_ch_data

  property p_r_ch_resp;
    @(posedge clk) disable iff (!rstn)
      $rose(RVALID) |-> $stable(RRESP) throughout RREADY [->1];
  endproperty : p_r_ch_resp

  property p_r_ch_last;
    @(posedge clk) disable iff (!rstn)
      $rose(RVALID) |-> $stable(RLAST) throughout RREADY [->1];
  endproperty : p_r_ch_last

  a_r_ch_id   : assert property (p_r_ch_id)  
    else begin 
    $error("R_CH ID failed");   
    end
  a_r_ch_data : assert property (p_r_ch_data)
    else begin 
      $error("R_CH DATA failed"); 
    end
  a_r_ch_resp : assert property (p_r_ch_resp)
    else  begin 
      $error("R_CH RESP failed"); 
     end
  a_r_ch_last : assert property (p_r_ch_last)
     else begin 
     $error("R_CH LAST failed"); 
     end

endmodule : m

