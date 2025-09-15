module m;

  bit clk;
  bit rstn;
  bit RVALID, RID, RREADY, RLAST;
  bit [31:0] RDATA;
  bit [ 2:0] RRESP;
  property p_r_ch;
    @(posedge clk) disable iff (!rstn) $rose(
        RVALID
    ) |-> ($stable(
        RID
    ) && $stable(
        RDATA
    ) && $stable(
        RRESP
    ) && $stable(
        RLAST
    )) throughout RREADY [-> 1];
  endproperty : p_r_ch

  property p_r_ch1;
    @(posedge clk) disable iff (!rstn) $rose(
        RVALID
    ) |-> ($stable(RID));
  endproperty : p_r_ch1

  a_r_ch : assert property (p_r_ch) 
  else
    begin 
      $error ("R_CH SVA failed");
    end

endmodule : m
