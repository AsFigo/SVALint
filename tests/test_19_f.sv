module m;

  bit clk;
  bit rstn;
  bit RVALID, RID, RREADY, RLAST;
  bit [31:0] RDATA;
  bit [ 2:0] RRESEP;
  property r_ch;
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
  endproperty : r_ch

  property r_ch1;
    @(posedge clk) disable iff (!rstn) $rose(
        RVALID
    ) |-> ($stable(RID));
  endproperty : r_ch1

  a_r_ch : assert property (r_ch) 
  else $error ("R_CH SVA failed");

endmodule : m
