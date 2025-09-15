module m;

  bit clk;
  bit sig_a, sig_b;

  sequence s_chk;
    sig_a ##2 sig_b;
  endsequence : s_chk

  sequence s_chk1;
    sig_a ##2 sig_b;
  endsequence : s_chk1


endmodule

