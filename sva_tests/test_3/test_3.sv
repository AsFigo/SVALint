module m_simple (
    input logic clk,
    input logic rst_n,
    input logic in_signal,
    output logic out_signal
);
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            out_signal <= 1'b0;
        else
            out_signal <= in_signal;
    end

endmodule
