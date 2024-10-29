module req_grnt_ctrl(
    input wire clk,
    input wire req,
    output reg grnt
);
    reg [1:0] delay_cnt;

    always @(posedge clk) begin
        if (req) begin
            delay_cnt <= 2'd0; // Start delay counter when req is high
        end else if (delay_cnt < 2'd2) begin
            delay_cnt <= delay_cnt + 1;
        end
        
        if (delay_cnt == 2'd1 || delay_cnt == 2'd2) begin
            grnt <= 1; // Assert grnt within 1-2 cycles after req
        end else begin
            grnt <= 0; // De-assert grnt otherwise
        end
    end
endmodule

