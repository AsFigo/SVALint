// Code your design here
module req_ack_generator (
    input  wire clk,
    input  wire reset_n,
    output reg  req,
    output reg  ack
);

    // State machine to control req and ack signals
    reg [1:0] state;

    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            req   <= 0;
            ack   <= 0;
            state <= 0;
        end else begin
            case (state)
                2'd0: begin
                    req   <= 1;  // Assert req
                    ack   <= 0;
                    state <= 2'd1;
                end
                2'd1: begin
                    req   <= 0;  // Deassert req
                    ack   <= 1;  // Assert ack
                    state <= 2'd2;
                end
                2'd2: begin
                    req   <= 0;
                    ack   <= 0;  // Deassert ack
                    state <= 2'd0; // Return to initial state
                end
            endcase
        end
    end
endmodule

