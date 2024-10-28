module req_grnt_controller (
    input  wire clk,
    output reg  req,
    output reg  grnt
);

    // Internal state for generating req and grnt signals
    reg [3:0] state;

    // Initialize signals
    initial begin
        req  = 0;
        grnt = 0;
        state = 0;
    end

    // Sequential logic for req and grnt signal generation
    always @(posedge clk) begin
        case (state)
            4'd0: begin
                req <= 1;    // Raise req signal
                grnt <= 0;
                state <= 4'd1;
            end
            4'd1: begin
                req <= 0;
                state <= 4'd2;
            end
            4'd2: begin
                grnt <= 1;   // Raise grnt signal
                req <= 0;
                state <= 4'd3;
            end
            4'd3: begin
                grnt <= 0;
                state <= 4'd0; // Reset the state to repeat the pattern
            end
            default: state <= 4'd0;
        endcase
    end

endmodule

