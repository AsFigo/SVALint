module tb_req_ack;

    reg clk;
    reg reset_n;
    wire req;
    wire ack;

    
    req_ack_generator uut (
        .clk(clk),
        .reset_n(reset_n),
        .req(req),
        .ack(ack)
    );

    //Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk; 
    end

    //Reset logic
    initial begin
        reset_n = 0;
        #10 reset_n = 1;
    end

    //Define sequence for req followed by ack in the next cycle
    sequence req_ack_sequence;
        req ##1 ack;
    endsequence

    //Cover property to verify non-vacuous coverage of req followed by ack
    cover property (@(posedge clk) req_ack_sequence);

    // Monitor for start and coverage tracking
    initial begin
        $display("Starting coverage tracking for req followed by ack.");
        #100 $finish; // End simulation after some time
    end

endmodule

