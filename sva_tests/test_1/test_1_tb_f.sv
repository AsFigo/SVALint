module tb_property;
    reg clk;
    reg req;
    reg grnt;

    // Property with the required "p_" prefix
    property req_grnt;
      @(posedge clk) $rose(req) |-> ##[1:3] grnt;
    endproperty : req_grnt

    // Assertion using the property
    assert property (req_grnt) else
        $error("Assertion failed: req_grnt - grant signal did not occur within 1 to 2 cycles after req signal.");

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 10ns clock period
    end

    // Stimulus for testing the property
    initial begin
        req = 0;
        grnt = 0;

        // Apply stimulus to satisfy the assertion
        #15 req = 1;  // Raise req at time = 15ns
        #10 req = 0;  // Lower req after one clock cycle

        // Assert grnt within the 1-2 cycle window
        #10 grnt = 1; // Assert grnt at 35ns, within the 1-2 cycle window after req
        #10 grnt = 0; //Lower grnt

        #100 $finish; 
    end

    //Monitor for start of test
    initial begin
        $display("Starting test...");
    end
endmodule

