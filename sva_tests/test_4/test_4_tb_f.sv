module tb_property;
    reg clk;
    reg req;
    reg grnt;

    // Clock generation
    initial begin
        clk = 0;
        forever #5 clk = ~clk; // 10ns clock period
    end

    //Coverage group with coverpoints prefixed by "c_", convention not used in this test case
    covergroup cg_req_grnt @(posedge clk);
        req_high: coverpoint req {
            bins req_high = {1'b1}; //Covers when req is high
        }
        grnt_high: coverpoint grnt {
            bins grnt_high = {1'b1}; //Covers when grnt is high
        }
    endgroup : cg_req_grnt

    //Instantiate the coverage group
    cg_req_grnt cov = new();

    // Stimulus for testing the coverage points
    initial begin
        req = 0;
        grnt = 0;

        //Apply stimulus to hit coverage points
        #10 req = 1;  //Set req high
        #10 req = 0;

        #10 grnt = 1; //Set grnt high
        #10 grnt = 0;

        #100 $finish; 
    end

    //Monitor coverage results
    initial begin
        wait (cov.c_req_high.get_coverage() == 100);
        wait (cov.c_grnt_high.get_coverage() == 100);
        $display("Coverage achieved for c_req_high and c_grnt_high.");
    end
endmodule

