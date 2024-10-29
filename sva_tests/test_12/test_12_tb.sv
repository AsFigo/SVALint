module cnt_tb;
    logic clk;
    logic reset;
    logic enable;
    logic [3:0] count;

   
    counter dut (
        .clk(clk),
        .reset(reset),
        .enable(enable),
        .count(count)
    );

   
    initial begin
        clk = 0;
        forever #5 clk = ~clk;  
    end

    property p_count_limit;
        @(posedge clk) disable iff (reset) (count <= 4'd10);
    endproperty

    count_limit_exceeded: assert property (p_count_limit) 
        else $error("Assertion failed: Counter exceeded limit");

    initial begin
        reset = 1;
        enable = 0;
        #10 reset = 0;       
        #10 enable = 1;       
        
        #200 $stop;
    end
endmodule

