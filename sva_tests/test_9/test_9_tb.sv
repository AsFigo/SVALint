module tb_memory;
    parameter DEPTH = 16;
    parameter WIDTH = 8;
    logic clk, rst_n;
    logic write_en;
    logic [$clog2(DEPTH)-1:0] addr;
    logic [WIDTH-1:0] data_in;
    logic [WIDTH-1:0] data_out;

    // DUT Instantiation
    memory #(DEPTH, WIDTH) dut (
        .clk(clk),
        .rst_n(rst_n),
        .write_en(write_en),
        .addr(addr),
        .data_in(data_in),
        .data_out(data_out)
    );
    always #5 clk = ~clk;

    initial begin
        
        clk = 0;
        rst_n = 0;
        write_en = 0;
        addr = 0;
        data_in = 0;
        #10 rst_n = 1;
        for (int i = 0; i < DEPTH; i++) begin
            @(posedge clk);
            write_en = 1;
            addr = i;
            data_in = i * 2;  
        end
        write_en = 0;

        for (int i = 0; i < DEPTH; i++) begin
            @(posedge clk);
            addr = i;
            #1 $display("Read Address %0d: Data Out = %h", i, data_out);
        end

        #20 $finish;
    end
endmodule

