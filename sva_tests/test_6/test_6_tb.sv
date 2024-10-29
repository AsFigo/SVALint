module tb_fifo;
    parameter DEPTH = 4;
    parameter WIDTH = 8;

    logic clk, rst_n;
    logic write_en, read_en;
    logic [WIDTH-1:0] data_in;
    logic [WIDTH-1:0] data_out;
    logic empty, full;

    fifo #(DEPTH, WIDTH) dut (
        .clk(clk),
        .rst_n(rst_n),
        .write_en(write_en),
        .data_in(data_in),
        .read_en(read_en),
        .data_out(data_out),
        .empty(empty),
        .full(full)
    );

   
    always #5 clk = ~clk;

    initial begin
        clk = 0;
        rst_n = 0;
        write_en = 0;
        read_en = 0;
        data_in = 0;

      
        #10 rst_n = 1;

        repeat (4) begin
            @(posedge clk);
            write_en = 1;
            data_in = $random;
        end
        write_en = 0;

      
        repeat (4) begin
            @(posedge clk);
            read_en = 1;
        end
        read_en = 0;

        #20 $finish;
    end

    initial begin
        $monitor("Time=%0t | write_en=%b | read_en=%b | data_in=%h | data_out=%h | empty=%b | full=%b", 
                  $time, write_en, read_en, data_in, data_out, empty, full);
    end
endmodule

