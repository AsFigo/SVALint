module tb_fifo_pass;
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

    // Clock generation
    always #5 clk = ~clk;

    initial begin
        clk = 0;
        rst_n = 0;
        write_en = 0;
        read_en = 0;
        data_in = 0;

        // Reset
        #10 rst_n = 1;

        // Write data
        repeat (4) begin
            @(posedge clk);
            write_en = 1;
            data_in = $random;
        end
        write_en = 0;

        // Read data
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

    // SVA Properties that WILL PASS - these do NOT use q.pop_front
    property fifo_write_pass_prop;
        @(posedge clk) disable iff (!rst_n)
        write_en && !full |-> ##1 !empty;
    endproperty

    property fifo_read_pass_prop;
        @(posedge clk) disable iff (!rst_n)
        read_en && !empty |-> ##1 !full;
    endproperty

    property fifo_data_valid_prop;
        @(posedge clk) disable iff (!rst_n)
        (write_en && !full) |-> ##1 (data_in == data_out || empty);
    endproperty

    property fifo_overflow_prop;
        @(posedge clk) disable iff (!rst_n)
        full |-> !write_en;
    endproperty

    property fifo_underflow_prop;
        @(posedge clk) disable iff (!rst_n)
        empty |-> !read_en;
    endproperty

    // These assertions should NOT trigger the pop_front rule violations
    FIFO_WRITE_PASS: assert property (fifo_write_pass_prop);
    FIFO_READ_PASS: assert property (fifo_read_pass_prop);
    FIFO_DATA_VALID: assert property (fifo_data_valid_prop);
    FIFO_OVERFLOW: assert property (fifo_overflow_prop);
    FIFO_UNDERFLOW: assert property (fifo_underflow_prop);

    // Cover properties
    FIFO_WRITE_PASS_COVER: cover property (fifo_write_pass_prop);
    FIFO_READ_PASS_COVER: cover property (fifo_read_pass_prop);
    FIFO_DATA_VALID_COVER: cover property (fifo_data_valid_prop);
    FIFO_OVERFLOW_COVER: cover property (fifo_overflow_prop);
    FIFO_UNDERFLOW_COVER: cover property (fifo_underflow_prop);

endmodule
