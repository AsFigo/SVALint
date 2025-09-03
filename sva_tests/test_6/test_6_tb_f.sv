module tb_fifo_fail;
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

    // SVA Properties that WILL FAIL - these use q.pop_front
    property fifo_queue_fail_prop1;
        @(posedge clk) disable iff (!rst_n)
        (write_en && !full, q.push_back(data_in)) |-> ##1 (read_en && !empty, q.pop_front());
    endproperty

    property fifo_queue_fail_prop2;
        @(posedge clk) disable iff (!rst_n)
        (read_en && !empty) |-> ##1 q.pop_front();
    endproperty

    property fifo_queue_fail_prop3;
        @(posedge clk) disable iff (!rst_n)
        (write_en && !full) |-> ##1 (q.push_back(data_in), q.pop_front());
    endproperty

    // These assertions should trigger the pop_front rule violations
    FIFO_QUEUE_FAIL_1: assert property (fifo_queue_fail_prop1);
    FIFO_QUEUE_FAIL_2: assert property (fifo_queue_fail_prop2);
    FIFO_QUEUE_FAIL_3: assert property (fifo_queue_fail_prop3);

    // Cover properties
    FIFO_QUEUE_FAIL_1_COVER: cover property (fifo_queue_fail_prop1);
    FIFO_QUEUE_FAIL_2_COVER: cover property (fifo_queue_fail_prop2);
    FIFO_QUEUE_FAIL_3_COVER: cover property (fifo_queue_fail_prop3);

endmodule
