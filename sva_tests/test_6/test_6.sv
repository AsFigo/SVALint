module fifo #(parameter DEPTH = 4, WIDTH = 8) (
    input logic        clk,
    input logic        rst_n,
    input logic        write_en,
    input logic [WIDTH-1:0] data_in,
    input logic        read_en,
    output logic [WIDTH-1:0] data_out,
    output logic       empty,
    output logic       full
);
    logic [WIDTH-1:0] memory [DEPTH-1:0];
    logic [$clog2(DEPTH):0] read_ptr, write_ptr;
    logic [$clog2(DEPTH+1):0] count;

    assign empty = (count == 0);
    assign full  = (count == DEPTH);
    assign data_out = (read_en && !empty) ? memory[read_ptr] : '0;
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            read_ptr <= 0;
            write_ptr <= 0;
            count     <= 0;
        end else begin
            if (write_en && !full) begin
                memory[write_ptr] <= data_in;
                write_ptr <= (write_ptr + 1) % DEPTH;
                count <= count + 1;
            end
            if (read_en && !empty) begin
                read_ptr <= (read_ptr + 1) % DEPTH;
                count <= count - 1;
            end
        end
    end
endmodule

