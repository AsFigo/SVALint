module assoc_array_controller (
    input wire clk,
    input wire reset_n,
    input wire write_en,     // Enable write operation
    input wire read_en,      // Enable read operation
    input wire [3:0] key,    // Key input (integer index)
    input wire [31:0] data_in,   // Data input (value)
    output reg [31:0] data_out,  // Data output
    output reg data_valid        // Flag to indicate valid output data
);

    //Array to store values indexed by integer keys (0-15 for simplicity)
    reg [31:0] data_store [0:15];

    // Write operation
    always @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            // Reset array elements to 0 on reset
            integer i;
            for (i = 0; i < 16; i = i + 1) begin
                data_store[i] <= 32'b0;
            end
            data_out <= 32'b0;
            data_valid <= 0;
        end else if (write_en) begin
            data_store[key] <= data_in;  // Write data to specified key
        end
    end

    // Read operation
    always @(posedge clk) begin
        if (read_en) begin
            data_out <= data_store[key];  // Read data from specified key
            data_valid <= 1;              // Indicate data is valid
        end else begin
            data_valid <= 0;
        end
    end

endmodule

