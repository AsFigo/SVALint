module memory #(parameter DEPTH = 16, WIDTH = 8) (
    input logic                     clk,
    input logic                     rst_n,
    input logic                     write_en,
    input logic [$clog2(DEPTH)-1:0] addr,
    input logic [WIDTH-1:0]         data_in,
    output logic [WIDTH-1:0]        data_out
);
    
    logic [WIDTH-1:0] mem [0:DEPTH-1];

   
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            for (int i = 0; i < DEPTH; i++) begin
                mem[i] <= '0;
            end
        end else if (write_en) begin
       
            mem[addr] <= data_in;
        end
    end

  
    assign data_out = mem[addr];  
endmodule
