module status_memory_module(
    input  logic        clk,        
    input  logic        reset_n,     
    input  logic        valid,      
    input  logic [7:0] status_addr,  
    output logic        status_active 
);
    
    logic [7:0] status_array[0:255]; 

    
    initial begin
        status_array[0] = 8'h01;
        status_array[1] = 8'h02;
        status_array[2] = 8'h03; 
       
    end

    // Process to check if the status is active
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            status_active <= 1'b0; 
        end else if (valid) begin
            status_active <= 1'b0; 
            // Check if the specified status exists
            for (int i = 0; i < 256; i++) begin
                if (status_array[i] == status_addr) begin
                    status_active <= 1'b1; // Status found
                    break; // Exit loop on finding the status
                end
            end
        end
    end
endmodule
