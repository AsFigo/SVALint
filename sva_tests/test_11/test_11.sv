module event_monitor(
    input  logic clk,            
    input  logic reset_n,        
    input  logic enable,         
    input  logic data_signal,     
    output logic event_occurred  
);
   
    

    // Always block to set the event_occurred based on conditions
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            event_occurred <= 1'b0; 
        end else if (enable) begin
            if (data_signal) begin
                event_occurred <= 1'b1; 
            end else begin
                event_occurred <= 1'b0;
            end
        end
    end
endmodule
