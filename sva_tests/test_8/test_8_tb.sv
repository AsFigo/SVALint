module memory_tb;
    
    logic clk;                 
    logic reset_n;            
    logic [7:0] addr;         
    logic valid;               
    logic v_err;              

    always #5 clk = ~clk;      
    memory_module uut (
        .clk(clk),
        .reset_n(reset_n),
        .addr(addr),
        .valid(valid),
        .v_err(v_err)
    );

    // Property declaration: Check if the address exists in the memory
    property p_check_address_exists;
        @(posedge clk) disable iff (!reset_n) (valid |-> !(v_err));
    endproperty

    // Assertion using the property with a_ prefix for the name
    a_check_address_exists: assert property (p_check_address_exists)
        else $error("Assertion Failed: Address does not exist in memory!");

    
    initial begin
        // Initialize signals
        clk = 0;
        reset_n = 0;
        addr = 8'h00;
        valid = 0;        
        #10 reset_n = 1;          
        #10 addr = 8'h01; valid = 1; 
        #10 valid = 0; 
        #10 addr = 8'hFF; valid = 1;
        #10 valid = 0;
        #10 $finish;
    end
endmodule
