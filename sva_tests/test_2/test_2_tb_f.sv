module counter_tb;
   
    logic clk;             
    logic reset_n;          
    logic enable;           
    logic [7:0] counter;     
    always #5 clk = ~clk;  

    
    counter_module uut (
        .clk(clk),
        .reset_n(reset_n),
        .enable(enable),
        .counter(counter)
    );

 
    property p_counter_within_limit;
        @(posedge clk) disable iff (!reset_n) (counter <= 100);
    endproperty

    // Assertion using the property with a_ prefix for the name
    counter_limit_check: assert property (p_counter_within_limit)
        else $error("Assertion Failed: Counter exceeds the maximum allowed value!");

    
    initial begin
        
        clk = 0;
        reset_n = 0;
        enable = 0;        
        #10 reset_n = 1;   
        #10 enable = 1; 
       
        #100;              

        // Force counter value to exceed the limit for testing
        #10 enable = 0;    // Disable counter
        uut.counter = 8'd120;  // Force counter to exceed the limit for testing
        
        #10 enable = 1;    
        #20 $finish;      
    end
endmodule
