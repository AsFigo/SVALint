module event_monitor_tb;
    
    logic clk;                 
    logic reset_n;             
    logic enable;             
    logic data_signal;         
    logic event_occurred;      

    
    always #5 clk = ~clk; 

    
    event_monitor uut (
        .clk(clk),
        .reset_n(reset_n),
        .enable(enable),
        .data_signal(data_signal),
        .event_occurred(event_occurred)
    );

    // Property declaration: Ensure that event occurs within a few cycles after enable
    property p_event_occurs;
        @(posedge clk) disable iff (!reset_n) 
        (enable |-> (data_signal |=> event_occurred)); // |=> operator to check for the condition, which helps avoid complications that can arise with s_until_with.
    endproperty

    // Assertion using the property with a_ prefix for the name
    a_event_occurs: assert property (p_event_occurs)
        else $error("Assertion Failed: data_signal did not occur as expected after enable!");

    
    initial begin
        clk = 0;
        reset_n = 0;
        enable = 0;
        data_signal = 0;

        
        #10 reset_n = 1;   

        // Stimulate inputs
        #10 enable = 1; data_signal = 0; 
        #10 data_signal = 1; 
        #10 enable = 0; 
        #10 data_signal = 0; 
        #10 enable = 1; data_signal = 1; 
        #10 enable = 0; 
        #10 $finish; 
    end
endmodule
