module queue_module(
    input  logic        clk,        
    input  logic        reset_n,    
    input  logic        a,          
    output logic [7:0] last_value, 
    output logic [7:0] popped_value // Output to store the value that was popped
);
    // Define a queue to hold values
    logic [7:0] q[$];  // Dynamic size queue

    // Process to manage queue operations
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            // Clear the queue on reset
          if (q.size() > 0) //begin
               // q.delete(0, q.size()-1); // Clear all elements in the queue
           // end
            popped_value <= 8'h00;    // Reset the popped value
            last_value <= 8'h00;      // Reset the last value
        end else begin
            if (a) begin
                // Push a new value to the queue when 'a' is high
                q.push_back(8'h08);  // Example value
            end 
            if (!a && q.size() > 0) begin
                // Pop the last value from the queue when 'a' is low
                popped_value <= q[$-1]; // Store the value to be popped
                //q.pop_back();           // Remove the last element from the queue
            end
            
            // Update last_value in procedural context
            last_value <= (q.size() > 0) ? q[$-1] : 8'h00; // Get the last element
        end
    end
endmodule
