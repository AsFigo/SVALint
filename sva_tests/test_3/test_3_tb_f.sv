module tb_m;
    logic clk;
    logic rst_n;
    logic in_signal;
    logic out_signal;
 
    always #5 clk = ~clk;

    m_simple dut (
        .clk(clk),
        .rst_n(rst_n),
        .in_signal(in_signal),
        .out_signal(out_signal)
    );

  
    property assume_reset_deasserted_before_signal;
        @(posedge clk) disable iff (!rst_n)
            $rose(in_signal) |-> rst_n;
    endproperty

    assume property (assume_reset_deasserted_before_signal);

   
    initial begin
      
        clk = 0;
        rst_n = 0;
        in_signal = 0;

       
        #10 clk=1;rst_n = 1;

    
        #15 in_signal = 1;
        #10 in_signal = 0;
        
       #10 $display("Time: %0t | clk: %b | rst_n: %b | in_signal: %b | out_signal: %b",
                    $time, clk, rst_n, in_signal, out_signal);
        #50 $finish;
    end

endmodule

