 module no2_within;
   bit go, a, w, y, b, clk;
   initial forever #3 clk = !clk;
   sequence s1; @(posedge clk) w ##1 y; endsequence 
   // No detection for 2 occurrence of 'a'
   ap_1a_within_b: assert property(@ (posedge clk) $rose(go) |=>  (a[=1] within b[->1]));
   ap_a_within_b:  assert property(@ (posedge clk) $rose(go) |=>  (a within b[->1]));
   ap_only1a_within_b:  assert property(@ (posedge clk) $rose(go) |=>  
     (a[->1] ##1 !a[*0:$] intersect b[->1]));

   // Detection for 2 occurrence of 'a'
   ap_within_not2: assert property(@ (posedge clk) $rose(go) |=>
          not ( (1[*0:$] ##1 a[->1])[*2] ##1 1[*0:$]  intersect b[->1]) );

   //------------- s1 within b[->1]
   ap_s1_within: assert property(@ (posedge clk) $rose(go) |=>  s1 within b[->1]);

      //  Detection for 2 occurrence of 's1'       
   ap_not2: assert property(@ (posedge clk) $rose(go) |=> 
        not((1[*0:$] ##1 s1)[*2] ##1 1[*0:$] intersect b[->1] ) );
   
   // For use in ap_no2_s1    
   asm_go_no_wy: assume property(@(posedge clk) $rose(go) |-> !s1.triggered ##1 !y);    

   // Using endpoints; assumng that at rose of go, there is no endpoint
   ap_no2_s1: assert property(@ (posedge clk) $rose(go) |=> 
      (s1.triggered[->1] ##1 !s1.triggered[*0:$]) intersect b[->1] );

   initial begin 
    // {go, a, w, y, b} 
     @(posedge clk) {go, a, w, y, b} <= 5'b00000;
     @(posedge clk) {go, a, w, y, b} <= 5'b10000; // go
     @(posedge clk) {go, a, w, y, b} <= 5'b00000;
     @(posedge clk) {go, a, w, y, b} <= 5'b01000; // a=1
     @(posedge clk) {go, a, w, y, b} <= 5'b00100; // w=1
     @(posedge clk) {go, a, w, y, b} <= 5'b00010; //y=1
     @(posedge clk) {go, a, w, y, b} <= 5'b00000;
     @(posedge clk) {go, a, w, y, b} <= 5'b00001;  // b=1
    // 2 s1
     @(posedge clk) {go, a, w, y, b} <= 5'b00000;
     @(posedge clk) {go, a, w, y, b} <= 5'b10000;
     @(posedge clk) {go, a, w, y, b} <= 5'b00000;
     @(posedge clk) {go, a, w, y, b} <= 5'b01000; // a=1
     @(posedge clk) {go, a, w, y, b} <= 5'b00000;
     @(posedge clk) {go, a, w, y, b} <= 5'b00100; // w=1
     @(posedge clk) {go, a, w, y, b} <= 5'b00010; // y=1
     @(posedge clk) {go, a, w, y, b} <= 5'b01000;  // a=1
     @(posedge clk) {go, a, w, y, b} <= 5'b00100; // w=1
     @(posedge clk) {go, a, w, y, b} <= 5'b00010; // y=1
     @(posedge clk) {go, a, w, y, b} <= 5'b00100; // w=1
     @(posedge clk) {go, a, w, y, b} <= 5'b00000;
     @(posedge clk) {go, a, w, y, b} <= 5'b00001;  // b=1
    // 
     @(posedge clk) {go, a, w, y, b} <= 5'b00000;
     #10 $finish;
    end
 endmodule