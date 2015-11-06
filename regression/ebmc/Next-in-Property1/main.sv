module top(input clk);
  
  reg [7:0] counter;
  
  always @(posedge clk)
    if(counter<5)
      counter=counter+1;

  initial counter=0;

  // this will hold for any bound
  p1: assert property (counter[0] |-> ##1 counter<=5); 

endmodule
