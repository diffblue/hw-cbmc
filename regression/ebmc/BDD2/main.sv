module main(input clk, input [31:0] a);

  reg [31:0] counter;
  
  always @(posedge clk)
    if(a<100 && counter<100)
      counter=counter+a;

  initial counter=0;
  
  my_prop1: assert property (counter<199);
  my_prop2: assert property (counter<198);

endmodule 
