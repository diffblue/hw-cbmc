module main(input clk);

  reg [31:0] counter;
  
  always @(posedge clk)
    if(counter<10)
      counter=counter+1;

  initial counter=0;
  
  my_prop1: assert property (counter<=10);
  my_prop2: assert property (counter<10);

endmodule 
