module top(input clk);

  reg [63:0] counter;

  initial counter=0;

  always @(posedge clk)
    counter=counter+1;

endmodule
