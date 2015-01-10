module main(index);

  reg [31:0] x;
  input [1:0] index;
  wire clk;
  wire my_bit;
  
  initial x='b10000;
  
  always @(posedge clk) x<=x+'b10000;

  assign my_bit=x[index];

  // this should pass
  always assert property1: !my_bit;

endmodule
