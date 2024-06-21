module main;
  parameter N=4;
  parameter WIDTH=4;
  parameter X=(1 << WIDTH);

  wire [N*WIDTH-1:0] w='hffff;

  always assert property1: w=='hffff;
  
  always assert property2: X==16;

endmodule
