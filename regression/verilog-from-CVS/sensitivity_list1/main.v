module main(in1, in2);

  input [31:0] in1, in2;
  reg [31:0] x, y, z;

  // Verilog 2001  
  always @(in1, in2)
    x=in1 | in2;

  // Verilog 2001  
  always @(*)
    y=in1 | in2;

  always @*
    z=in1 | in2;
    
  always assert p1: x==y;

endmodule
