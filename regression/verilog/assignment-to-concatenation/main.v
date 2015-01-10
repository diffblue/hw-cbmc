module main(in);

  reg [2:0] out1;
  input [2:0] in;
  
  // bits only
  always @in
    {out1[2],out1[1],out1[0]} = 3'b100;

  always assert property1: out1==4;
  
  // also vectors
  reg [2:0] out2;
  
  always @in
    {out2[2:1],out2[0]} = 3'b100;
  
  always assert property2: out2==4;

endmodule
