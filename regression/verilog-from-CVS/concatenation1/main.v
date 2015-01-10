module main(in1, in2);

  reg [31:0] out;
  input [15:0] in1;
  input [15:0] in2;
  
  always @in1
    out = { in2, in1 };

  always assert property1: out == ((in2<<16)|in1);

  always assert property2: {4'b1001,4'b1011}==8'b10011011;

endmodule
