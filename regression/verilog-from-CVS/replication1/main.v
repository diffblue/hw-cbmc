module main(in);

  reg [31:0] out;
  input [7:0] in;
  
  always @in
    out = { 4 { in } };
    
  always assert property1:
    out==(in | (in<<8) | (in<<16) | (in<<24));

endmodule
