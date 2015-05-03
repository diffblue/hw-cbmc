module main(in);

  reg [31:0] out;
  input [7:0] in;
  
  always @in
    out = { 4 { in } };
    
  always assert property1:
    out==(in | (in<<8) | (in<<16) | (in<<24));

  // 1-replication
  always assert property2:
    {{ 1 { in }}, in } == { in, in };

  // replication of something boolean
  always assert property3:
    {{ 1 { 1'b0 }}, in } == in;

endmodule
