module main(in);

  reg [31:0] out;
  input [7:0] in;
  
  always @in
    out = { 4 { in } };
    
  always assert property1:
    out==({24'b0, in} | (in<<8) | (in<<16) | (in<<24));

  // 1-replication
  always assert property2:
    {{ 1 { in }}, in } == { in, in };

  // 0-replication
  always assert property3:
    {{ 0 { in }}, in } == { in };

  // replication of something boolean
  always assert property4:
    {{ 1 { 1'b0 }}, in } == in;

  // constant folding
  parameter P = { 2 { 2'b01 } };

  wire [P:0] some_wire;

  always assert property5:
    P == 'b0101;

endmodule
