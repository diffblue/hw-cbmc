module M (out);
  parameter size=8;
  output [size-1:0] out;
  reg [size-1:0] out;
  wire x;

  always @x out=-1;

endmodule

module main;
  wire [31:0] bin;

  M #(32) m(bin);
  
  always assert property1: bin=='hffffffff;

endmodule
