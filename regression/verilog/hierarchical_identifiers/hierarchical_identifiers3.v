module Msubsub;

  wire [31:0] magic_number = -1;

endmodule

module Msub;
  reg [31:0] out;
  wire x;

  Msubsub subsub();

  always @x out = subsub.magic_number;

endmodule

module main;
  wire [31:0] bin;

  assign bin=sub.out;

  Msub sub();

  always assert property1: bin=='hffffffff;

  always assert property2: sub.subsub.magic_number =='hffffffff;

endmodule
