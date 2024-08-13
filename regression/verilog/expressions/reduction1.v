module main(input [31:0] in);

  // reduction and
  always assert reduction_and1:
    &3'b111 == 1 && &3'b101 == 0;

  // constant folding
  wire [&3'b111:0] wire_and;

  // reduction nand
  always assert reduction_nand1:
    ~&in == !(&in);

  // constant folding
  wire [~&3'b111:0] wire_nand;

  // reduction or
  always assert reduction_or1:
    |3'b000 == 0 && |3'b101 == 1;

  // constant folding
  wire [|3'b101:0] wire_or;

  // reduction nor
  always assert reduction_nor1:
    ~|in == !(|in);

  // constant folding
  wire [~|3'b000:0] wire_nor;

  // reduction xor
  always assert reduction_xor1:
    ^3'b000 == 0 && ^3'b111 == 1;

  // constant folding
  wire [^3'b111:0] wire_xor;

  // reduction xnor, variant 1
  always assert reduction_xnor1:
    ~^in == !(^in);

  // constant folding
  wire [~^3'b000:0] wire_xnor1;

  // reduction xnor, variant 2
  always assert reduction_xnor2:
    ^~in == !(^in);

  // constant folding
  wire [^~3'b000:0] wire_xnor2;

endmodule
