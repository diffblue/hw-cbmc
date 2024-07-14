module main;

  wire [1:8] vector = 1;
  wire [7:0] index;

  // Non-constant index.
  // Note that index 8 is the least significant bit.
  p0: assert final (index == 8 -> vector[index] == 1);

  // Verilog guarantees that any out-of-bounds access is zero.
  p1: assert final (index >= 1 && index <= 7 -> vector[index] == 0);

endmodule
