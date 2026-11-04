module main;

  // a named generate-if block
  if (1) begin : some_block
    wire x = 1;
  end

  wire y = some_block.x;

  initial p0: assert (y == 1);

endmodule
