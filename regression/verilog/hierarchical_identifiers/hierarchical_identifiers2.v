module main;

  // a named generate-if block
  if (1) begin : some_block
    wire x;
  end

  wire y = some_block.x;

endmodule
