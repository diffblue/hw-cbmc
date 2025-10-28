module main;

  localparam [7:0] foo = 1;
  parameter [7:0] bar = 2;

  // Parameters with type are "assignment contexts"
  localparam [7:0] baz = 1'b1 + 1'b1;

  always assert property1: $bits(foo) == 8;
  always assert property2: $bits(bar) == 8;
  always assert property3: baz == 2;

endmodule
