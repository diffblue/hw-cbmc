module main;

  localparam [7:0] foo = 1;
  parameter [7:0] bar = 2;

  always assert property1: $bits(foo) == 8;
  always assert property2: $bits(bar) == 8;

endmodule
