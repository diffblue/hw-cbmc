module main(input [3:0] data);

  // The type of the input port symbol 'data' must be
  // available during constant elaboration.
  localparam data_width = $bits(data);
  reg [$bits(data)-1:0] copy = data;

  always assert property1: $bits(copy) == 4;

endmodule
