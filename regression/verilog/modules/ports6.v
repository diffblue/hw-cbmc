// The type of the input port symbol 'data' must be
// available during constant elaboration.
module main(input [3:0] data1, input [$bits(data1)-1:0] data2);

  always assert property1: $bits(data2) == 4;

endmodule
