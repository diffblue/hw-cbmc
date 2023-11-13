module main(input [3:0] data);

  reg [$bits(data)-1:0] copy = data;

  always assert property1: $bits(copy) == 4;

endmodule
