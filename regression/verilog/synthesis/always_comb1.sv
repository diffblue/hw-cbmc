module main(input [7:0] data1);

  logic [7:0] data2;
  always_comb data2 = data1;

  p1: assert property (data2 == data1);

endmodule
