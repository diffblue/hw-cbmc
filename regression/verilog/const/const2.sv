module main(input clk, input [31:0] data);

  // The value need not be constant.
  const reg [31:0] data_const = data;

  // 1800 2017 6.20.6
  always @(posedge clk)
    // But can't assign to it.
    data_const = 123;

endmodule
