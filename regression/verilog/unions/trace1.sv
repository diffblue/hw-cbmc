module main(input clk);

  union packed {
    bit [7:0] field1;
    bit [7:0] field2;
  } u;

  // bit-vectors can be converted without cast to packed unions
  initial u = 1;

  always_ff @(posedge clk)
    u.field2++;

  assert property (@(posedge clk) u.field1 != 3);

endmodule
