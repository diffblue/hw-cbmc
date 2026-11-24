module main(input [7:0] d, input [31:0] k);

  // A write to an unpacked array with a variable index that may be
  // outside the declared range. Per 1800-2017 7.4.6, writing to an array
  // with an invalid index shall perform no operation.
  reg [7:0] q [0:15];
  integer i;

  always @* begin
    for(i = 0; i < 16; i = i + 1)
      q[i] = 0;
    q[k] = d;
  end

  p0: assert final (k >= 16 -> q[3] == 0);

endmodule
