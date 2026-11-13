module main(input x);

  // A long chain of combinational definitions, where each bit of w
  // depends on the next higher one.
  parameter N = 4000;

  wire [N:0] w;

  assign w[N] = x;

  for(genvar i = 0; i < N; i++)
    assign w[i] = !w[i + 1];

  // N is even
  p0: assert property (w[0] == x);

endmodule
