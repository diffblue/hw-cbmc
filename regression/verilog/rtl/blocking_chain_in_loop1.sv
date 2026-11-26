module main(input [31:0] d, input [31:0] x0);

  // Each iteration reads x twice. The value of x after the loop is a
  // DAG of size linear in the number of iterations, but RTL construction
  // used to take time and memory exponential in it.
  reg [31:0] x;
  integer i;

  always @* begin
    x = x0;
    for(i = 0; i < 32; i = i + 1)
      x = (x >> 1) ^ (32'hEDB88320 & {32{x[0] ^ d[i]}});
  end

  // CRC-32 of the zero word with initial value zero is zero
  p0: assert property (d == 0 && x0 == 0 -> x == 0);

endmodule
