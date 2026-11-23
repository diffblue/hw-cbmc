module main(input clk, input [31:0] d);

  // The next value of x is a DAG of size linear in the number of loop
  // iterations. The instrumentation of $past used to walk it as a tree,
  // taking time exponential in the number of iterations.
  reg [31:0] x, y;
  integer i;

  initial x = 0;

  always @* begin
    y = x;
    for(i = 0; i < 32; i = i + 1)
      y = (y >> 1) ^ (32'hEDB88320 & {32{y[0] ^ d[i]}});
  end

  always @(posedge clk)
    x <= y;

  // CRC-32 of the zero word with initial value zero is zero
  p0: assert property (@(posedge clk) $past(d) == 0 && $past(x) == 0 |-> x == 0);

endmodule
