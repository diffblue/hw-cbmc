// let with ports, with non-constant arguments, 1800-2017 11.12

module main(input clk, input [7:0] x, input [7:0] y);

  let add(a, b) = a + b;
  let sub(a, b) = a - b;

  // in a continuous assignment
  wire [7:0] s = add(x, y);

  // in a procedural assignment
  reg [7:0] r;
  initial r = 0;
  always @(posedge clk) r <= add(r, 1);

  p0: assert final (add(x, y) == x + y);

  // the substitution is simultaneous
  wire [7:0] a = y, b = x;
  p1: assert final (sub(b, a) == x - y);

  // named arguments
  p2: assert final (sub(.b(x), .a(y)) == y - x);

  // nested let instances
  p3: assert final (add(sub(x, y), y) == x);

  p4: assert property (@(posedge clk) s == x + y);
  p5: assert property (@(posedge clk) r != 3);

endmodule
