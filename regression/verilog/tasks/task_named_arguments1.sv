module main;

  reg [7:0] x, y, z;

  task sub(output [7:0] out, input [7:0] a, input [7:0] b);
    out = a - b;
  endtask

  initial begin
    sub(.b(3), .a(10), .out(x)); // named, in reverse order
    sub(y, .b(1), .a(5));        // ordered, then named
    sub(z, 9, 4);                // all ordered
  end

  p0: assert final (x == 7);
  p1: assert final (y == 4);
  p2: assert final (z == 5);

endmodule
