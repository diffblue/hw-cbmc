module main;

  reg [7:0] x, y;

  // a void function called as a statement, with a default
  function automatic void f(output [7:0] out, input [7:0] v = 42);
    out = v;
  endfunction

  initial begin
    f(x);
    f(.v(7), .out(y));
  end

  p0: assert final (x == 42);
  p1: assert final (y == 7);

endmodule
