module main;

  reg [7:0] x, y, z;

  task set(output [7:0] out, input [7:0] value = 42);
    out = value;
  endtask

  initial begin
    set(x);           // uses the default
    set(y, 7);        // overrides the default
    set(.out(z));     // named argument, uses the default
  end

  p0: assert final (x == 42);
  p1: assert final (y == 7);
  p2: assert final (z == 42);

endmodule
