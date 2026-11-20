module main;

  reg [7:0] x, y;

  task set(output [7:0] out, input [7:0] a = 1, input [7:0] b = 2);
    out = a * 10 + b;
  endtask

  // 1800-2017 13.5.3: an empty position uses the default
  initial begin
    set(x, , 7);
    set(y, 3, );
  end

  p0: assert final (x == 17);
  p1: assert final (y == 32);

endmodule
