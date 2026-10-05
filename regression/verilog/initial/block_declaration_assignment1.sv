// A static variable declared inside a procedural block with an
// initializer. Per IEEE 1800-2017 6.21 and 10.5, a static variable
// declaration assignment happens once before any initial or always
// procedure starts, exactly like a module-level variable with an
// initializer. Hence tmp holds 5 and y becomes 5 after the first clock
// edge, so the property must be PROVED.
module main(input clk);

  reg [3:0] y;

  always @(posedge clk) begin
    reg [3:0] tmp = 4'd5;
    y <= tmp;
  end

  p0: assert property (@(posedge clk) ##1 y == 5);

endmodule
