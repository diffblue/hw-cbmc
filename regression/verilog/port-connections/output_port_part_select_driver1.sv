module sub(input [3:0] i, output [3:0] o);
  assign o = i;
endmodule

module main(input clk);
  reg [7:0] counter = 0;
  always @(posedge clk) counter <= counter + 1;

  wire [7:0] v;
  sub s(.i(counter[3:0]), .o(v[3:0]));   // driven by the child's output port
  assign v[7:4] = 4'd0;                  // driven by a continuous assignment

  p0: assert property (@(posedge clk) counter != 5);
  p1: assert property (@(posedge clk) v != 5);
endmodule
