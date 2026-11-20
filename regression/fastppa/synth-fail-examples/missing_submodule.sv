// Category: missing sub-module
// Error: "module not found"
// Cause: Module instantiates a sub-module not in the provided files.
// All 160 failures from TinyRocket are this category when modules
// are extracted individually.
// Fix: provide all Verilog files, or flatten before estimation.

module sub_module(input [7:0] a, output [7:0] y);
  assign y = a + 8'd1;
endmodule

module top_with_submod(input clk, input [7:0] din, output reg [7:0] dout);
  wire [7:0] inc;
  sub_module u0(.a(din), .y(inc));
  always @(posedge clk) dout <= inc;
endmodule
