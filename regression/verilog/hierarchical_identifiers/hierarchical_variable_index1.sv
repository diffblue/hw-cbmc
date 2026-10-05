// Procedural assignment to a hierarchical identifier that selects an array
// element with a non-constant index, i.e. s.mem[i] <= ...
//
// Writing to another module's variable through a hierarchical identifier is
// permitted (IEEE 1800-2017, 23.6 "Hierarchical names" and 23.7 "Member
// selects and hierarchical names").  The same assignment with a constant
// index (s.mem[2] <= ...) is accepted, and the equivalent local write
// mem[i] <= ... (see regression/verilog/assignments/
// assignment-to-non-constant-index1) is accepted, so the hierarchical form
// with a variable index must be accepted too and the property must hold.
module sub(input clk);
  reg [7:0] mem [0:3];
endmodule

module main(input clk, input [1:0] i);
  sub s(clk);
  always @(posedge clk) s.mem[i] <= 8'hAB;
  p0: assert property (@(posedge clk) ##1 s.mem[$past(i)] == 8'hAB);
endmodule
