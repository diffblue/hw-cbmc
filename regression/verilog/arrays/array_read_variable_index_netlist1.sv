// An element of an unpacked array that a combinational block writes is
// read with a variable index. The netlist-based engines failed with
// "failed to find identifier __CPROVER_internal_actual_array_0[0] in var_map".
module main(input clk, input [3:0] d, input [1:0] i);
  logic [3:0] m [0:3];
  logic [3:0] n;
  always @* begin m[0] = d; m[1] = ~d; m[2] = d + 1; m[3] = 4'd7; n = m[i]; end
  reg [3:0] r = 0;
  always @(posedge clk) r <= n;   // a latch, for IC3
  p0: assert property (@(posedge clk) n == (i == 0 ? d : i == 1 ? ~d : i == 2 ? d + 4'd1 : 4'd7));
  p1: assert property (@(posedge clk) n == d);          // fails
  p2: assert property (@(posedge clk) i == 3 -> n == 7);
  p3: assert property (@(posedge clk) r != 4'd7);       // fails after one step
endmodule
