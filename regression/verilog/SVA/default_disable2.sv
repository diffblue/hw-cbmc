// A 'default disable iff (expr)' applies to ALL concurrent assertions in
// the module (1800-2017 16.15), including procedural concurrent assertions
// written inside an always block (16.14.6). Whenever the disable condition
// 'rst' holds, the assertion must be disabled, so 'p0' must be PROVED: the
// property 'rst == 0' is only checked while 'rst' is 0.
//
// Observed: ebmc REFUTES p0, i.e. the default disable iff is NOT applied to
// the procedural concurrent assertion. (A module-level assertion with the
// same default disable iff is correctly PROVED.)
module main(input clk, input rst);
  default disable iff (rst);
  always @(posedge clk) begin
    p0: assert property (rst == 0); // disabled when rst
  end
endmodule
