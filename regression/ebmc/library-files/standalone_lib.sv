// This module is not instantiated by any non-library module.
// Without -l, it would be considered a top-level module.
// With -l, it should NOT be considered top-level.
module standalone_lib(input clk);

  reg [3:0] cnt;

  initial cnt = 0;

  always @(posedge clk) cnt = cnt + 1;

  p_lib: assert property (@(posedge clk) cnt < 15);

endmodule
