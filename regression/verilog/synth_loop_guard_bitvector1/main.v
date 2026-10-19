// Synthesis of a for loop whose loop variable is a bit-vector reg (not an
// integer), initialised with a replication expression. Synthesis has to
// constant-fold the guard and increment across iterations to unroll the loop;
// this requires the Verilog-aware simplifier to reduce the replication
// {DW-1{1'b0}} in the initialiser to a constant.
// Minimal reproduction of blocks/lfsr (rtl/lfsr.v:235) and blocks/ethmac
// (rtl/eth_lfsr.v:235):
//   for(data_mask = {1'b1, {DW-1{1'b0}}}; data_mask != 0;
//       data_mask = data_mask >> 1)
module main;

  parameter DW = 8;

  // Counts how many bit positions the walking-one mask visits: exactly DW.
  function [DW-1:0] popcount(input [31:0] dummy);
    reg [DW-1:0] data_mask;
    begin
      popcount = 0;
      for(data_mask = {1'b1, {DW-1{1'b0}}}; data_mask != 0;
          data_mask = data_mask >> 1)
        popcount = popcount + 1;
    end
  endfunction

  wire [DW-1:0] r = popcount(0);

  always assert p1: r == DW;

endmodule
