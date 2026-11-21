module main(input clk, input we, input [1:0] addr, input [15:0] din,
            input [15:0] wmask);

  reg [15:0] ram [0:3];
  integer i;

  // Per-bit conditional writes to an element with a variable index. The
  // resulting expressions share subexpressions; lowering them as trees
  // used to take time and memory exponential in the number of bits.
  always @(posedge clk)
    if(we)
      for(i = 0; i < 16; i = i + 1)
        if(wmask[i])
          ram[addr][i] <= din[i];

  initial ram[3] = 0;

  // nothing is written if the mask is zero
  p0: assert property (@(posedge clk) wmask == 0 |=> ram[3] == $past(ram[3]));

endmodule
