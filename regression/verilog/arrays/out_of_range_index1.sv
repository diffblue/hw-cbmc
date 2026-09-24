module main(input clk, input [2:0] idx);

  bit [3:0] mem [0:3];

  initial begin
    mem[0] = 1;
    mem[1] = 2;
    mem[2] = 3;
    mem[3] = 4;
  end

  assume property (idx == 5);

  // 1800-2017 7.4.6: reading from an out-of-range index yields the
  // default value of the element type, which is 0 for 2-state types.
  p0: assert property (mem[idx] == 0);

endmodule
