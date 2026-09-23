module main(input clk, input we, input [1:0] addr, input [7:0] d);

  // A memory with a decreasing range.
  reg [7:0] mem [3:0];

  always @(posedge clk)
    if(we)
      mem[addr] <= d;

  p0: assert property (@(posedge clk) ##1 ($past(we) -> mem[$past(addr)] == $past(d)));

endmodule
