module main(input clk, reset, input data);

  reg y;

  // combinational only, no need to unwind
  always_comb @data begin
    y = data;
    // should fail when data is false
    p0: assert(y);
  end

  // but we have an assumption in the reset state!
  assume property (@(posedge clk) reset -> data);

endmodule
