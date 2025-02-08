module main(input clock, reset);

  default clocking cb @(posedge clk);
  endclocking
  default disable iff (!reset);

endmodule
