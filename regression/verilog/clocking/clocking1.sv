module main(input clk);

  clocking my_clocking @(posedge clk);
  endclocking

  // The identifier is optional.
  default clocking @(posedge clk);
  endclocking

endmodule
