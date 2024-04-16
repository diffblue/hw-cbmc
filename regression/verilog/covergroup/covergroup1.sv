module main;

  wire clk, some_signal;

  covergroup cg @(posedge clk);
    coverpoint some_signal;
  endgroup

endmodule
