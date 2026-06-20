module M(ref [31:0] some_ref, input clk);
  always_ff @(posedge clk)
    some_ref++;
endmodule

module main(input clk);
  bit [31:0] some_var;
  initial some_var = 1;
  M m(some_var, clk);

  // This should fail
  p0: assert property (@(posedge clk) some_var == 1);
endmodule
