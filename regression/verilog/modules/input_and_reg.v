module main;
  // some_var must not be both an input and a reg
  input [31:0] some_var;
  reg [31:0] some_var;
endmodule
