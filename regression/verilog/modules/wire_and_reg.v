module main;
  // some_var must not be both wire and reg
  wire [31:0] some_var;
  reg [31:0] some_var;
endmodule
