package p;
  typedef enum logic [1:0] { A, B, C } e_t;
endpackage

module main;

  // a cast to a type declared in a package, 1800-2017 6.24.1
  wire [1:0] y = p::e_t'(2);

  p0: assert property (y == p::C);

endmodule
