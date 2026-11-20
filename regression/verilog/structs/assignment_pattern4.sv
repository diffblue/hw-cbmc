module main;

  typedef struct packed {
    logic [7:0] a;
    logic [7:0] b;
  } s_t;

  // 1800-2017 10.9.2: a default key applies to the members that are not
  // named explicitly
  s_t v;
  assign v = '{a: 8'h12, default: 8'h34};

  p0: assert property (v == 16'h1234);

endmodule
