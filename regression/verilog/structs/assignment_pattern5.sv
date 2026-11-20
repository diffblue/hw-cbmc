module main;

  typedef struct packed {
    logic [7:0] a;
    logic [7:0] b;
  } s_t;

  s_t v;
  assign v = '{default: 8'h56};

  p0: assert property (v == 16'h5656);

endmodule
