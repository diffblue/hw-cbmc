module main;

  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;

  pair_t a [2];
  logic [7:0] b [2];

  // 1800-2017 6.22.1: the element types do not have the same number of
  // bits, and hence the two unpacked arrays are not of equivalent types.
  // 1800-2017 7.6 does not allow the assignment.
  initial b = a;

endmodule
