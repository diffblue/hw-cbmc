// Restricted type parameters in a parameter declaration in the module
// body, and as localparam (IEEE 1800-2023 6.20.3)
typedef struct packed { logic [3:0] f; } struct_t;

module main;
  parameter type struct S = struct_t;
  localparam type struct L = struct_t;

  S s;
  L l;

  p0: assert final ($bits(s) == 4 && $bits(l) == 4);
endmodule
