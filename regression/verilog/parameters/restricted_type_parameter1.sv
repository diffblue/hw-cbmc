// Restricted type parameters (IEEE 1800-2023 6.20.3)
typedef enum { A, B } enum_t;
typedef struct packed { logic [7:0] f; } struct_t;
typedef union packed { logic [7:0] f; logic [7:0] g; } union_t;

module sub #(
  parameter type enum E = enum_t,
  parameter type struct S = struct_t,
  parameter type union U = union_t
);
  E e;
  S s;
  U u;
endmodule

module main;
  sub inst();
  p0: assert final ($bits(inst.s) == 8 && $bits(inst.u) == 8 && $bits(inst.e) == 32);
endmodule
