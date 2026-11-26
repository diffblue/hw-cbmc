// The type given at the instantiation does not match the restriction
typedef struct packed { logic [7:0] f; } struct_t;
typedef union packed { logic [7:0] f; } union_t;

module sub #(parameter type struct S = struct_t);
endmodule

module main;
  sub #(.S(union_t)) inst();
endmodule
