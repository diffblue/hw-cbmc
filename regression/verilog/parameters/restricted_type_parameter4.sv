// The default type does not match the restriction
typedef struct packed { logic [7:0] f; } struct_t;

module main #(parameter type enum E = struct_t);
endmodule
