// A mux (?:) whose operands are struct-typed, not bool/bitvector.
module struct_mux(input clk, input sel, input [63:0] a_in, b_in,
                   output [63:0] out);
  typedef struct packed {
    logic [31:0] hi;
    logic [31:0] lo;
  } pair_t;

  pair_t a, b, out_reg;

  always @(posedge clk) begin
    a <= a_in;
    b <= b_in;
    out_reg <= sel ? a : b;
  end

  assign out = out_reg;
endmodule
