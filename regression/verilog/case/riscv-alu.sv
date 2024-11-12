
module alu(
  input [2:0] func3,
  input [6:0] func7,
  input [63:0] a, b,
  output reg [63:0] out);

  // https://riscv.org/wp-content/uploads/2017/05/riscv-spec-v2.2.pdf
  // Page 104
  wire ADD  = func7 == 'b0000000 & func3 == 'b000;
  wire SUB  = func7 == 'b0100000 & func3 == 'b000;
  wire SLL  = func7 == 'b0000000 & func3 == 'b001;
  wire SLT  = func7 == 'b0000000 & func3 == 'b010;
  wire SLTU = func7 == 'b0000000 & func3 == 'b011;
  wire XOR  = func7 == 'b0000000 & func3 == 'b100;
  wire SRL  = func7 == 'b0000000 & func3 == 'b101;
  wire SRA  = func7 == 'b0100000 & func3 == 'b101;
  wire OR   = func7 == 'b0000000 & func3 == 'b110;
  wire AND  = func7 == 'b0000000 & func3 == 'b111;

  wire subtraction = SUB || SLT || SLTU;
  wire [64:0] a_ext = {SLT ? a[63] : 0, a};
  wire [64:0] b_ext = {SLT ? b[63] : 0, b};
  wire [64:0] b_inv = (subtraction?~b_ext:b_ext);
  wire [64:0] adder_out = a_ext + b_inv + subtraction;

  always_comb case(1)
    ADD || SUB:  out <= adder_out[63:0];
    SLL:         out <= a << b[4:0];
    SLT || SLTU: out <= adder_out[64];
    XOR:         out <= a ^ b;
    SRL:         out <= a >> b[4:0];
    SRA:         out <= $signed(a) >>> b[4:0];
    OR:          out <= a | b;
    AND:         out <= a & b;
    default:     out <= 0;
  endcase

  wire [9:0] op = {func7, func3};
  pADD:  assert final (op == {7'b0000000, 3'b000} -> out == a + b);
  pSUB:  assert final (op == {7'b0100000, 3'b000} -> out == a - b);
  pSLL:  assert final (op == {7'b0000000, 3'b001} -> out == a << b[4:0]);
  pSLT:  assert final (op == {7'b0000000, 3'b010} -> out == ($signed(a) < $signed(b)));
  pSLTU: assert final (op == {7'b0000000, 3'b011} -> out == (a < b));
  pXOR:  assert final (op == {7'b0000000, 3'b100} -> out == (a ^ b));
  pSRL:  assert final (op == {7'b0000000, 3'b101} -> out == a >> b[4:0]);
  pSRA:  assert final (op == {7'b0100000, 3'b101} -> out == $signed(a) >>> b[4:0]);
  pOR:   assert final (op == {7'b0000000, 3'b110} -> out == (a | b));
  pAND:  assert final (op == {7'b0000000, 3'b111} -> out == (a & b));

endmodule
