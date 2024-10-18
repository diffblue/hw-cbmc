module alu(input [1:0] op, input [31:0] a, b, output reg [31:0] out);

  always_comb case(op)
    0: out = a + b;
    1: out = a - b;
    2: out = a >> b;
    3: out = a << b;
  endcase;

  wire clk;
  always @(posedge clk) case(op)
    default:;
    0: assert(out == a + b);
    1: assert(out == a - b);
    2: assert(out == a >> b);
    3: assert(out == a << b);
  endcase;

endmodule
