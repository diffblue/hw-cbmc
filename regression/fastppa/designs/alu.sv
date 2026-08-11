module alu(input clk, input [2:0] op, input [31:0] a, b,
           output reg [31:0] result, output reg zero);
  always @(posedge clk) begin
    case (op)
      3'b000: result <= a + b;
      3'b001: result <= a - b;
      3'b010: result <= a & b;
      3'b011: result <= a | b;
      3'b100: result <= a ^ b;
      3'b101: result <= a << b[4:0];
      3'b110: result <= a >> b[4:0];
      3'b111: result <= (a < b) ? 32'd1 : 32'd0;
    endcase
    zero <= (result == 32'd0) ? 1'b1 : 1'b0;
  end
endmodule
