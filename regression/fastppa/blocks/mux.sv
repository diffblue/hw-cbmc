module mux_tree(input clk, input [1:0] sel, input [7:0] a, b, c, d,
               output reg [7:0] y);
  always @(posedge clk)
    case (sel)
      2'b00: y <= a;
      2'b01: y <= b;
      2'b10: y <= c;
      2'b11: y <= d;
    endcase
endmodule
