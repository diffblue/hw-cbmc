module comb_mux(input [1:0] sel, input [7:0] a, b, c, d, output [7:0] y);
  assign y = sel[1] ? (sel[0] ? d : c) : (sel[0] ? b : a);
endmodule
