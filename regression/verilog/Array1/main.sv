module top (input clk, input reset);

   wire [3:0] x[4:0][5:0];

   assign x[4][5][3] = 1;
   
   p1: assert final (x[4][5][3] == 1);

endmodule
   
