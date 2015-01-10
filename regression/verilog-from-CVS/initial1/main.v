module main(input clk);

 reg [7:0] t;

 initial t=20;

 always @(posedge clk) begin
   t=5;
 end
 
 always assert p1: t==20 || t==5;

endmodule 
