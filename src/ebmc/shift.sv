module main(out1, out2, enable ,clk, reset);
   output [7:0] out1;
   output [7:0] out2;
   input        enable, clk, reset;
   reg [7:0]    out1;
   reg [7:0]    out2;
   parameter shift = 8'b1111;
   
   initial begin
      out1 = 8'b0;
      out2 = shift;
   end
   always @(posedge clk) begin
      if (out1 == 100) begin
         out1 = 8'b0;
      end else if (enable) begin
         out1 = out1 + 1;
      end
   end
   always @(posedge clk) begin
      if (out2 == (100 + shift)) begin
         out2 = shift;
      end else if (enable) begin
         out2 = out2 + 1;
      end
   end
   assert property (out1 == (out2 - shift));
endmodule 
