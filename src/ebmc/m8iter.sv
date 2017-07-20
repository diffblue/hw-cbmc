module main(out1, out2, enable ,clk, reset);
output [7:0] out1;
output [7:0] out2;
input enable, clk, reset;
reg [7:0] out1;
reg [7:0] out2;
initial begin
 out1 = 8'b0;
 out2 = 8'b0;
end
always @(posedge clk) begin
if (reset) begin
  out1 = 8'b0;
  out2 = 8'b0;
end else if (enable) begin
  out1 = out1 + 1;
  out2 = out2 + 1;
end
end
   assert property (out1 == out2);
   assert property (out1[0] == out2[0]);
   assert property (out1[1] == out2[1]);
   assert property (out1[2] == out2[2]);
   assert property (out1[3] == out2[3]);
   assert property (out1[4] == out2[4]);
   assert property (out1[5] == out2[5]);
   assert property (out1[6] == out2[6]);
   assert property (out1[7] == out2[7]);
endmodule 
