module main(out, enable ,clk, reset);
output [7:0] out;
input enable, clk, reset;
reg [7:0] out;
initial begin
 out = 8'b0;
end
always @(posedge clk) begin
if (reset) begin
  out = 8'b0;
end else if (enable) begin
  out = out + 1;
end
  assert property1: !reset || (out == 0);
  assert property2: !enable || (out != 0 || out == 0);
end
endmodule 
