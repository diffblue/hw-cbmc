module top(in,out);

`include "function.v"
`include "constant.v"
input [3:0] in;
output [3:0] out;

reg [3:0] result;
always @* begin
  result = VAL;
end

endmodule 


