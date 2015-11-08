module vmain(in,out);

`include "function.v"
`include "constant.v"

localparam LINK_OFFSET_ZERO = {COUNT{1'b0}};

input [3:0] in;
output [3:0] out;

reg [3:0] result;
always @* begin
  result = VAL;
end
endmodule 


