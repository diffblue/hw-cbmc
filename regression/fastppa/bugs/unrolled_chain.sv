module main(input [31:0] a, output [7:0] y);
  wire [7:0] acc [0:3];
  assign acc[0] = a[7:0];
  genvar i;
  for(i = 1; i < 4; i = i + 1) begin : g
    assign acc[i] = (i >= 1 ? acc[i - 1] : 8'd0) + a[i*8 +: 8];
  end
  assign y = acc[3];
endmodule
