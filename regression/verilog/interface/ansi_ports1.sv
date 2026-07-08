// Interface with ANSI port list (IEEE 1800-2017 25.3)
interface bus_if(
  input wire clk,
  input wire rst
);
  logic [7:0] data;

  always @(posedge clk)
    if (rst) data <= 0;
endinterface

module main(input clk, input rst);
  bus_if bif(clk, rst);
  initial bif.data = 8'hAB;
endmodule
