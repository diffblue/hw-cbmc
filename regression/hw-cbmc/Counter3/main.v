module top(input clk);

  reg [63:0] var1;
  reg [63:0] var2;

  initial var1=0;
  initial var2=0;

  always @(posedge clk) begin
    var2=var2+1;
    var1=var2;
  end

endmodule
