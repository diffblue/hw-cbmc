module top(input clk, in);

  reg [31:0] variable;

  initial variable=0;

  always @(posedge clk) begin
    if(in)
      variable=variable+1;
  end

endmodule
