module top(input reset_n, clk);

  reg [7:0] data;

  always @(posedge clk) begin
    if(!reset_n)
      data = 0;
    else if(data != 10)
      data++;
  end

  // the below holds if the design is reset properly
  p1: assert property (disable iff (!reset_n) data >=0 && data <= 10);

endmodule
