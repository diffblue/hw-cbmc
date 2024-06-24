module main(input clk);

  reg [31:0] x;

  initial x=0;

  always @(posedge clk) begin
    if(x == 11)
      assert(x & 1); // holds

    x<=x+1;
  end

endmodule
