module main(input clk);

  reg [31:0] x, y;

  initial x=0;

  always @(posedge clk) begin : blk

    // This is an assertion in an action block of
    // an assertion.
    if(x != 11)
      P: assert(x & 1); // fails
         else Q: assert(x & 1); // holds

    x<=x+1;
  end

endmodule
