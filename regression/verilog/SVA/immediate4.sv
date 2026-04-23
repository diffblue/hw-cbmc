module main(input clk);

  reg [31:0] x, y;

  initial x=0;

  always @(posedge clk) begin : blk

    // It is unclear whether this should parse
    // as an if-then-else or as an if followed
    // by an assertion with an action block.
    if(x != 11)
      P: assert(x & 1); // fails
    else
      Q: assert(x & 1); // holds

    x<=x+1;
  end

endmodule
