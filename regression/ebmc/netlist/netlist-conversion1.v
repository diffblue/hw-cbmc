module main(input clk);

  reg [0:0] q;

  always @(posedge clk)
    q[0] <= q[0];

  always assert p1: q[0];

endmodule
