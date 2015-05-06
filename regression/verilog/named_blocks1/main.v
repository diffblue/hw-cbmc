module m;

  wire [31:0] w;
  reg  [31:0] r, y;

  always @(w) begin : my_block
    reg [31:0] x;
    y=w;
  end
  
  always assert p1: y==w;

endmodule
