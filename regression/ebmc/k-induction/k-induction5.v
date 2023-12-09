module main();

  reg [31:0] x, y;
  wire clk;

  initial x=1;
  initial y=1;

  always @(posedge clk)
    if(x<1000) begin
      x<=x+1;
      y<=y+1;
    end

  // true, and 1-inductive
  always assert property1: x<=1000;

  // false, bound 1 suffices
  always assert property2: x!=2;

endmodule
