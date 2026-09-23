module main(input clk, input [0:0] i);

  reg [7:0] a [0:1];

  initial begin
    a[0] = 0;
    a[1] = 0;
  end

  always @(posedge clk) begin
    // a blocking assignment to an element with a constant index
    a[1] = 7;
    // followed by a blocking assignment with a non-constant index
    a[i] = 3;
  end

  p0: assert property (@(posedge clk) ##1 ($past(i) == 0 -> a[1] == 7));

endmodule
