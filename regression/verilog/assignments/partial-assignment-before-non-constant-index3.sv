module main(input clk, input [0:0] i);

  typedef struct packed {
    logic [3:0] hi;
    logic [1:0][1:0] arr;
  } s_t;

  s_t s;

  initial s = 0;

  always @(posedge clk) begin
    // a blocking assignment to a member
    s.hi = 4'hF;
    // followed by a blocking assignment with a non-constant index
    s.arr[i] = 2'b11;
  end

  p0: assert property (@(posedge clk) ##1 s.hi == 4'hF);

endmodule
