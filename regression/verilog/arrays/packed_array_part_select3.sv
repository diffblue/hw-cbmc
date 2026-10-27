// A non-indexed part-select on a packed array selects elements
// (1800-2017 7.4.6). The selected range may extend beyond the declared
// range of the array; the elements outside the array read as zero, as
// bits outside a vector do, both for a packed array of vectors and for a
// packed array of packed structs.
module main(input clk);
  typedef struct packed { logic v; logic [2:0] d; } s_t;

  logic [1:0][3:0] la;
  s_t [1:0] sa;
  initial begin la = 8'hA5; sa = 8'hA5; end
  always @(posedge clk) begin la <= la; sa <= sa; end

  // within range
  p0: assert property (@(posedge clk) la[1:0] == 8'hA5);
  p1: assert property (@(posedge clk) sa[1:0] == 8'hA5);
  p2: assert property (@(posedge clk) sa[1].d == 3'b010);

  // entirely above the range
  p3: assert property (@(posedge clk) la[7:4] == 16'd0);
  p4: assert property (@(posedge clk) sa[7:4] == 16'd0);

  // partially below the range: {la[0], la[-1]}
  p5: assert property (@(posedge clk) la[0:-1] == 8'h50);
  p6: assert property (@(posedge clk) sa[0:-1] == 8'h50);

  // partially above the range: {la[3], la[2], la[1], la[0]}
  p7: assert property (@(posedge clk) la[3:0] == 16'h00A5);
  p8: assert property (@(posedge clk) sa[3:0] == 16'h00A5);
endmodule
