// An unpacked array is copied as a whole in an always_comb, and an
// element of the copy is read in the same block. The read must see the
// copied value, for one- and two-dimensional arrays, and with constant
// and non-constant indices.
module main(input clk, input [1:0] rp);
  logic [3:0] pend [0:3];
  logic [3:0] pend_next [0:3];
  logic [3:0] o;

  assign pend[0] = 4'h1;
  assign pend[1] = 4'h2;
  assign pend[2] = 4'h4;
  assign pend[3] = 4'h8;

  always_comb begin
    pend_next = pend;
    o = pend_next[rp];
  end

  p0: assert property (@(posedge clk) o == (4'h1 << rp));
  p1: assert property (@(posedge clk) pend_next[2] == 4'h4);

  logic [3:0] m [0:1][0:3];
  logic [3:0] m_next [0:1][0:3];
  logic [3:0] o2;
  logic [1:0] pop;

  assign m[0][0] = 4'h1; assign m[0][1] = 4'h2;
  assign m[0][2] = 4'h4; assign m[0][3] = 4'h8;
  assign m[1][0] = 4'h9; assign m[1][1] = 4'hA;
  assign m[1][2] = 4'hB; assign m[1][3] = 4'h0;

  always_comb begin
    integer i;
    m_next = m;
    o2 = m_next[1][rp];
    for(i = 0; i < 2; i = i + 1)
      pop[i] = ~(|m_next[i][rp]);
  end

  p2: assert property (@(posedge clk) rp != 2'd3 |-> o2 == 4'h9 + rp);
  p3: assert property (@(posedge clk) pop[0] == 1'b0);
  p4: assert property (@(posedge clk) pop[1] == (rp == 2'd3));
endmodule
