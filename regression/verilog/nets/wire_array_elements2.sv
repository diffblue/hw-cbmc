// As wire_array_elements1, with descending and offset ranges, and a read
// with a variable index.
module main(input clk, input [1:0] i);
  wire [1:0] d [3:0];
  assign d[3] = 2'd1;
  assign d[2] = d[3] + 2'd1;
  assign d[1] = d[2] + 2'd1;
  assign d[0] = d[1] ^ d[3];

  wire [1:0] o [1:4];
  assign o[1] = 2'd1;
  assign o[2] = o[1] + 2'd1;
  assign o[3] = o[2] + 2'd1;
  assign o[4] = o[3] ^ o[1];

  wire [1:0] v [0:3];
  assign v[0] = 2'd0;
  assign v[1] = v[0] + 2'd1;
  assign v[2] = v[1] + 2'd1;
  assign v[3] = v[2] + 2'd1;

  p0: assert property (@(posedge clk) d[2] == 2'd2 && d[0] == 2'd2);
  p1: assert property (@(posedge clk) d[0] == 2'd0);   // fails
  p2: assert property (@(posedge clk) o[3] == 2'd3 && o[4] == 2'd2);
  p3: assert property (@(posedge clk) o[4] == 2'd0);   // fails
  p4: assert property (@(posedge clk) v[i] == i);
  p5: assert property (@(posedge clk) v[i] == 2'd0);   // fails
endmodule
