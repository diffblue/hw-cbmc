// Continuous assignments to slices of a vector that read other slices of
// the same vector. These are not combinational loops, and the reads must
// yield the values of those slices.
module main(input clk, input x, input [1:0] a);

  // a chain of slices, in increasing order
  wire [7:0] v;
  assign v[1:0] = 2'd0;
  assign v[3:2] = v[1:0] + 2'd1;
  assign v[5:4] = v[3:2] + 2'd1;
  assign v[7:6] = v[5:4] + 2'd1;
  p0: assert property (@(posedge clk) v == 8'b11_10_01_00);

  // a chain of bits
  wire [3:0] w;
  assign w[0] = x;
  assign w[1] = w[0];
  assign w[2] = w[1];
  assign w[3] = w[2];
  p1: assert property (@(posedge clk) w == {4{x}});

  // the higher slice feeds the lower one
  wire [3:0] y;
  assign y[3:2] = a;
  assign y[1:0] = y[3:2];
  p2: assert property (@(posedge clk) y == {a, a});

  // indexed part selects, in a generate loop
  wire [7:0] z;
  genvar i;
  for(i = 0; i < 4; i++) begin : g
    if(i == 0) begin : b0
      assign z[i*2 +: 2] = 2'd0;
    end
    else begin : bn
      assign z[i*2 +: 2] = z[(i-1)*2 +: 2] + 2'd1;
    end
  end
  p3: assert property (@(posedge clk) z == 8'b11_10_01_00);

  // A genuine combinational loop within one slice: the value of that
  // slice is unconstrained, but the other slice is not affected.
  wire [3:0] u;
  assign u[1:0] = 2'd1;
  assign u[3:2] = ~u[3:2];
  p4: assert property (@(posedge clk) u[1:0] == 2'd1);
  p5: assert property (@(posedge clk) u[3:2] == 2'd0);

  // A combinational loop through two slices: both are unconstrained.
  wire [1:0] t;
  assign t[0] = ~t[1];
  assign t[1] = t[0];
  p6: assert property (@(posedge clk) t == 2'd0);

  // A slice that depends on itself and also reads a separately defined
  // slice: only the self-read is unconstrained, the other read keeps
  // its value.
  wire [3:0] r;
  assign r[1:0] = 2'd0;
  assign r[3:2] = r[3:2] & r[1:0];
  p7: assert property (@(posedge clk) r[3:2] == 2'd0);

  // An out-of-range read of an array in a wire definition yields 'x',
  // and must not be rejected.
  wire [1:0] arr [0:1];
  wire [1:0] oor;
  assign arr[0] = 2'd1;
  assign arr[1] = 2'd2;
  assign oor = arr[2];
  p8: assert property (@(posedge clk) arr[0] == 2'd1);

endmodule
