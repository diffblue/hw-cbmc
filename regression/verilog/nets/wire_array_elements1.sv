// Unpacked arrays of nets and variables whose elements are defined in
// terms of other elements of the same array.
module main(input clk);
  wire [1:0] arr [0:3];
  assign arr[0] = 2'd1;
  assign arr[1] = arr[0] + 2'd1;
  assign arr[2] = arr[1] + 2'd1;
  assign arr[3] = arr[2] ^ arr[0];

  logic [1:0] l [0:2];
  assign l[0] = 2'd1;
  assign l[1] = l[0] + 2'd1;
  assign l[2] = l[1] + 2'd1;

  p0: assert property (@(posedge clk) arr[1] == 2'd2);
  p1: assert property (@(posedge clk) arr[2] == 2'd3);
  p2: assert property (@(posedge clk) arr[3] == 2'd2);
  p3: assert property (@(posedge clk) arr[3] == 2'd0); // fails
  p4: assert property (@(posedge clk) l[2] == 2'd3);
  p5: assert property (@(posedge clk) l[2] == 2'd0);   // fails
endmodule
