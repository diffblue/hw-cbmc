// An initial block assigns single elements of a large two-dimensional
// unpacked array (the shape of sv-tests 11.5.2--multi_dim_array_addressing).
// Only the assigned elements are constrained; the size of the initial-state
// constraint must not grow with the size of the array.
module main(input clk);
  logic [7:0] mem [0:1023][0:3];
  logic [7:0] a;
  logic [3:0] v;

  initial begin
    mem[123][2] = 125;
    mem[5][0] = 8'h11;
    a = mem[123][2];
    v[1:0] = 2'b01;
  end

  always @(posedge clk) begin
    mem <= mem;
    a <= a;
    v <= v;
  end

  p0: assert property (@(posedge clk) mem[123][2] == 125);
  p1: assert property (@(posedge clk) mem[5][0] == 8'h11);
  p2: assert property (@(posedge clk) a == 125);
  p3: assert property (@(posedge clk) v[1:0] == 2'b01);
  // elements that are not assigned are unconstrained
  p4: assert property (@(posedge clk) mem[123][1] == 0);
  p5: assert property (@(posedge clk) v[3:2] == 0);
endmodule
