module main(input clk);

  typedef struct packed {
    logic [3:0] hi;
    logic [3:0] lo;
  } s_t;

  s_t s;
  logic [7:0] r;

  initial begin
    s = 8'h05;
    r = 0;
  end

  always @(posedge clk) begin
    s.hi = 4'hA;
    // reads the struct after a blocking assignment to one member
    r = s;
  end

  p0: assert property (@(posedge clk) ##1 r == 8'hA5);

endmodule
