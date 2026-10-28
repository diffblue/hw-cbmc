// An unpacked array of packed structs, assigned element-wise in terms of
// other elements.
module main(input clk);
  typedef struct packed { logic [1:0] a; logic b; } s_t;
  s_t arr [0:1];
  assign arr[0] = '{a: 2'd1, b: 1'b1};
  assign arr[1] = '{a: arr[0].a + 2'd1, b: ~arr[0].b};
  p0: assert property (@(posedge clk) arr[1].a == 2'd2 && arr[1].b == 0);
  p1: assert property (@(posedge clk) arr[1].a == 2'd0); // fails
endmodule
