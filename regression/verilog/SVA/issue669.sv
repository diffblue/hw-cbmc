module top(input x, input y, input clk);

  logic a, b;
  always_ff @(posedge clk) begin
    a <= x;
    b <= y;
  end

  // Not s_eventually 0 should always be true
  assert property (not s_eventually 0);

  // Using until_with
  assert property (a until_with b |-> not ((not b) s_until (not a)));
  assert property (not ((not b) s_until (not a)) |-> a until_with b);

  // Until_with equivalence with until
  assert property ((a until_with b) |-> (a until (a and b)));
  assert property ((a until (a and b)) |-> (a until_with b));

  // Property implies itself should always be true
  assert property ((b or (always b)) |-> (b or (always b)));
  assert property ((b or (always b)) implies (b or (always b)));

  // Definitions of strong eventually
  assert property ((s_eventually a) |-> (1 s_until a));
  assert property ((1 s_until a) |-> (s_eventually a));

  // Definitions of strong until
  assert property ((a s_until b) |-> ((s_eventually b) and (a until b)));
  assert property ((a s_until b) implies ((s_eventually b) and (a until b)));
  assert property (((s_eventually b) and (a until b)) |-> (a s_until b));
  assert property (((s_eventually b) and (a until b)) implies (a s_until b));

endmodule
