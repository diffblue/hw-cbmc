module top(input x, input y, input clk);

  logic a, b;
  always_ff @(posedge clk) begin
    a <= x;
    b <= y;
  end

  // Not s_eventually 0 should always be true
  assert property (not s_eventually 0);

  // Using until_with
  assert property ((a until_with b) implies not ((not b) s_until (not a)));
  assert property (not ((not b) s_until (not a)) implies (a until_with b));

  // Until_with equivalence with until
  assert property ((a until_with b) implies (a until (a and b)));
  assert property ((a until (a and b)) implies (a until_with b));

  // Definitions of strong eventually
  assert property ((s_eventually a) implies (1 s_until a));
  assert property ((1 s_until a) implies (s_eventually a));

  // Definitions of strong until
  assert property ((a s_until b) implies ((s_eventually b) and (a until b)));
  assert property (((s_eventually b) and (a until b)) implies (a s_until b));

endmodule
