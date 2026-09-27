module drv_a(input logic a, output logic y);
  assign y = a;
endmodule

module drv_b(input logic a, output logic y);
  assign y = ~a;
endmodule

module main(input logic a);
  logic x;

  drv_a i_a(.a(a), .y(x));
  drv_b i_b(.a(a), .y(x));

  // x is simultaneously constrained to a and to ~a by the two
  // port-connected drivers, which makes the whole model UNSAT.
  // This property is trivially false but should be REFUTED, not PROVED.
  p0: assert final (a == !a);
endmodule
