module main(input not_in);

  wire not_out1, not_out2;

  not not_gate(not_out1, not_out2, not_in);

  // should pass
  not_out1_ok: assert final (not_out1 == !not_in);
  not_out2_ok: assert final (not_out2 == !not_in);

endmodule
