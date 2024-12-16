module main(output [31:0] xnor_out, input [31:0] xnor_in1, xnor_in2);

  // An 'xnor' with two inputs, 32 bits each.
  xnor x1[31:0](xnor_out, xnor_in1, xnor_in2);

  // should pass
  `ifndef __ICARUS__
  xnor_ok: assert final (xnor_in1 ~^ xnor_in2==xnor_out);
  `endif

endmodule
