module main(output [31:0] xnor_out, input [31:0] xnor_in1, xnor_in2, xnor_in3);

  // An 'xnor' with three inputs over 32 bits.
  xnor x1[31:0] (xnor_out, xnor_in1, xnor_in2, xnor_in3);

  // should pass
  xnor_x1_ok: assert final (~(xnor_in1 ^ xnor_in2 ^ xnor_in3)==xnor_out);

  // An 'xnor' with one input over 32 bits.
  xnor x2[31:0] (xnor_out, xnor_in1);

  // should pass
  xnor_x2_ok: assert final (~xnor_in1==xnor_out);

endmodule
