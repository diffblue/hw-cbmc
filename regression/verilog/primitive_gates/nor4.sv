module main(output [31:0] nor_out, input [31:0] nor_in1, nor_in2, nor_in3);

  // An 'nor' with three inputs over 32 bits.
  nor x1[31:0] (nor_out, nor_in1, nor_in2, nor_in3);

  // should pass
  nor_x1_ok: assert final (~(nor_in1 | nor_in2 | nor_in3)==nor_out);

  // An 'nor' with one input over 32 bits.
  nor x2[31:0] (nor_out, nor_in1);

  // should pass
  nor_x2_ok: assert final (~nor_in1==nor_out);

endmodule
