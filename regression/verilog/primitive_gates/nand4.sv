module main(output [31:0] nand_out, input [31:0] nand_in1, nand_in2, nand_in3);

  // An 'nand' with three inputs over 32 bits.
  nand x1[31:0] (nand_out, nand_in1, nand_in2, nand_in3);

  // should pass
  nand_x1_ok: assert final (~(nand_in1 & nand_in2 & nand_in3)==nand_out);

  // An 'nand' with one input over 32 bits.
  nand x2[31:0] (nand_out, nand_in1);

  // should pass
  nand_x2_ok: assert final (~nand_in1==nand_out);

endmodule
