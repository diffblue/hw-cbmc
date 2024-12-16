module main(input nand_in1, nand_in2, nand_in3);

  wire nand_out;

  // a 'nand' with three inputs
  nand n1(nand_out, nand_in1, nand_in2, nand_in3);

  // should pass
  nand_ok: assert final (!(nand_in1 && nand_in2 && nand_in3)==nand_out);

endmodule
