module main(output nand_out, input nand_in1);

  // An 'nand' with just one input.  These negate.
  nand n1(nand_out, nand_in1);

  // should pass
  `ifndef __ICARUS__
  nand_ok: assert final (!nand_in1==nand_out);
  `endif

  // should pass -- nand is the same as reduction nand
  `ifndef __ICARUS__
  nand_is_reduction_nand: assert final (~&{nand_in1}==nand_out);
  `endif

endmodule

// To check simulator behavior
module nand_tb;

  wire nand_out;
  reg nand_in1;

  main m(nand_out, nand_in1);

  task print;
    begin
      $display("input: ", nand_in1);
      $display("  nand gate:      ", nand_out);
      $display("  reduction-nand: ", ~&{nand_in1});
      $display("  !reduction-and: ", !(&{nand_in1}));
      $display("  !:              ", !nand_in1);
    end
  endtask

  initial begin
    {nand_in1} = 'b0;
    #1;
    print();
    {nand_in1} = 'b1;
    #1;
    print();
  end

endmodule
