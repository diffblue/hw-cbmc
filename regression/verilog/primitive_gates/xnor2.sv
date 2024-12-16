module main(output xnor_out, input xnor_in1);

  // An 'xnor' with just one input.  These negate.
  xnor x1(xnor_out, xnor_in1);

  // should pass
  `ifndef __ICARUS__
  xnor_ok: assert final (!xnor_in1==xnor_out);
  `endif

  // should pass -- xnor is the same as reduction xnor
  `ifndef __ICARUS__
  xnor_is_reduction_xnor: assert final (~^{xnor_in1}==xnor_out);
  `endif

endmodule

// To check simulator behavior
module xnor_tb;

  wire xnor_out;
  reg xnor_in1;

  main m(xnor_out, xnor_in1);

  task print;
    begin
      $display("input: ", xnor_in1);
      $display("  xnor gate:      ", xnor_out);
      $display("  reduction-xnor: ", ~^{xnor_in1});
      $display("  !reduction-xor: ", !(^{xnor_in1}));
      $display("  !:              ", !xnor_in1);
    end
  endtask

  initial begin
    {xnor_in1} = 'b0;
    #1;
    print();
    {xnor_in1} = 'b1;
    #1;
    print();
  end

endmodule
