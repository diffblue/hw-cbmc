module main(output xnor_out, input xnor_in1, xnor_in2, xnor_in3);

  // An 'xnor' with three inputs.
  // 1800-2017 28.4 says that these "shall have a natural extension".
  xnor x1(xnor_out, xnor_in1, xnor_in2, xnor_in3);

  // should pass
  `ifndef __ICARUS__
  xnor_ok: assert final (!(xnor_in1 ^ xnor_in2 ^ xnor_in3)==xnor_out);
  `endif

  // should fail -- not the same as using a chain of binary xnors
  `ifndef __ICARUS__
  xnor_fail: assert final ((xnor_in1 ~^ xnor_in2 ~^ xnor_in3)==xnor_out);
  `endif

  // should pass -- xnor is the same as reduction xnor
  `ifndef __ICARUS__
  xnor_is_reduction_xnor: assert final (~^{xnor_in1, xnor_in2, xnor_in3}==xnor_out);
  `endif

endmodule

// To check simulator behavior
module xnor_tb;

  wire xnor_out;
  reg xnor_in1, xnor_in2, xnor_in3;

  main m(xnor_out, xnor_in1, xnor_in2, xnor_in3);

  task print;
    begin
      $display("input: ", xnor_in1, xnor_in2, xnor_in3);
      $display("  xnor gate:      ", xnor_out);
      $display("  reduction-xnor: ", ~^{xnor_in1, xnor_in2, xnor_in3});
      $display("  !reduction-xor: ", !(^{xnor_in1, xnor_in2, xnor_in3}));
      $display("  !xor:           ", !(xnor_in1 ^ xnor_in2 ^ xnor_in3));
      $display("  binary xnors:   ", xnor_in1 ~^ xnor_in2 ~^ xnor_in3);
    end
  endtask

  initial begin
    {xnor_in1, xnor_in2, xnor_in3} = 'b000;
    #1;
    print();
    {xnor_in1, xnor_in2, xnor_in3} = 'b100;
    #1;
    print();
    {xnor_in1, xnor_in2, xnor_in3} = 'b110;
    #1;
    print();
    {xnor_in1, xnor_in2, xnor_in3} = 'b111;
    #1;
    print();
    {xnor_in1, xnor_in2, xnor_in3} = 'b101;
    #1;
    print();
  end

endmodule
