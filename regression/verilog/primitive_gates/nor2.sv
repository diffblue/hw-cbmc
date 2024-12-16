module main(output nor_out, input nor_in1);

  // An 'nor' with just one input.  These negate.
  nor n1(nor_out, nor_in1);

  // should pass
  `ifndef __ICARUS__
  nor_ok: assert final (!nor_in1==nor_out);
  `endif

  // should pass -- nor is the same as reduction nor
  `ifndef __ICARUS__
  nor_is_reduction_nor: assert final (~|{nor_in1}==nor_out);
  `endif

endmodule

// To check simulator behavior
module nor_tb;

  wire nor_out;
  reg nor_in1;

  main m(nor_out, nor_in1);

  task print;
    begin
      $display("input: ", nor_in1);
      $display("  nor gate:      ", nor_out);
      $display("  reduction-nor: ", ~|{nor_in1});
      $display("  !reduction-or: ", !(|{nor_in1}));
      $display("  !:             ", !nor_in1);
    end
  endtask

  initial begin
    {nor_in1} = 'b0;
    #1;
    print();
    {nor_in1} = 'b1;
    #1;
    print();
  end

endmodule
