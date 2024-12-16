module main(input nor_in1, nor_in2, nor_in3);

  wire nor_out;

  // a 'nor' with three inputs
  nor n1(nor_out, nor_in1, nor_in2, nor_in3);

  // should pass
  nor_ok: assert final (!(nor_in1 || nor_in2 || nor_in3)==nor_out);

endmodule
