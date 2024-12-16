module main(input or_in1, or_in2, or_in3);

  wire  or_out;

  or o1(or_out, or_in1, or_in2, or_in3);

  // should pass
  or_ok: assert final ((or_in1 || or_in2 || or_in3)==or_out);

  // should fail
  or_not_ok1: assert final (or_out == (or_in1 || or_in2));

  // should fail
  or_not_ok2: assert final (or_in1 || or_in2 || !or_in3);

endmodule
