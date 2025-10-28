module sub(input in, output logic data);

  assign data = in;

endmodule

module main;
  logic subout;

  sub sub_inst(.data(subout));

  // The value of the output needs to be able to change
  cover property (##1 subout != $past(subout));

endmodule
