module submodule(input sub_input);

  wire some_wire = sub_input;

endmodule

module main(input input1);

  wire some_wire = input1;

  submodule my_instance(some_wire);

endmodule
