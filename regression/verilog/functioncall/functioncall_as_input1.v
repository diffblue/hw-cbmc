module submodule(input [31:0] in);
  wire [31:0] my_wire = in;
endmodule

module main;

  function [31:0] sum;
    input [31:0] a, b;
    sum = a + b;
  endfunction

  submodule my_instance(sum(1, 2));

  always assert p1: (my_instance.my_wire == 3);

endmodule
