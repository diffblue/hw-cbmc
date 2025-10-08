module submoduleA(input [2:0] some_input);
endmodule

module submoduleB(output [2:0] some_output);
  assign some_output = 1'd1+1'd1;
endmodule

module main;

  // 1800-2017 10.8 Assignment-like contexts

  // continuous assignment
  wire [1:0] v1;
  assign v1 = 1'd1+1'd1;
  assert final (v1 == 2'd2);

  // procedural assignment
  reg [1:0] v2;
  initial v2 = 1'd1+1'd1;
  assert final (v2 == 2'd2);

  // parameter with explicit type declaration
  parameter [1:0] v3 = 1'd1+1'd1;
  assert final (v3 == 2'd2);

  // A port connection to an input port of a module
  submoduleA subA(1'd1+1'd1);
  assert final (subA.some_input == 2'd2);

  // A port connection to an output port of a module
  submoduleB subB();
  assert final (subB.some_output == 2'd2);

  // The passing of a value to a subroutine input port
  task my_task(input [1:0] some_input);
    assert final (some_input == 2'd2);
  endtask

  initial my_task(1'd1+1'd1);

  // A return statement in a function
  function [1:0] my_fun;
    return 1'd1+1'd1;
  endfunction

  assert final (my_fun() == 2'd2);

  // A tagged union expression
  union tagged {
    bit [1:0] my_tag;
  } some_union = tagged my_tag(1'd1+1'd1);
  assert final (some_union.my_tag == 2'd2);

  // recursively, an expression within parentheses
  wire [1:0] v4;
  assign v4 = (1'd1+1'd1);
  assert final (v4 == 2'd2);

  // recursively, the second and third operand of ?:
  wire [1:0] v5;
  assign v5 = 0 ? 1'b0 : 1'd1+1'd1;
  assert final (v4 == 2'd2);

  // nondefault value in assignment pattern
  struct { bit [1:0] field; } s = '{ field: 1'd1+1'd1 };
  assert final (s.field == 2'd2);

endmodule
