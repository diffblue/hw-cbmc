// Constant function whose body uses an if statement, evaluated by the
// Verilog constant-expression interpreter to compute a parameter.
// Minimal reproduction of large/axicrossbar (rtl/axi_crossbar_addr.v:140),
// where the interpreter did not know how to interpret an `if' statement.
module main;

  function [31:0] f(input [31:0] x);
    reg [31:0] r;
    begin
      r = 0;
      if(x > 10)
        r = x + 1; // taken for x==20
      else
        r = x - 1;
      // if without else
      if(r > 100)
        r = 0;
    end
    f = r;
  endfunction

  parameter P = f(20);

  always assert p1: P == 21;

endmodule
