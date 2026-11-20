module main;

  reg [7:0] x;

  task set(output [7:0] out, input [7:0] value);
    out = value;
  endtask

  // ordered arguments must precede named arguments
  initial set(.out(x), 1);

endmodule
