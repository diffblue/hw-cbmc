module main;

  reg [7:0] x;

  task set(output [7:0] out, input [7:0] value);
    out = value;
  endtask

  // no default for 'value'
  initial set(.out(x));

endmodule
