module main;

  reg [7:0] x;

  // defaults are only supported for inputs
  task set(output [7:0] out = x);
    out = 1;
  endtask

endmodule
