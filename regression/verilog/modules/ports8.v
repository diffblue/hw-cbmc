// Ports can be arrays.
module sub(output reg [31:0] array [9:0]);

  wire some_floating_wire;

  always @some_floating_wire begin
    integer i;
    for(i=0; i<10; i=i+1)
      array[i] = i;
  end

endmodule

module main;
  wire [31:0] array [9:0];

  sub s(array);

  always assert p0: array[0] == 0;
  always assert p9: array[9] == 9;

endmodule
