module main(input my_input);

  reg [7:0] some_wire;

  always @my_input begin
    some_wire[0 +: 2] = 'b01;
    some_wire[2 +: 2] = 'b01;
    some_wire[4 +: 2] = 'b01;
    some_wire[6 +: 2] = 'b01;
  end

  p0: assert final (some_wire == 'b01_01_01_01);

endmodule
