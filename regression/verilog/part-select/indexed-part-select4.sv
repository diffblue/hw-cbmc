module main(input my_input);

  bit [7:0] some_wire;

  always @my_input begin
    integer i;
    for(i=0; i<4; i++)
      // part select with index known at synthesis time
      some_wire[i * 2 +: 2] = 'b01;
  end

  p0: assert final (some_wire == 'b01_01_01_01);

endmodule
