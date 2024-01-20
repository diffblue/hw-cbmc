module main;

  parameter MAX = 'd1;
  parameter something = 1;

  wire [MAX-1:0] my_wire;

  generate
    if(something) begin
      genvar i;
      for (i = 0; i < MAX; i = i + 1)
        assign my_wire[i] = 1;
    end
  endgenerate

  always assert p1: my_wire == 1;

endmodule
