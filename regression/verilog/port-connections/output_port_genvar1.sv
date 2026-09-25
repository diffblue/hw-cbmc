module child(output reg o);
endmodule

module main;
  wire [3:0] locked;
  genvar g;

  generate
    for(g = 0; g < 4; g = g + 1)
    begin : genblk
      child c(.o(locked[g]));
    end
  endgenerate
endmodule
