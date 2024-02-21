module main(input clk);

  enum { RED, YELLOW1, GREEN, YELLOW2 } my_light = RED;

  always @(posedge clk)
    case(my_light)
      RED:     my_light <= YELLOW1;
      YELLOW1: my_light <= GREEN;
      GREEN:   my_light <= YELLOW2;
      YELLOW2: my_light <= RED;
    endcase

  // expected to fail
  p1: assert property (my_light != YELLOW2);

endmodule
