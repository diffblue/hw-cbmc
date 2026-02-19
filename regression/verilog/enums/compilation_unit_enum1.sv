typedef enum { RED, YELLOW1, GREEN, YELLOW2 } traffic_light_type;

module main(input clk);

  traffic_light_type my_light = RED;

  always_ff @(posedge clk)
    case(my_light)
      RED:     my_light <= YELLOW1;
      YELLOW1: my_light <= GREEN;
      GREEN:   my_light <= YELLOW2;
      YELLOW2: my_light <= RED;
    endcase

  // expected to fail
  p1: assert property (my_light != YELLOW2);

endmodule
