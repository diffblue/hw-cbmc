module main(input clk, input data);

  reg data_old = 0;
  reg [2:0] counter = 0;

  always_ff @(posedge clk)
    if(data != data_old)
      counter = 0;
    else if(counter < 3)
      counter++;

  always_ff @(posedge clk)
    data_old = data;

  p0: assert property ($stable(data) |=> counter >= 1);

endmodule
