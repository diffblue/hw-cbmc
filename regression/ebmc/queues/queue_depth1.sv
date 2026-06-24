module queue(
  input in_data, in_valid,
  output out_data, out_valid,
  input clk);

  reg data;
  reg valid;

  initial valid = 0;

  always_ff @(posedge clk)
    {data, valid} <= {in_data, in_valid};

  assign out_data = data;
  assign out_valid = valid;

  assert property (@(posedge clk) in_valid implies s_eventually out_valid);

endmodule
