module queue(
  input in_data, in_valid,
  output out_data, out_valid,
  input clk);

  reg data0, data1;
  reg valid0, valid1;

  initial {valid0, valid1} = 2'b00;

  always_ff @(posedge clk) begin
    {data0, valid0} <= {in_data, in_valid};
    {data1, valid1} <= {data0, valid0};
  end

  assign out_data = data1;
  assign out_valid = valid1;

  assert property (@(posedge clk) in_valid implies s_eventually out_valid);

endmodule
