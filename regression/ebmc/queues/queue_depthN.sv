module queue
  #(parameter N = 10)
  (input in_data, in_valid,
  output out_data, out_valid,
  input clk);

  reg [N-1:0] data;
  reg [N-1:0] valid;

  initial valid = {N{1'b0}};

  always_ff @(posedge clk)
    {data[0], valid[0]} <= {in_data, in_valid};

  always_ff @(posedge clk)
    for(integer i=1; i<N; i++)
      {data[i], valid[i]} <= {data[i-1], valid[i-1]};

  assign out_data = data[N-1];
  assign out_valid = valid[N-1];

  assert property (@(posedge clk) in_valid implies s_eventually out_valid);

endmodule
