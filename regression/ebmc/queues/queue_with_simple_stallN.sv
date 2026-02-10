module queue
  #(parameter N = 10)
  (input in_data, in_valid, in_stall,
  output out_data, out_valid, out_stall,
  input clk);

  reg [N-1:0] data;
  reg [N-1:0] valid;

  initial valid = {N{1'b0}};

  always_ff @(posedge clk)
    if(!out_stall)
      {data[0], valid[0]} <= {in_data, in_valid};

  always_ff @(posedge clk)
    for(integer i=1; i<N; i++)
      if(!out_stall)
        {data[i], valid[i]} <= {data[i-1], valid[i-1]};

  assign out_data = data[N-1];
  assign out_valid = valid[N-1];
  assign out_stall = in_stall;

  // we need to assume we are not stalled indefinitively
  assume property (@(posedge clk) s_eventually !in_stall);

  assert property (@(posedge clk) (in_valid && !out_stall) implies s_eventually out_valid);

endmodule
