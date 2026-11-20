module top(output wire [7:0] y);

  function automatic [7:0] increment(input [7:0] x = 8'd3);
    increment = x + 8'd1;
  endfunction

  assign y = increment();

  p0: assert final (y == 4);

endmodule
