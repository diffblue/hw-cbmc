module time_literals;

realtime t;

initial begin
  t = 1fs;
  t = 0.1ps;
  t = 0.01ns;
  t = 0.001us;
  t = 0.0001ms;
  t = 0.00001s;
end

endmodule
