module top;
  integer i;
  initial begin
    for(i = 0; i < 3; i = i + 1)
      $display("i = %d", i);
  end
endmodule
